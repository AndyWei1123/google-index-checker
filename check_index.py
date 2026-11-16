#!/usr/bin/env python3
"""
Google 收錄批次檢查工具（使用 ScrapingDog Google Search API）

三種模式：
  url     每個網址各查一次 site:網址（最準，最貴：每條 5 credits）
  domain  每個網域翻頁查 site:網域（便宜，但大站翻不完，只能當參考）
  hybrid  先用網域掃描撈一批，找不到的再逐條查（預設，通常最省）

執行前一定會先印出預估 credits，輸入 yes 才會真的打 API。
"""
import argparse
import csv
import gzip
import json
import math
import os
import re
import sys
import threading
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from urllib.parse import urlsplit, unquote
import xml.etree.ElementTree as ET

import requests

API_URL = "https://api.scrapingdog.com/google/"
CREDITS_PER_REQ = 5          # 一般查詢每次 5 credits（官方文件）
RESULTS_PER_PAGE = 10        # Google 現在每頁只回 10 筆
GOOGLE_DOMAIN = "google.com" # 一律用 google.com，只用地區代碼（--country）區分地區
HERE = os.path.dirname(os.path.abspath(__file__))
UA = "Mozilla/5.0 (compatible; index-checker/1.0)"

# 預設排除：不是 SEO 要看的頁面（以 WordPress 為主）
DEFAULT_EXCLUDES = [
    r"/tag/", r"/tags/", r"/category/", r"/categories/", r"/author/",
    r"/page/\d+", r"/feed/?$", r"/comments/", r"/attachment/", r"/trackback/?$",
    r"/embed/?$", r"/amp/?$", r"/wp-content/", r"/wp-json/", r"/wp-admin/",
    r"/wp-login", r"/search/", r"[?&](s|p|page_id|replytocom|amp)=",
    r"/cart/?$", r"/checkout/?$", r"/my-account/?$",
    r"\.(jpg|jpeg|png|gif|webp|svg|pdf|zip)$",
]


# ---------------------------------------------------------------- 小工具

def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def norm(url):
    """比對用的標準化：去掉協定、www、結尾斜線、#、?，解碼中文/日文網址，轉小寫。"""
    url = (url or "").strip()
    if not url:
        return ""
    if "://" not in url:
        url = "http://" + url
    p = urlsplit(url)
    host = (p.hostname or "").lower()
    if host.startswith("www."):
        host = host[4:]
    path = unquote(p.path or "/").rstrip("/")
    return (host + path).lower()


def host_of(url):
    if "://" not in url:
        url = "http://" + url
    h = (urlsplit(url).hostname or "").lower()
    return h[4:] if h.startswith("www.") else h


def single_query(u):
    return "site:" + re.sub(r"^https?://", "", u.strip()).rstrip("/")


def load_api_key():
    key = os.environ.get("SCRAPINGDOG_API_KEY", "").strip()
    if key:
        return key
    env_path = os.path.join(HERE, ".env")
    if os.path.exists(env_path):
        with open(env_path, encoding="utf-8-sig") as f:
            for line in f:
                line = line.strip()
                if line.startswith("SCRAPINGDOG_API_KEY="):
                    return line.split("=", 1)[1].strip().strip('"').strip("'")
    return ""


# ---------------------------------------------------------------- 讀網址清單（免費，不扣額度）

def fetch(url, timeout=30):
    r = requests.get(url, headers={"User-Agent": UA}, timeout=timeout)
    r.raise_for_status()
    data = r.content
    if data[:2] == b"\x1f\x8b":
        data = gzip.decompress(data)
    return data


def parse_sitemap_xml(data):
    """回傳 (子 sitemap 清單, 網址清單)"""
    root = ET.fromstring(data)
    tag = root.tag.split("}")[-1].lower()
    locs = [el.text.strip() for el in root.iter()
            if el.tag.split("}")[-1] == "loc" and el.text]
    if tag == "sitemapindex":
        return locs, []
    return [], locs


def read_sitemap(url, seen=None, depth=0):
    seen = seen if seen is not None else set()
    if url in seen or depth > 4:
        return []
    seen.add(url)
    try:
        children, urls = parse_sitemap_xml(fetch(url))
    except Exception as e:
        print(f"  ! 讀不到 sitemap {url}：{e}")
        return []
    for c in children:
        urls += read_sitemap(c, seen, depth + 1)
    return urls


def discover_sitemaps(domain):
    """從 robots.txt 找 Sitemap:，找不到就試常見路徑。"""
    domain = domain.strip().rstrip("/")
    base = domain if "://" in domain else "https://" + domain
    found = []
    try:
        txt = fetch(base + "/robots.txt").decode("utf-8", "ignore")
        found = [line.split(":", 1)[1].strip() for line in txt.splitlines()
                 if line.lower().startswith("sitemap:")]
    except Exception:
        pass
    if found:
        return found
    for path in ("/sitemap_index.xml", "/sitemap.xml", "/wp-sitemap.xml"):
        try:
            parse_sitemap_xml(fetch(base + path))
            return [base + path]
        except Exception:
            continue
    return []


def read_lines(path):
    with open(path, encoding="utf-8-sig") as f:
        return [line.strip() for line in f
                if line.strip() and not line.strip().startswith("#")]


# ---------------------------------------------------------------- 快取

class Cache:
    def __init__(self, path, max_age_days):
        self.path = path
        self.max_age = max_age_days * 86400
        self.lock = threading.Lock()
        self.data = {}
        if path and os.path.exists(path):
            try:
                with open(path, encoding="utf-8") as f:
                    self.data = json.load(f)
            except Exception:
                self.data = {}

    def get(self, k):
        v = self.data.get(k)
        if v and time.time() - v["ts"] <= self.max_age:
            return v
        return None

    def put(self, k, links, total):
        with self.lock:
            self.data[k] = {"ts": time.time(), "links": links, "total": total}

    def save(self):
        if not self.path:
            return
        with self.lock:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False)
            os.replace(tmp, self.path)


# ---------------------------------------------------------------- API

class BudgetExceeded(Exception):
    pass


class FatalAPIError(Exception):
    pass


class Client:
    def __init__(self, key, args, cache, budget):
        self.key = key
        self.args = args
        self.cache = cache
        self.budget = budget
        self.spent = 0
        self.requests = 0
        self.cache_hits = 0
        self.lock = threading.Lock()
        self.fatal = None

    def cache_key(self, query, page):
        a = self.args
        return f"{query}|p{page}|{a.country}|{GOOGLE_DOMAIN}|{a.language}"

    def search(self, query, page=0, force=False):
        """回傳 (links, total_results)。有快取就不扣額度；force=True 時略過快取重查。"""
        ck = self.cache_key(query, page)
        hit = None if force else self.cache.get(ck)
        if hit:
            with self.lock:
                self.cache_hits += 1
            return hit["links"], hit["total"]
        if self.fatal:
            raise FatalAPIError(self.fatal)
        with self.lock:
            if self.spent + CREDITS_PER_REQ > self.budget:
                raise BudgetExceeded()
            self.spent += CREDITS_PER_REQ  # 先預扣，失敗再退回
        try:
            links, total = self._call(query, page)
        except Exception:
            with self.lock:
                self.spent -= CREDITS_PER_REQ
            raise
        self.cache.put(ck, links, total)
        with self.lock:
            self.requests += 1
            save_now = self.requests % 20 == 0
        if save_now:
            self.cache.save()
        return links, total

    def _call(self, query, page):
        a = self.args
        params = {"api_key": self.key, "query": query, "filter": "0"}
        if page:
            params["page"] = str(page * 10 if a.page_style == "offset" else page)
        if a.country:
            params["country"] = a.country
        params["domain"] = GOOGLE_DOMAIN
        if a.language:
            params["language"] = a.language
        last_err = None
        for attempt in range(4):
            try:
                r = requests.get(API_URL, params=params, timeout=60)
            except requests.RequestException as e:
                last_err = f"連線錯誤：{e.__class__.__name__}"
                time.sleep(2 * (attempt + 1))
                continue
            if r.status_code in (401, 403):
                self.fatal = f"HTTP {r.status_code}：API key 錯誤或額度用完。{r.text[:200]}"
                raise FatalAPIError(self.fatal)
            if r.status_code == 429 or r.status_code >= 500:
                last_err = f"HTTP {r.status_code}"
                time.sleep(3 * (attempt + 1))
                continue
            if r.status_code != 200:
                raise RuntimeError(f"HTTP {r.status_code}：{r.text[:200]}")
            data = r.json()
            organic = data.get("organic_results") or []
            links = [o.get("link") for o in organic if o.get("link")]
            info = data.get("search_information") or {}
            return links, info.get("total_results")
        raise RuntimeError(last_err or "重試多次仍失敗")


# ---------------------------------------------------------------- 兩種查法

def check_single(client, url, force=False):
    """site:網址，看結果裡有沒有完全相同的網址。"""
    target = norm(url)
    links, _ = client.search(single_query(url), 0, force=force)
    for link in links:
        if norm(link) == target:
            return "已收錄", link, ""
    note = f"有 {len(links)} 筆相近結果但不是這條" if links else ""
    return "未收錄", "", note


def sweep_domain(client, domain, max_pages, wanted=None):
    """site:網域 一頁一頁翻。wanted 有值時，清單全部找到就提早停。"""
    found, order = set(), []
    pages, total, prev = 0, None, None
    for page in range(max_pages):
        links, t = client.search(f"site:{domain}", page)
        pages += 1
        if total is None:
            total = t
        if not links:
            break
        sig = tuple(links)
        if sig == prev:
            print(f"  ! {domain} 第 {page + 1} 頁和上一頁一樣，翻頁參數可能不對，"
                  f"停止掃描（可試 --page-style offset）")
            break
        prev = sig
        for link in links:
            n = norm(link)
            if n not in found:
                found.add(n)
                order.append(link)
        if wanted is not None and wanted <= found:
            break
        if len(links) < RESULTS_PER_PAGE:
            break
    return order, pages, total


# ---------------------------------------------------------------- 主流程

def collect_urls(args):
    raw = []
    if args.urls:
        raw += read_lines(args.urls)
    for sm in args.sitemap or []:
        print(f"讀取 sitemap：{sm}")
        raw += read_sitemap(sm)
    if args.sites:
        for d in read_lines(args.sites):
            sms = discover_sitemaps(d)
            if not sms:
                print(f"  ! {d} 找不到 sitemap，略過")
                continue
            print(f"{d}：找到 sitemap {', '.join(sms)}")
            for sm in sms:
                raw += read_sitemap(sm)
    seen, out = set(), []
    for u in raw:
        n = norm(u)
        if n and n not in seen:
            seen.add(n)
            out.append(u.strip())
    return out


def sweep_cap(n, args):
    if args.mode == "domain":
        return args.max_pages
    # hybrid：掃描頁數最多約「清單數 × 2 / 10」，再多就不如逐條查
    return max(1, min(args.max_pages, math.ceil(n * args.sweep_factor / RESULTS_PER_PAGE)))


def estimate(groups, args, cache):
    probe = Client("", args, cache, 0)
    url_cost = sum(CREDITS_PER_REQ for v in groups.values() for u in v
                   if not cache.get(probe.cache_key(single_query(u), 0)))
    caps = {d: sweep_cap(len(v), args) for d, v in groups.items()}
    sweep_cost = sum(caps.values()) * CREDITS_PER_REQ
    if args.mode == "url":
        upper = typical = url_cost
    elif args.mode == "domain":
        upper = typical = sweep_cost
    else:
        upper = sweep_cost + url_cost
        typical = sweep_cost + url_cost // 3  # 假設網域掃描能找到約 2/3
    return url_cost, caps, upper, typical


def build_parser():
    ap = argparse.ArgumentParser(description="用 ScrapingDog 批次檢查網址是否被 Google 收錄")
    src = ap.add_argument_group("網址來源（可混用）")
    src.add_argument("--urls", help="文字檔，一行一個網址")
    src.add_argument("--sitemap", action="append", help="sitemap 網址，可重複給多個")
    src.add_argument("--sites", help="文字檔，一行一個網域，自動找 sitemap（適合同時管理多個網站）")
    ap.add_argument("--mode", choices=["hybrid", "url", "domain"], default="hybrid")
    ap.add_argument("--max-pages", type=int, default=30, help="每個網域最多翻幾頁（每頁 5 credits）")
    ap.add_argument("--sweep-factor", type=float, default=2.0,
                    help="hybrid 時掃描頁數上限 = 清單數 × 此值 / 10")
    ap.add_argument("--exclude", action="append", default=[], help="額外排除的網址 regex，可重複")
    ap.add_argument("--no-default-exclude", action="store_true", help="不要套用預設排除規則")
    ap.add_argument("--country", default="", help="Google 地區代碼，例如 tw、jp、us（網域固定用 google.com）")
    ap.add_argument("--language", default="", help="例如 en、ja")
    ap.add_argument("--page-style", choices=["index", "offset"], default="index",
                    help="翻頁參數格式：index=0,1,2；offset=0,10,20")
    ap.add_argument("--workers", type=int, default=3, help="同時查詢數")
    ap.add_argument("--budget", type=int, default=0, help="本次最多花幾 credits（預設 = 預估上限）")
    ap.add_argument("--cache-days", type=float, default=3, help="幾天內查過的直接用快取，不再扣額度")
    ap.add_argument("--out", default="", help="輸出資料夾（預設 output/日期時間）")
    ap.add_argument("--dry-run", action="store_true", help="只算預估額度，不打 API")
    ap.add_argument("--yes", action="store_true", help="跳過確認直接執行")
    return ap


def main(argv=None, client_factory=None):
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    ap = build_parser()
    args = ap.parse_args(argv)
    if not (args.urls or args.sitemap or args.sites):
        ap.error("請給 --urls、--sitemap 或 --sites 其中至少一個")

    # 1. 收集網址 + 過濾非 SEO 頁面
    urls = collect_urls(args)
    patterns = ([] if args.no_default_exclude else DEFAULT_EXCLUDES) + args.exclude
    rx = re.compile("|".join(patterns), re.I) if patterns else None
    kept = [u for u in urls if not (rx and rx.search(unquote(u)))]
    skipped = len(urls) - len(kept)
    groups = defaultdict(list)
    for u in kept:
        groups[host_of(u)].append(u)

    cache = Cache(os.path.join(HERE, "cache.json"), args.cache_days)
    url_cost, caps, upper, typical = estimate(groups, args, cache)

    print()
    print(f"網址總數 {len(urls)}，排除非 SEO 頁面 {skipped} 條，要檢查 {len(kept)} 條，共 {len(groups)} 個網域")
    print(f"模式：{args.mode}")
    print(f"  全部逐條查（url 模式）需要 {url_cost} credits（已扣掉快取）")
    if args.mode != "url":
        pages = sum(caps.values())
        print(f"  網域掃描上限 {pages} 頁 = {pages * CREDITS_PER_REQ} credits")
    print(f"預估花費：約 {typical} credits，最多 {upper} credits")
    if not kept:
        print("沒有要檢查的網址。")
        return
    if args.dry_run:
        print("（dry-run，沒有打 API，沒有花額度）")
        return

    budget = args.budget or upper
    if client_factory:
        client = client_factory(args, cache, budget)
    else:
        key = load_api_key()
        if not key:
            sys.exit("找不到 API key：請設定環境變數 SCRAPINGDOG_API_KEY，或在本資料夾建立 .env")
        client = Client(key, args, cache, budget)
    if not args.yes:
        ans = input(f"\n本次額度上限 {budget} credits，確定要執行嗎？輸入 yes 繼續：").strip().lower()
        if ans != "yes":
            print("已取消，沒有花任何額度。")
            return

    results = {}       # norm -> row
    sweep_info = {}    # domain -> (pages, links, total)
    lock = threading.Lock()

    def set_row(u, status, method, matched="", note=""):
        with lock:
            results[norm(u)] = {
                "url": u, "domain": host_of(u), "status": status, "method": method,
                "matched_link": matched, "note": note, "checked_at": now_str(),
            }

    try:
        # 2. 網域掃描
        if args.mode in ("domain", "hybrid"):
            def do_sweep(d):
                wanted = {norm(u) for u in groups[d]}
                try:
                    links, pages, total = sweep_domain(
                        client, d, caps[d], wanted if args.mode == "hybrid" else None)
                except BudgetExceeded:
                    print(f"  ! {d} 掃描時碰到額度上限")
                    return
                except Exception as e:
                    print(f"  ! {d} 掃描失敗：{e}")
                    return
                sweep_info[d] = (pages, links, total)
                found = {norm(link): link for link in links}
                hit = 0
                for u in groups[d]:
                    if norm(u) in found:
                        set_row(u, "已收錄", "網域掃描", found[norm(u)])
                        hit += 1
                print(f"  {d}：翻 {pages} 頁，Google 列出 {len(links)} 條，清單中找到 {hit}/{len(groups[d])}")

            print("\n[1] 網域掃描")
            with ThreadPoolExecutor(max_workers=args.workers) as ex:
                list(ex.map(do_sweep, list(groups)))

        # 3. 逐條查
        remaining = [u for v in groups.values() for u in v if norm(u) not in results]
        if args.mode == "domain":
            for u in remaining:
                set_row(u, "未在掃描中出現", "網域掃描", note="不一定沒收錄，可用 url 模式複查")
        elif remaining:
            print(f"\n[2] 逐條查詢 {len(remaining)} 條")
            done = [0]

            def do_one(u):
                try:
                    status, matched, note = check_single(client, u)
                    set_row(u, status, "逐條查詢", matched, note)
                except BudgetExceeded:
                    set_row(u, "略過", "逐條查詢", note="額度上限已到")
                except Exception as e:
                    set_row(u, "錯誤", "逐條查詢", note=str(e)[:150])
                with lock:
                    done[0] += 1
                    if done[0] % 25 == 0 or done[0] == len(remaining):
                        print(f"  進度 {done[0]}/{len(remaining)}，已花 {client.spent} credits")

            with ThreadPoolExecutor(max_workers=args.workers) as ex:
                list(ex.map(do_one, remaining))
    except KeyboardInterrupt:
        print("\n中斷了，先把已查到的結果存起來。")
    finally:
        cache.save()

    # 4. 輸出
    out = args.out or os.path.join(HERE, "output", datetime.now().strftime("%Y%m%d_%H%M%S"))
    os.makedirs(out, exist_ok=True)
    for u in kept:
        if norm(u) not in results:
            set_row(u, "略過", "", note="未執行（中斷或額度用完）")

    fields = ["url", "domain", "status", "method", "matched_link", "note", "checked_at"]
    with open(os.path.join(out, "results.csv"), "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for u in kept:
            w.writerow(results[norm(u)])

    listed = {norm(u) for u in kept}
    with open(os.path.join(out, "extra_indexed.csv"), "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(["domain", "link", "is_junk"])
        for d, (_, links, _) in sweep_info.items():
            for link in links:
                if norm(link) not in listed:
                    w.writerow([d, link, "yes" if rx and rx.search(unquote(link)) else ""])

    with open(os.path.join(out, "domain_summary.csv"), "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(["domain", "checked", "indexed", "not_indexed", "skipped_or_error",
                    "index_rate", "sweep_pages", "sweep_links", "google_total_estimate"])
        for d, us in groups.items():
            rows = [results[norm(u)] for u in us]
            ok = sum(r["status"] == "已收錄" for r in rows)
            no = sum(r["status"] in ("未收錄", "未在掃描中出現") for r in rows)
            pages, links, total = sweep_info.get(d, (0, [], ""))
            rate = f"{ok / (ok + no):.0%}" if ok + no else ""
            w.writerow([d, len(rows), ok, no, len(rows) - ok - no, rate,
                        pages, len(links), total or ""])

    ok = sum(r["status"] == "已收錄" for r in results.values())
    print()
    print(f"完成：已收錄 {ok}/{len(kept)}")
    print(f"實際花費 {client.spent} credits（{client.requests} 次 API 呼叫，"
          f"{client.cache_hits} 次用快取免費）")
    print(f"結果在：{out}")
    return out


if __name__ == "__main__":
    main()
