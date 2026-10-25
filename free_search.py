#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""free_search.py —— 零依赖免费网页搜索命令行工具（个人自用）

纪律（写死在文件里，不许删）：
  · 本工具仅供个人学习与自用（查资料、查文档），不做批量抓取。
  · 遵守目标站点 robots.txt 与服务条款；每次调用每个源最多发 1 次普通 GET
    （searx 特殊：JSON 失败后允许补 1 次 HTML，共 ≤2 次）；降级换源时两次
    请求之间强制间隔 ≥1.2 秒；只带正常浏览器 User-Agent，不做任何反爬对抗、
    不用代理池、不伪造指纹。超时即放弃该源。
  · 只用 Python 标准库（urllib / json / re / html / argparse / sys），零第三方依赖。

用法：
  python free_search.py "查询词"                     # auto：按实测可用性自动选源+降级
  python free_search.py "查询词" --limit 8
  python free_search.py "查询词" --source bing       # bing|sogou|so360|baidu|searx|github|auto

输出（stdout，纯文本）：每条结果 3 行——
  1. 标题
     链接: https://...
     摘要: ...
最后一行固定：实际使用源: xxx（auto 降级链中每个被跳过源的原因走 stderr）

已知实测特征（2026-10-24 用 3 个真实查询验证）：
  · bing：三个测试查询全成功、摘要完整；但中文社区类查询（如"虎扑 社区规则"）
    相关度一般（疑似把"虎扑"拆成"虎"+"扑"）。
  · sogou：中文社区类查询相关度明显更好，但部分结果没有摘要，且链接是搜狗
    站内跳转链接（/link?url=...，点开可达原页面）。
  → 用法建议：默认 auto（先 bing）；查中文社区/平台规则相关度差时，加 --source sogou。
"""
# 设计依据（2026-10-24 实际探活测试）：
#   bing / sogou / so360 / baidu / github 均 200 且含真实结果块；
#   searx 公共实例（searx.be、search.bus-hit.me，JSON 与 HTML）全部超时 →
#   searx 不进 auto 降级链，仅在 --source searx 显式指定时尝试。

import argparse
import html as html_mod
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

VERSION = "1.0"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")
HEADERS = {
    "User-Agent": UA,
    "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
    "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.6",
}
GITHUB_HEADERS = dict(HEADERS, Accept="application/vnd.github+json")
TIMEOUT = 15
DEGRADE_SLEEP = 1.2          # 换源重试前强制 ≥1.2 秒，避免高频
SEARX_URL = "https://searx.be"   # 探活显示本机网络不可达；留作显式指定用，可按需改实例

MAX_SNIPPET = 120


# ---------------------------------------------------------------- 基础工具

def _get(url, headers=None):
    """发一次 GET。返回 (status, body_bytes, err)；err 非 None 时视为该源失败。"""
    req = urllib.request.Request(url, headers=headers or HEADERS, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            return resp.status, resp.read(), None
    except urllib.error.HTTPError as e:
        try:
            data = e.read()
        except Exception:
            data = b""
        return e.code, data, "HTTP %s（%s），返回 %d 字节" % (e.code, e.reason, len(data))
    except Exception as e:                      # URLError / timeout 等
        return None, b"", "%s: %s" % (type(e).__name__, e)


def _clean(s):
    """去标签 + 反转义 + 折叠空白。"""
    s = re.sub(r"<[^>]+>", " ", s)
    s = html_mod.unescape(s)
    return re.sub(r"\s+", " ", s).strip()


def _mk(title, url, snippet):
    """构造一条结果，snippet 截断到 MAX_SNIPPET。"""
    return {"title": _clean(title)[:80],
            "url": url,
            "snippet": _clean(snippet or "")[:MAX_SNIPPET]}


def _extract_title_link(block, base_url):
    """在结果块里抓 (标题, 链接)。优先 h2/h3 内第一个 <a>；链接优先 data-mdurl/mu 真实地址。"""
    m = re.search(r"<h[23][^>]*>(.*?)</h[23]>", block, re.S)
    if not m:
        return None
    h3 = m.group(0)
    title_m = re.search(r"<a[^>]*>(.*?)</a>", h3, re.S)
    title = _clean(title_m.group(1) if title_m else re.sub(r"<[^>]+>", " ", m.group(1)))
    if not title:
        return None
    url_m = re.search(r'\b(?:data-mdurl|mu)="([^"]+)"', h3)
    href_m = re.search(r'<a[^>]*href="([^"]*)"', h3, re.S)
    url = html_mod.unescape((url_m.group(1) if url_m else
                             (href_m.group(1) if href_m else "")) or "")
    if url.startswith("//"):
        url = "https:" + url
    elif url.startswith("/link"):
        url = base_url + url                    # 搜狗等站内跳转链接
    elif url.startswith("/"):
        url = base_url + url
    return title, url


def _split(text, marker_re):
    """按结果块开头标志把页面切成块（去掉第一段页头）。"""
    parts = re.split(marker_re, text)
    return parts[1:] if len(parts) > 1 else []


# ---------------------------------------------------------------- 各源解析

def _parse_generic(text, marker_re, base_url, snippet_res, min_title_n=1):
    """通用 HTML 结果页解析：切块 → 每块抓标题/链接 → 按 snippet_res 候选抓摘要。"""
    out = []
    for block in _split(text, marker_re):
        tl = _extract_title_link(block, base_url)
        if not tl:
            continue
        title, url = tl
        snippet = ""
        for sr in snippet_res:
            m = re.search(sr, block, re.S)
            if m:
                snippet = _clean(m.group(1))
                if len(snippet) >= 12:          # 太短视为没抓准，试下一个候选
                    break
                snippet = snippet or _clean(m.group(1))
        out.append(_mk(title, url, snippet))
    return out


def parse_bing(text):
    """Bing 结果页：<li class="b_algo"> 块，标题在 <h2><a>，摘要是块内第一段 <p>。"""
    return _parse_generic(
        text, r'(?=<li\s+class="b_algo")', "https://www.bing.com",
        [r"<p[^>]*>(.*?)</p>"])


def parse_sogou(text):
    """搜狗结果页：<div class="vrwrap"> 或 <div class="rb"> 块，标题在 <h3 class="vr-title">。"""
    return _parse_generic(
        text, r'(?=<div class="(?:vrwrap|rb)")', "https://www.sogou.com",
        [r'<p class="star-wiki[^"]*"[^>]*>(.*?)</p>', r"<p[^>]*>(.*?)</p>"])


def parse_so360(text):
    """360 搜索结果页：<li class="res-list"> 块（真实地址常在 h3 的 data-mdurl 属性）。"""
    return _parse_generic(
        text, r'(?=<li\s+class="res-list)', "https://www.so.com",
        [r'<p class="res-desc[^"]*"[^>]*>(.*?)</p>', r"<p[^>]*>(.*?)</p>"])


def parse_baidu(text):
    """百度结果页：<div class="result..."> 块（真实地址常在 h3 的 mu 属性；链接多为百度跳转链接）。"""
    return _parse_generic(
        text, r'(?=<div class="result)', "https://www.baidu.com",
        [r'<span class="content-right[^"]*"[^>]*>(.*?)</span>', r"<p[^>]*>(.*?)</p>"])


def search_bing(query, limit):
    url = ("https://www.bing.com/search?q=%s&setlang=zh-CN"
           % urllib.parse.quote_plus(query))
    status, data, err = _get(url)
    text = data.decode("utf-8", errors="replace")
    if err or status != 200:
        return None, "%s" % (err or "HTTP %s" % status)
    res = parse_bing(text)
    return res[:limit], "200，%d 字节，解析出 %d 条" % (len(data), len(res))


def search_sogou(query, limit):
    url = "https://www.sogou.com/web?query=%s" % urllib.parse.quote_plus(query)
    status, data, err = _get(url)
    text = data.decode("utf-8", errors="replace")
    if err or status != 200:
        return None, "%s" % (err or "HTTP %s" % status)
    res = parse_sogou(text)
    return res[:limit], "200，%d 字节，解析出 %d 条" % (len(data), len(res))


def search_so360(query, limit):
    url = "https://www.so.com/s?q=%s" % urllib.parse.quote_plus(query)
    status, data, err = _get(url)
    text = data.decode("utf-8", errors="replace")
    if err or status != 200:
        return None, "%s" % (err or "HTTP %s" % status)
    res = parse_so360(text)
    return res[:limit], "200，%d 字节，解析出 %d 条" % (len(data), len(res))


def search_baidu(query, limit):
    url = "https://www.baidu.com/s?wd=%s" % urllib.parse.quote_plus(query)
    status, data, err = _get(url)
    text = data.decode("utf-8", errors="replace")
    if err or status != 200:
        return None, "%s" % (err or "HTTP %s" % status)
    if "百度安全验证" in text or "wappass" in text.lower():
        return None, "命中反爬验证页（不绕过，直接放弃该源）"
    res = parse_baidu(text)
    return res[:limit], "200，%d 字节，解析出 %d 条" % (len(data), len(res))


def search_github(query, limit):
    """GitHub 仓库搜索 API：免 key，官方限速 10 次/分钟，只做兜底源，不宜高频调用。"""
    url = ("https://api.github.com/search/repositories?q=%s&per_page=%d"
           % (urllib.parse.quote_plus(query), min(limit, 30)))
    status, data, err = _get(url, GITHUB_HEADERS)
    if err or status != 200:
        return None, "%s" % (err or "HTTP %s" % status)
    try:
        obj = json.loads(data.decode("utf-8"))
    except ValueError as e:
        return None, "非 JSON 回包（%s）" % e
    items = obj.get("items") or []
    res = [_mk(it.get("name", it.get("full_name", "")),
               it.get("html_url", ""), it.get("description", ""))
           for it in items]
    return res[:limit], "200，%d 字节，items N=%d" % (len(data), len(items))


def search_searx(query, limit):
    """SearXNG 公共实例。探活显示本机网络不可达（超时）；仅在显式指定时尝试。
    纪律：JSON 一次 → 失败允许补一次 HTML，共 ≤2 次请求。"""
    note = []
    q = urllib.parse.quote_plus(query)
    h = dict(HEADERS, Accept="application/json")

    status, data, err = _get("%s/search?q=%s&format=json" % (SEARX_URL, q), h)
    note.append("json:%s" % (err or "HTTP %s" % status))
    if status == 200 and not err:
        try:
            obj = json.loads(data.decode("utf-8"))
            results = obj.get("results") or []
            res = [_mk(r.get("title", ""), r.get("url", ""), r.get("content", ""))
                   for r in results]
            if res:
                return res[:limit], "json 200，%d 字节，results N=%d" % (len(data), len(results))
            note.append("json 无 results")
        except ValueError as e:
            note.append("json 解析失败(%s)" % e)

    time.sleep(DEGRADE_SLEEP)                    # 两次请求之间 ≥1.2 秒
    status, data, err = _get("%s/search?q=%s" % (SEARX_URL, q))
    note.append("html:%s" % (err or "HTTP %s" % status))
    if status == 200 and not err:
        text = data.decode("utf-8", errors="replace")
        res = []
        for block in re.split(r'(?=<article[^>]*class="[^"]*result)', text)[1:]:
            tl = _extract_title_link(block, SEARX_URL)
            if not tl:
                continue
            m = re.search(r"<p[^>]*>(.*?)</p>", block, re.S)
            res.append(_mk(tl[0], tl[1], m.group(1) if m else ""))
        if res:
            return res[:limit], "html 200，%d 字节，解析出 %d 条" % (len(data), len(res))
    return None, "；".join(note)


# 引擎注册表：顺序即 auto 降级顺序（依据 2026-10-24 探活实测）
ENGINE_ORDER = ["bing", "sogou", "so360", "baidu", "searx", "github"]
AUTO_ORDER = ["bing", "sogou", "so360", "baidu", "github"]   # searx 连不上，不进 auto
SEARCHERS = {
    "bing": search_bing,
    "sogou": search_sogou,
    "so360": search_so360,
    "baidu": search_baidu,
    "searx": search_searx,
    "github": search_github,
}


def do_search(query, limit, source):
    """按 source 搜索。返回 (results, used_source, attempts)。
    attempts: [(源, 状态说明)]，状态说明含成功时的证据摘要。"""
    attempts = []
    order = AUTO_ORDER if source == "auto" else [source]
    for i, name in enumerate(order):
        if i > 0:
            time.sleep(DEGRADE_SLEEP)            # 换源之前强制间隔 ≥1.2 秒
        try:
            res, note = SEARCHERS[name](query, limit)
        except Exception as e:                   # 任何意外不让工具崩，当该源失败
            res, note = None, "异常 %s: %s" % (type(e).__name__, e)
        if res is None or not res:
            attempts.append((name, "失败：" + (note or "无结果")))
            continue
        attempts.append((name, "成功：" + note))
        return res, name, attempts
    return None, None, attempts


# ---------------------------------------------------------------- 输出与入口

def print_results(results, used, attempts):
    for i, r in enumerate(results, 1):
        print("%d. %s" % (i, r["title"]))
        print("   链接: %s" % (r["url"] or "（无）"))
        print("   摘要: %s" % (r["snippet"] or "（无）"))
    chain = " -> ".join("%s(%s)" % (n, s[:2]) for n, s in attempts)
    print("实际使用源: %s（尝试链：%s）" % (used, chain))


def main(argv=None):
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    p = argparse.ArgumentParser(
        description="零依赖免费搜索命令行工具（个人自用，遵守 robots.txt，不做高频抓取）")
    p.add_argument("query", help="查询词（如 \"虎扑 社区规则\"）")
    p.add_argument("--limit", type=int, default=8, help="返回条数，默认 8")
    p.add_argument("--source", default="auto",
                   choices=["auto"] + ENGINE_ORDER,
                   help="搜索源，默认 auto（按探活实测顺序自动降级）")
    p.add_argument("--version", action="version", version="free_search.py " + VERSION)
    args = p.parse_args(argv)

    query = args.query.strip()
    if not query:
        p.error("查询词不能为空")
    if args.limit < 1:
        p.error("--limit 必须 ≥1")

    results, used, attempts = do_search(query, args.limit, args.source)

    for name, note in attempts:
        ok = name == used
        if not ok or args.source != "auto":
            print("[%s] %s" % (name, note), file=sys.stderr)

    if results is None:
        print("所有源都失败了，未拿到任何结果。", file=sys.stderr)
        for name, note in attempts:
            print("  %s: %s" % (name, note), file=sys.stderr)
        return 1
    print_results(results, used, attempts)
    return 0


if __name__ == "__main__":
    sys.exit(main())
