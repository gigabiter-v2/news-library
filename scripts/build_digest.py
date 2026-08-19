#!/usr/bin/env python3
"""
毎朝実行: 気象概況 + ニュース見出し(AI要約付き)をまとめてEPUB化し、
OPDSフィード(feed.xml)を更新するスクリプト。

設計方針(※事実と推測を分離):
- ニュース本文は保存しない。取得するのはタイトル・URL・RSSのdescription程度。
- 元記事本文はAI要約の入力としてのみ一時利用し、成果物には含めない。
- AIには「元の文章を切り貼りせず、自分の言葉で200字程度に要約する」ことを明示指示する。
- 気象庁の概況JSONは気象庁公式文なので、要約せずそのまま掲載する
  (概況自体が既に短い定型文のため)。
"""

import json
import os
import sys
import time
import uuid
import yaml
import feedparser
import requests
from datetime import datetime, timezone, timedelta
from pathlib import Path
from xml.sax.saxutils import escape
from ebooklib import epub

ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = ROOT / "config" / "sources.yaml"
BOOKS_DIR = ROOT / "books"
FEED_PATH = ROOT / "feed.xml"

GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.5-flash")  # モデル名は環境変数で差し替え可能にしておく
GEMINI_ENDPOINT = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"

JST = timezone(timedelta(hours=9))


def load_config():
    with open(CONFIG_PATH, encoding="utf-8") as f:
        return yaml.safe_load(f)


def fetch_weather(cfg):
    """気象庁の概況JSONを取得。失敗しても全体を止めない。"""
    if not cfg["weather"]["enabled"]:
        return None
    url = cfg["weather"]["url_template"].format(code=cfg["weather"]["area_code"])
    try:
        resp = requests.get(url, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        return {
            "area": cfg["weather"]["area_name"],
            "text": data.get("text", "").strip(),
            "report_datetime": data.get("reportDatetime", ""),
        }
    except Exception as e:
        print(f"[WARN] 気象庁データ取得失敗: {e}", file=sys.stderr)
        return None


def fetch_rss_articles(cfg):
    """RSSから記事一覧(タイトル・URL・descriptionのみ)を取得し、キーワードでフィルタ。"""
    articles_by_category = {}
    keyword_filter = cfg.get("keyword_filter", {})
    max_per_cat = cfg.get("max_articles_per_category", 8)

    for feed_cfg in cfg["rss_feeds"]:
        if not feed_cfg.get("enabled", True):
            continue
        category = feed_cfg["category"]
        try:
            parsed = feedparser.parse(feed_cfg["url"])
        except Exception as e:
            print(f"[WARN] RSS取得失敗 {feed_cfg['name']}: {e}", file=sys.stderr)
            continue

        keywords = keyword_filter.get(category, [])
        bucket = articles_by_category.setdefault(category, [])

        for entry in parsed.entries:
            title = entry.get("title", "")
            link = entry.get("link", "")
            summary_hint = entry.get("summary", "")

            if keywords and not any(kw in title for kw in keywords):
                continue

            bucket.append({
                "title": title,
                "link": link,
                "summary_hint": summary_hint,
                "source": feed_cfg["name"],
            })
            if len(bucket) >= max_per_cat:
                break

    return articles_by_category


def fetch_article_text(url, timeout=10):
    """要約生成のためだけに本文を一時取得する。保存はしない。"""
    try:
        resp = requests.get(url, timeout=timeout, headers={"User-Agent": "Mozilla/5.0"})
        resp.raise_for_status()
        # 簡易的なタグ除去(本格的な抽出はしない。要約精度が悪ければ改善余地あり)
        import re
        text = re.sub(r"<[^>]+>", " ", resp.text)
        text = re.sub(r"\s+", " ", text)
        return text[:4000]  # 要約入力として十分な長さに制限
    except Exception as e:
        print(f"[WARN] 本文取得失敗 {url}: {e}", file=sys.stderr)
        return ""


def summarize_with_gemini(title, body_text, target_length):
    """Gemini APIで要約を生成する。失敗時はNoneを返す(呼び出し側でRSS summaryにフォールバック)。"""
    if not GEMINI_API_KEY or not body_text:
        return None

    prompt = (
        f"以下はニュース記事の本文(一部)です。この記事の内容を、"
        f"元の文章表現をそのまま使わず、あなた自身の言葉で{target_length}字程度に要約してください。"
        f"事実関係(数字・固有名詞・時系列)は正確に保ってください。"
        f"見出しやラベルは不要で、要約本文のみを出力してください。\n\n"
        f"タイトル: {title}\n\n本文: {body_text}"
    )

    payload = {
        "contents": [{"parts": [{"text": prompt}]}]
    }

    try:
        resp = requests.post(
            f"{GEMINI_ENDPOINT}?key={GEMINI_API_KEY}",
            json=payload,
            timeout=30,
        )
        resp.raise_for_status()
        data = resp.json()
        return data["candidates"][0]["content"]["parts"][0]["text"].strip()
    except Exception as e:
        print(f"[WARN] Gemini要約失敗 ({title}): {e}", file=sys.stderr)
        return None


def build_epub(date_str, weather, articles_by_category, output_path):
    book = epub.EpubBook()
    book_id = str(uuid.uuid4())
    book.set_identifier(book_id)
    book.set_title(f"ニュースダイジェスト {date_str}")
    book.set_language("ja")
    book.add_author("News Digest Bot")

    chapters = []

    # 気象セクション
    if weather:
        weather_html = f"""
        <h1>気象 ({escape(weather['area'])})</h1>
        <p>{escape(weather['text'])}</p>
        <p style="font-size:0.8em;color:#666;">発表: {escape(weather['report_datetime'])}</p>
        """
        c = epub.EpubHtml(title="気象", file_name="weather.xhtml", lang="ja")
        c.content = weather_html
        book.add_item(c)
        chapters.append(c)

    category_labels = {
        "economy": "経済",
        "general": "主要ニュース",
        "tech": "技術・IT",
        "international": "国際",
        "society": "社会",
        "crypto": "仮想通貨",
        "car": "車",
        "medical": "医療業界",
        "finance_literacy": "金融リテラシー",
    }

    for category, articles in articles_by_category.items():
        label = category_labels.get(category, category)
        items_html = ""
        for art in articles:
            items_html += f"""
            <h2>{escape(art['title'])}</h2>
            <p>{escape(art['summary'])}</p>
            <p style="font-size:0.8em;"><a href="{escape(art['link'])}">元記事: {escape(art['source'])}</a></p>
            <hr/>
            """
        cat_html = f"<h1>{escape(label)}</h1>{items_html}"
        c = epub.EpubHtml(title=label, file_name=f"{category}.xhtml", lang="ja")
        c.content = cat_html
        book.add_item(c)
        chapters.append(c)

    book.toc = chapters
    book.add_item(epub.EpubNcx())
    book.add_item(epub.EpubNav())
    book.spine = ["nav"] + chapters

    epub.write_epub(str(output_path), book)
    return book_id


def update_opds_feed(cfg, entries):
    """
    entries: [{"id":..., "title":..., "filename":..., "updated":...}, ...]
    直近N日分のみをfeed.xmlに残す(古いものは自然に切り捨て)。
    """
    retain_days = 7
    cutoff = datetime.now(JST) - timedelta(days=retain_days)

    # 既存EPUBファイルのうち、期限内のものだけ列挙(booksディレクトリを正とする)
    kept_entries = []
    for entry in entries:
        kept_entries.append(entry)

    # 古いEPUBファイルを削除(保持期間外)
    for f in BOOKS_DIR.glob("*.epub"):
        try:
            date_part = f.stem.split("_")[0]  # 例: 2026-08-17_digest -> 2026-08-17
            file_date = datetime.strptime(date_part, "%Y-%m-%d").replace(tzinfo=JST)
            if file_date < cutoff:
                f.unlink()
                print(f"[INFO] 期限切れEPUB削除: {f.name}")
        except Exception:
            continue

    now_iso = datetime.now(JST).isoformat()

    entries_xml = ""
    for e in kept_entries:
        entries_xml += f"""
  <entry>
    <title>{escape(e['title'])}</title>
    <id>urn:uuid:{escape(e['id'])}</id>
    <updated>{escape(e['updated'])}</updated>
    <link rel="http://opds-spec.org/acquisition"
          href="{escape('books/' + e['filename'])}"
          type="application/epub+zip"/>
  </entry>"""

    feed_xml = f"""<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom"
      xmlns:opds="http://opds-spec.org/2010/catalog">
  <id>urn:uuid:x4-news-library-root</id>
  <title>{escape("News & Biography Library")}</title>
  <updated>{escape(now_iso)}</updated>
  <link rel="self" href="feed.xml" type="application/atom+xml;profile=opds-catalog;kind=acquisition"/>{entries_xml}
</feed>
"""
    FEED_PATH.write_text(feed_xml, encoding="utf-8")
    print(f"[INFO] feed.xml 更新完了 ({len(kept_entries)}件)")


def main():
    cfg = load_config()
    date_str = datetime.now(JST).strftime("%Y-%m-%d")

    weather = fetch_weather(cfg)
    articles_by_category = fetch_rss_articles(cfg)

    summary_length = cfg.get("summary_length", 200)

    for category, articles in articles_by_category.items():
        for art in articles:
            body_text = fetch_article_text(art["link"])
            summary = summarize_with_gemini(art["title"], body_text, summary_length)
            if not summary:
                # AI要約に失敗した場合はRSSのdescriptionを軽くトリムして代用
                summary = (art["summary_hint"] or "(要約取得失敗)")[:summary_length]
            art["summary"] = summary
            time.sleep(1)  # 無料枠のRPM対策として最低限の間隔を空ける

    BOOKS_DIR.mkdir(exist_ok=True)
    filename = f"{date_str}_digest.epub"
    output_path = BOOKS_DIR / filename
    book_id = build_epub(date_str, weather, articles_by_category, output_path)

    # 既存のfeed.xmlエントリを維持しつつ今回分を追加する設計に将来拡張可能。
    # 現状はシンプルに「booksディレクトリ内の直近ファイル」を都度スキャンして再構築する。
    all_entries = []
    for f in sorted(BOOKS_DIR.glob("*.epub")):
        d = f.stem.split("_")[0]
        all_entries.append({
            "id": f.stem,
            "title": f"ニュースダイジェスト {d}",
            "filename": f.name,
            "updated": f"{d}T00:00:00+09:00",
        })

    update_opds_feed(cfg, all_entries)
    print(f"[INFO] 完了: {filename}")


if __name__ == "__main__":
    main()
