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
SENT_LOG_PATH = ROOT / "sent_articles.json"

GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.5-flash")  # モデル名は環境変数で差し替え可能にしておく
GEMINI_ENDPOINT = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"

JST = timezone(timedelta(hours=9))

# GitHub PagesのベースURL(相対パスの解決に依存しないよう、リンクは絶対URLで出力する)
SITE_BASE_URL = os.environ.get("SITE_BASE_URL", "https://gigabiter-v2.github.io/news-library")


def load_config():
    with open(CONFIG_PATH, encoding="utf-8") as f:
        return yaml.safe_load(f)


def load_sent_log(retain_days=7):
    """
    過去に配信済みの記事URLを {url: 配信日時ISO文字列} の形で読み込む。
    保持期間より古いものは読み込み時点で自動的に切り捨てる(ファイル肥大化防止)。
    """
    if not SENT_LOG_PATH.exists():
        return {}
    try:
        with open(SENT_LOG_PATH, encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"[WARN] 配信履歴の読み込み失敗(空として扱う): {e}", file=sys.stderr)
        return {}

    cutoff = datetime.now(JST) - timedelta(days=retain_days)
    kept = {}
    for url, sent_at in data.items():
        try:
            sent_dt = datetime.fromisoformat(sent_at)
            if sent_dt >= cutoff:
                kept[url] = sent_at
        except Exception:
            continue  # 壊れた日時が入っていた場合はそのエントリだけ捨てる
    return kept


def save_sent_log(sent_log):
    with open(SENT_LOG_PATH, "w", encoding="utf-8") as f:
        json.dump(sent_log, f, ensure_ascii=False, indent=2)


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


def fetch_rss_articles(cfg, sent_log):
    """RSSから記事一覧(タイトル・URL・descriptionのみ)を取得し、キーワードでフィルタ。
    sent_logに含まれるURL(過去配信済み)は除外する。
    """
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

            if not link or link in sent_log:
                continue  # 過去に配信済みの記事は除外

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


def fetch_article_text(url, timeout=15, retries=1):
    """要約生成のためだけに本文を一時取得する。保存はしない。
    NHKニュースサイト(news.web.nhk)は自動アクセスを403で一律ブロックしているため、
    無駄なリトライを避けて即座に諦める。
    """
    import re
    if "news.web.nhk" in url:
        return ""
    for attempt in range(retries + 1):
        try:
            resp = requests.get(url, timeout=timeout, headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"})
            resp.raise_for_status()
            resp.encoding = resp.apparent_encoding  # 文字化け対策
            # 簡易的なタグ除去(本格的な抽出はしない。要約精度が悪ければ改善余地あり)
            text = re.sub(r"<script[^>]*>.*?</script>", " ", resp.text, flags=re.DOTALL)
            text = re.sub(r"<style[^>]*>.*?</style>", " ", text, flags=re.DOTALL)
            text = re.sub(r"<[^>]+>", " ", text)
            text = re.sub(r"\s+", " ", text).strip()
            if len(text) > 100:  # 極端に短い(取得失敗の可能性が高い)場合はリトライ
                return text[:5000]  # 要約入力として十分な長さに制限
        except Exception as e:
            print(f"[WARN] 本文取得失敗(試行{attempt+1}/{retries+1}) {url}: {e}", file=sys.stderr)
        if attempt < retries:
            time.sleep(1)
    return ""


def summarize_with_gemini(title, body_text, summary_hint, target_length):
    """Gemini APIで要約を生成する。失敗時はNoneを返す(呼び出し側でRSS summaryにフォールバック)。
    本文が取得できなかった場合(NHKなど)は、タイトルとRSSの短い要約(summary_hint)を
    手がかりに、Geminiに内容を補って自然な文章にまとめてもらう。
    """
    if not GEMINI_API_KEY:
        return None
    if not body_text and not summary_hint:
        return None

    if body_text:
        source_text = f"本文: {body_text}"
        instruction = "元の文章表現をそのまま使わず、あなた自身の言葉で"
    else:
        # 本文が取得できない場合、RSSの短い抜粋(尻切れのことが多い)を素材に、
        # 一般的なニュース記事としてあり得る自然な文章に補って再構成してもらう。
        source_text = f"この記事の抜粋(尻切れの可能性あり): {summary_hint}"
        instruction = (
            "抜粋が文の途中で切れている場合は、無理に続きを創作せず、"
            "分かっている範囲の事実だけを使って自然な文章に整えて"
        )

    prompt = (
        f"以下はニュース記事の情報です。この記事の内容を、"
        f"{instruction}{target_length}字程度に要約してください。"
        f"事実関係(数字・固有名詞・時系列)は正確に保ち、憶測で新しい事実を付け加えないでください。"
        f"見出しやラベルは不要で、要約本文のみを出力してください。\n\n"
        f"タイトル: {title}\n\n{source_text}"
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
            <h2 style="margin-top:1.5em;margin-bottom:0.6em;">{escape(art['title'])}</h2>
            <p style="margin-top:0;margin-bottom:0.8em;line-height:1.7;">{escape(art['summary'])}</p>
            <p style="font-size:0.8em;margin-top:0;margin-bottom:1.2em;"><a href="{escape(art['link'])}">元記事: {escape(art['source'])}</a></p>
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
    固定ファイル名で毎回上書きする運用のため、feed.xmlには常に最新の1件のみが載る。
    """
    now_iso = datetime.now(JST).isoformat()

    entries_xml = ""
    for e in entries:
        entries_xml += f"""
  <entry>
    <title>{escape(e['title'])}</title>
    <id>urn:uuid:{escape(e['id'])}</id>
    <updated>{escape(e['updated'])}</updated>
    <link rel="http://opds-spec.org/acquisition"
          href="{escape(SITE_BASE_URL + '/books/' + e['filename'])}"
          type="application/epub+zip"/>
  </entry>"""

    feed_xml = f"""<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom"
      xmlns:opds="http://opds-spec.org/2010/catalog">
  <id>urn:uuid:x4-news-library-root</id>
  <title>{escape("News & Biography Library")}</title>
  <updated>{escape(now_iso)}</updated>
  <link rel="self" href="{escape(SITE_BASE_URL + '/feed.xml')}" type="application/atom+xml;profile=opds-catalog;kind=acquisition"/>{entries_xml}
</feed>
"""
    FEED_PATH.write_text(feed_xml, encoding="utf-8")
    print(f"[INFO] feed.xml 更新完了 ({len(entries)}件)")


def main():
    cfg = load_config()
    date_str = datetime.now(JST).strftime("%Y-%m-%d")

    sent_log = load_sent_log(retain_days=7)
    print(f"[INFO] 配信履歴 {len(sent_log)}件を読み込み(直近7日分を保持)")

    weather = fetch_weather(cfg)
    articles_by_category = fetch_rss_articles(cfg, sent_log)

    total_articles = sum(len(v) for v in articles_by_category.values())
    print(f"[INFO] 新規記事 {total_articles}件を取得(既読は除外済み)")

    summary_length = cfg.get("summary_length", 200)

    for category, articles in articles_by_category.items():
        for art in articles:
            body_text = fetch_article_text(art["link"])
            summary = summarize_with_gemini(art["title"], body_text, art["summary_hint"], summary_length)
            if not summary:
                # AI要約に失敗した場合はRSSのdescriptionを使う。
                # 350字に満たない場合はそのまま、超える場合は文の区切りで切る(単純な文字数カットで
                # 語尾が不自然に切れるのを避ける)。
                hint = (art["summary_hint"] or "").strip()
                if not hint:
                    summary = "(要約を取得できませんでした。元記事をご確認ください)"
                elif len(hint) <= summary_length:
                    summary = hint
                else:
                    cut = hint[:summary_length]
                    # 句点があれば、その位置までで切って不自然な尻切れを避ける
                    last_period = cut.rfind("。")
                    summary = cut[:last_period + 1] if last_period > summary_length * 0.5 else cut
            art["summary"] = summary
            # この記事を配信済みとして記録(次回以降のfetch_rss_articlesで除外される)
            sent_log[art["link"]] = datetime.now(JST).isoformat()
            time.sleep(4.5)  # 無料枠のRPM制限(15RPM程度)に収めるため、1リクエストあたり十分な間隔を空ける

    save_sent_log(sent_log)
    print(f"[INFO] 配信履歴を更新 (計{len(sent_log)}件を保持)")

    BOOKS_DIR.mkdir(exist_ok=True)
    # 固定ファイル名で毎回上書きする(ライブラリ内で本が増え続けて埋もれるのを防ぐため)。
    # タイトルには日付を入れて、いつの分か分かるようにする。
    filename = "latest_digest.epub"
    output_path = BOOKS_DIR / filename

    # 前回分が残っていれば削除してから作り直す(上書きだが念のため明示的にクリーンアップ)
    for old_f in BOOKS_DIR.glob("*.epub"):
        if old_f.name != filename:
            old_f.unlink()
            print(f"[INFO] 旧ファイル削除: {old_f.name}")

    book_id = build_epub(date_str, weather, articles_by_category, output_path)

    entries = [{
        "id": f"latest-digest-{date_str}",
        "title": f"ニュースダイジェスト {date_str}",
        "filename": filename,
        "updated": datetime.now(JST).isoformat(),
    }]

    update_opds_feed(cfg, entries)
    print(f"[INFO] 完了: {filename}")


if __name__ == "__main__":
    main()
