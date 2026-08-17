# X4 News & Biography Library

CrossPoint (XTEINK X4) 向けの、毎朝自動更新されるニュースダイジェスト配信システム。
Mac常時起動不要。GitHub Actions + GitHub Pages で完結する。

## 構成

```
x4-news-library/
├── .github/workflows/daily-digest.yml   ← 毎朝自動実行するワークフロー
├── config/sources.yaml                  ← 取得元・キーワード・地域の設定
├── scripts/build_digest.py              ← 収集・要約・EPUB生成本体
├── books/                                ← 生成されたEPUB(自動コミットされる)
├── biographies/                          ← 青空文庫等の伝記EPUBを手動配置する場所
├── feed.xml                              ← OPDSカタログ(自動生成)
└── requirements.txt
```

## セットアップ手順(初回のみ)

### 1. GitHubリポジトリ作成

- 新規リポジトリを作成(公開/非公開どちらでも可。ただしGitHub Pagesは
  Freeプランの場合パブリックリポジトリでのみ無料利用可能な点に注意)
- このフォルダの中身一式をpush

### 2. GitHub Pages を有効化

- リポジトリの Settings → Pages
- Source を「Deploy from a branch」、ブランチを `main` / ルート(`/`)に設定
- 公開URLが `https://<username>.github.io/<repo>/` の形で発行される
- OPDSサーバーURLは `https://<username>.github.io/<repo>/feed.xml` になる

### 3. Gemini APIキーをリポジトリに登録

- Google AI Studio (https://aistudio.google.com) でAPIキーを発行
- リポジトリの Settings → Secrets and variables → Actions
- 「New repository secret」で以下を登録
  - Name: `GEMINI_API_KEY`
  - Value: 発行したAPIキー

### 4. 動作確認(手動実行)

- リポジトリの Actions タブ → 「Daily News Digest」を選択
- 「Run workflow」で手動実行し、正常に `books/` と `feed.xml` が更新されるか確認
- エラーが出た場合はログを確認(RSSのURLが実在するか等、要検証項目あり。下記「未検証項目」参照)

### 5. X4 (CrossPoint) 側の設定

- Settings → System → OPDS Servers → Add Server
- Server Name: 任意(例: News Digest)
- OPDS Server URL: `https://<username>.github.io/<repo>/feed.xml`
- Wi-Fi接続時に OPDS Servers からブラウズ・ダウンロード可能

## 伝記の追加方法

`biographies/` フォルダに青空文庫等から変換したEPUBを配置し、
feed.xml に手動でエントリを追加(または将来的にスクリプトを拡張して自動化可能)。
現状のスクリプトはニュースダイジェストのみ自動化対象。

## 未検証項目(実運用前に確認が必要)

- `config/sources.yaml` 内のRSS URL(NHKニュースの実際のフィードURL)は
  今回未検証のプレースホルダ。実際にブラウザ/curlでアクセスして存在確認が必要
- Gemini APIのモデル名(`gemini-3.5-flash`)は世代交代が速いため、
  実行時にエラーが出た場合は最新のモデル名に差し替える
  (`GEMINI_MODEL` 環境変数、または workflow の env で上書き可能)
- 気象庁の概況JSON (`overview_forecast`) は非公式提供のため、
  将来的にURL構造が変わる可能性がある
- 記事本文取得(`fetch_article_text`)は簡易的なHTMLタグ除去のみで、
  サイトによっては不要な文字列(広告・ナビ等)が混入する可能性がある。
  要約精度が悪い場合はサイトごとの本文抽出ロジック追加を検討

## 保持期間

デフォルトで直近7日分のEPUBのみ保持し、古いものは自動削除される
(`build_digest.py` の `retain_days` で変更可能)。
