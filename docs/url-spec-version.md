# 固定する仕様と test の version

## URL Standard

* repository: <https://github.com/whatwg/url>
* file: `url.bs`
* 取得日: 2026-09-11（`main` の先頭）

## WPT

`test/url/wpt-ascii.json` と `test/url/wpt-setters.json` の `_source` に、
元にした `web-platform-tests/wpt` の commit を書いてある。

* `wpt-ascii.json` — `url/resources/urltestdata.json` から、
  input と base が ASCII だけの case を抜いたもの。
* `wpt-setters.json` — `url/resources/setters_tests.json` から、
  入力も期待値も ASCII だけの case を抜いたもの。

更新するときは `url-model --wpt` と `url-model --setters` を通してから上げる。
