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
* `wpt-searchparams-sort.json` — `url/urlsearchparams-sort.any.js` が持つ
  配列リテラルをそのまま取り出したもの（行末の `//` コメントだけ落としてある）。

どちらの表も、model の対象外にする case には `out_of_model` に理由を書く。
runner はこの印だけを見て対象外を決め、実行結果から推測しない。
印が古くなった（対象外としたのに一致するようになった）場合も報告する。

更新するときは `url-model --wpt` と `--setters` と `--searchparams` を通してから上げる。
