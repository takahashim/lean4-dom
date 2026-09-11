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

## Unicode / UTS #46

* `test/url/uts46-table.json` — Unicode 17.0.0 の `IdnaMappingTable.txt` を
  範囲の配列に畳んだもの（8,509 範囲）。
  `UseSTD3ASCIIRules=false` / `Transitional_Processing=false` で読んである。
* 各範囲は `[lo, hi, status, out_of_model]` と、`mapped` のときの写像先。
  `out_of_model` は canonical combining class ≠ 0、NFC_Quick_Check ≠ Yes、
  Bidi_Class ∈ {R, AL, AN}、Hangul、deviation の code point に付けてある。
  正規化と Bidi 検査をこの model が持たないためで、印の付いた code point を
  含む domain は `toASCII` が `none` を返す。
* `test/url/rfc3492-punycode.json` — RFC 3492 §7.1 の例をそのまま写したもの。

表は `test/url/generate-uts46.rb` が作る。Unicode の配布ファイル四つ
（`IdnaMappingTable.txt`、`DerivedCombiningClass.txt`、`DerivedBidiClass.txt`、
`DerivedNormalizationProps.txt`）を置いた directory を渡す。

```sh
ruby test/url/generate-uts46.rb DIR > test/url/uts46-table.json
```

Unicode の版を上げるときは四つを取り直して走らせ、
`--wpt` と `--setters` を表付きで通してから上げる。

表は証明の中には入れない。`Url/Idna.lean` の `IdnaTable` が interface で、
`checkResolved` が読み込んだ表について `IdnaTable.Resolved`
（mapped の写像先が再び mapped にならないこと）を実行時に確かめる。
`url-model --wpt FILE uts46-table.json` の形で渡す。
