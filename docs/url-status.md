# URL Standard の実装状況

WHATWG URL Standard（`docs/url-spec-version.md` の commit）の形式化。
DOM 側（`docs/status.md`）と同じ repository に置き、`Infra` ライブラリを共有する。

## なぜ同じ repository か

* **語彙を共有する。** ASCII の判定、大文字小文字、byte 列と UTF-8 は
  Infra Standard のもので、DOM も URL も同じものを使う（`Infra/`）。
* **差分の相手が同じ。** Dommy 一つで両方を突き合わせられる。
  pinned version、Bundler、CI、axiom 監査、文書の書式が 1 セットで済む。

## DOM との性質の違い

| | DOM | URL |
| --- | --- | --- |
| 状態 | 木・live object・observer を持つ | 無い。文字列から record への純関数 |
| 中心の定理 | 操作列に沿った invariant の保存 | parser の停止性と、結果の record の妥当性 |
| 期待値 | 固定 scenario を自分で書く | **WPT が機械可読の表で配っている** |
| 難所 | invariant を全 algorithm で閉じること | state machine の停止性、byte 層、IDNA |

三つ目が大きい。`urltestdata.json` は 893 件の
`(input, base, 期待される各成分)` の表で、そのまま固定 scenario になる。
roadmap §12 が言う「第三の根拠」が最初から手に入る。

## 実装したもの

| 仕様 | 定義 | module |
| --- | --- | --- |
| §1.3 code point の判定、ASCII lowercase / uppercase | `Infra.isAscii*`, `asciiLowercase`, `asciiUppercase` | `Infra/Ascii.lean` |
| byte 列、UTF-8 encode / decode | `Infra.Bytes`, `utf8Encode`, `utf8Decode` | `Infra/Bytes.lean` |
| §1.3 percent-encode set と percent-encode / decode | `c0ControlSet` ほか、`utf8PercentEncode`, `percentDecodeBytes` | `Url/Percent.lean` |
| §3.3 IPv4 number parser / IPv4 parser / ends in a number / serializer | `ipv4NumberParser`, `ipv4Parser`, `endsInANumber`, `ipv4Serializer` | `Url/Ipv4.lean` |
| §3.3 IPv6 parser、§3.5 IPv6 serializer | `ipv6Parser`, `ipv6Serializer`, `ipv6CompressIndex` | `Url/Ipv6.lean` |
| §3.2 host parser / opaque-host parser / domain parser | `hostParser`, `opaqueHostParser`, `asciiDomainToASCII` | `Url/Host.lean` |
| §4.1 URL record、§4.2 special scheme、§4.3 serializer | `Url`, `Path`, `isSpecialScheme`, `urlSerializer` | `Url/Record.lean` |
| §4.4 basic URL parser | `run`, `basicUrlParse`, `parseUrl` | `Url/Parser.lean` |

## pointer を持たない書き方

仕様は入力上の pointer を進める state machine で、いくつかの state が pointer を戻す。
戻り方は二通りしかない。

* **1 つ戻す**（`decrease pointer by 1`）。「この文字を次の state で読み直す」なので、
  次の state に `c :: rest` を渡せばよい。
* **buffer のぶん戻す**（authority state と host state）。
  buffer に溜めた文字はまだ確定していない入力そのものなので、`buffer ++ input` を渡せばよい。

本当に入力が先頭へ戻るのは scheme state の "start over" だけで、これは高々一度しか起きない
（やり直した先は no scheme state で、そこから scheme start state へ戻る道は無い）。
`PResult.startOver` として再帰の外へ返し、入口で一度だけ処理する。

## 停止性

`stateRank`（`Url/Parser.lean`）が示すとおり、どの遷移も

* state の順位を下げるか、
* 順位を変えずに入力を 1 つ消費する

かのどちらかである。入力を消費しない遷移は必ず順位を下げ、
順位を変えない遷移（buffer に 1 文字積む自己ループ）は必ず入力を 1 つ消費する。
したがって `(stateRank st, 残りの入力長)` の辞書式順序が減る。

測度は `(stateRank st, 残りの文字数, 位相)` の辞書式で、**fuel は使っていない**。

位相が要るのは、入力の先頭を取り出す `run` と本体の `step` を分けたからである。
`run` が位相 1、`step` が位相 0 で、同じ state・同じ文字数のまま
`run` から `step` へ降りるぶんを位相が引き受ける。

この形に辿り着くまでに二つ直した。

* `c`（いま読んでいる文字）と `input`（読み直すための入力）を
  `let` ではなく **`step` の引数** にした。`let` だと `match c with` が
  `c` を絞り込んでも束縛済みの `input` には伝わらず、
  `decreasing_by` が「入力が空でない」を復元できない。
* 順位を変えない自己ループ（`specialAuthorityIgnoreSlashes` と `authority`）を
  `if c == some 'x'` から `match c with | some ch => ...` に書き換えた。
  `if` の guard では `c` が絞り込まれないので、
  「残りの文字数が 1 減る」が言えない。

## IDNA の境界

`domain parser` は Unicode の ToASCII（UTS #46）に委ねている。
UTS #46 は数千 code point の写像表と Punycode と正規化と bidi/joiner の検査で、
忠実に写すには Unicode のデータを model に埋め込むことになる。
仕様自身が別仕様へ委譲していること、この model の他の hook
（custom element の steps、MutationObserver の callback、NodeFilter の callback）と
同じ扱いであることから、`hostParser` は **ToASCII を引数で受け取る**。

ASCII だけの domain は `asciiDomainToASCII` が仕様どおりに振る舞う（UTS #46 の写像は
ASCII では ASCII lowercase に一致し、Punycode も走らない）ので、そちらは model 内で閉じる。

## 証明したもの

| 定理 | 内容 |
| --- | --- |
| `ipv4Parser_lt` | IPv4 parser が返す値は 2^32 未満。part 数が 4 でなくても成り立つ |
| `foldl_base256_lt` | 256 進の畳み込みの上限 |
| `opaqueHostParser_no_forbidden` | opaque host が返るなら入力に forbidden host code point は無い |
| `asciiDomainToASCII_no_forbidden` | domain parser の結果に forbidden domain code point は無い |
| `asciiDomainToASCII_ne_empty` | domain parser の結果は空でない |
| `utf8PercentEncode_id` | set に入るものが無ければ percent-encode は何も変えない |
| （`run` / `step` の停止性） | `termination_by` で示してある。fuel は使っていない |
| `checkValidUrl_iff` | `ValidUrl` は決定可能。boolean の checker と `Prop` が一致する |

`ipv4Parser_lt` を書いていて off-by-one を拾った。畳み込んだ値に掛けるのは
`256^(4−size)` ではなく `256^(5−size)` である。仕様の counter が
「最後の part を除いた後」に 0 から始まるためで、
差分テストでは 4 part の場合しか通らないので気づきにくい。

## 検証

`lake exe url-model --wpt test/url/wpt-ascii.json` が WPT の `urltestdata.json`
（ASCII だけの 820 件）を通す。

```
WPT: 一致 816 / 不一致 0 / IDNA が要る（model の対象外） 4
```

残る 4 件は percent-encode された非 ASCII host で UTS #46 が要るもの。
**一致とは数えず、対象外として別に報告する。**

IPv4（10 件）、IPv6（15 件）、host（15 件）は Dommy の実装とも突き合わせた。
host の 2 件が IDNA の境界で、それ以外は一致した。

## WPT が見つけた仕様の読み違い

1. **"start over" は scheme state 限定。** 最初は「どこで失敗しても先頭からやり直す」に
   していたので、`http://[]` が base に対する相対 URL になっていた（本来は失敗）。
2. **scheme state では EOF も「alphanumeric でも `:` でもない」に当たる。**
   これを失敗にしていたので、`test` のような素の相対参照が全部失敗していた。

## 未着手

* **`ValidUrl` の保存。** 述語（`ValidUrl`）と決定手続き（`checkValidUrl`、
  `checkValidUrl_iff`）は入れて、**WPT の全 case で実行時に検査している**
  （`url-model --wpt` の `ValidUrl: 違反 0`）。DOM 側の `dom-model --check` と同じ形である。

  証明はまだ。`step.induct`（functional induction）で 50 ほどの case に分かれる。
  難所は、途中の状態では成り立たない条件があることである。
  authority state は host が決まる前に credentials を入れるので、
  「host が null なら credentials を持たない」は host state を抜けるまで成り立たない。
  state ごとに条件を分けるか、`SpecialNotOpaque`（special なら opaque path でない）のように
  途中でも成り立つものから順に示すことになる。
  後者は opaque path を作るのが scheme state の一分岐だけなので、
  base の妥当性を仮定すれば通る見込みがある。
* **setter（state override）。** `Location` と `URL` の各 setter が使う引数。
* **`URLSearchParams`**（application/x-www-form-urlencoded）。
* **IDNA / UTS #46 そのもの。** 上記の理由で抽象化したままにする。
* **encoding override。** HTML 由来の legacy 引数。UTF-8 に固定している。
