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
| §4.4 basic URL parser | `run`, `step`, `basicUrlParse`, `parseUrl` | `Url/Parser.lean` |
| §4.7 origin | `origin`, `originSerializer`, `Origin` | `Url/Parser.lean`, `Url/Record.lean` |
| §5.1 urlencoded parser、§5.2 serializer | `parseUrlencoded`, `serializeUrlencoded` | `Url/Urlencoded.lean` |
| §5 の往復 | `parse_serialize` | `Url/UrlencodedRoundtrip.lean` |
| §4.4 state override | `SOverride`, `basicUrlParseOverride` | `Url/Parser.lean` |
| §6.1 `URL` の getter と setter | `Url.href` ほか、`Url.setProtocol` ほか | `Url/Api.lean` |
| §4.4 parser が `ValidUrl` を保つこと | `PInv`, `basicUrlParse_valid` | `Url/Invariant.lean` |
| §4.4 state machine の 1 歩 | `step_X_valid`（state ごと 20 個）, `step_valid`, `run_valid` | `Url/StepValid.lean` |
| §6.2 `URLSearchParams` | `Params.get` ほか、`Params.sort` | `Url/SearchParams.lean` |
| UTF-16 の code unit と code unit 順 | `Infra.codeUnits`, `Infra.strLt` | `Infra/Utf16.lean` |
| UTF-8 の往復 | `Infra.utf8Decode_encode` | `Infra/Utf8Roundtrip.lean` |
| RFC 3492 Punycode | `Punycode.encode`, `Punycode.decode` | `Url/Punycode.lean` |

## state override をどう通したか

`Location` と `URL` の setter は、basic URL parser に
「この URL record から始めて、この state から読んで、成分が一つ決まったら返す」
と指示する。state を引数で渡すところは元から `run` がそうなっているので、
足したのは `PCtx.over`（override が与えられているか、`host` か `hostname` か）だけである。

仕様の分岐は三種類に分かれる。

* **override があるときだけ返る。** host / port / file host / path start が
  成分を書いた直後に `.ok` を返す。
* **override があるときだけ拒む。** scheme start state は no scheme state へ落ちず失敗し、
  scheme state は "start over" せず失敗する。
  protocol setter が URL の形を壊す四つの場合（`schemeOverride`）もここ。
* **override があるとき区切りとして読まない。** path state の `?` と `#`、
  query state の `#` は、override 付きでは percent-encode されて成分の中に入る。

### 失敗しても書き換えは残る

これが一番はまりやすかった。仕様の setter は URL record を **その場で書き換える**ので、
parse が途中で失敗しても、そこまでの書き換えは残る。setter は
basic URL parser の返り値を見ないからである。

`u.host = "example.com:65536"` がその例で、host state が host を書き換えてから
port state へ渡り、port が範囲外で失敗する。結果は
**host だけが `example.com` に変わり、port は元のまま**になる。
`url.host` に `example.net` を期待して WPT で落ちた。

`Url/Parser.lean` の `fail` が、override があるときの「return failure」を
「そこまでの record を返す」に読み替えている。

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

### Punycode は入れた

UTS #46 のうち **Unicode の表を使わない部分は Punycode だけ**で、そこは入れてある
（`Url/Punycode.lean`）。RFC 3492 の bootstring で、fuel を使わずに停止性が言える形にした。

| ループ | 測度 |
| --- | --- |
| `adaptLoop` | `delta` が 35 で割られて減る |
| `encodeDigits` | 閾値 `t` が 1 以上なので `(q - t) / (36 - t) < q` |
| `encodeLoop` | 残りの code point の個数が減る |
| `decodeDigits` / `decodeLoop` | 残りの入力が減る |

`encode_ascii`（出力は ASCII だけからなる）を証明した。
RFC 3492 §7.1 の sample strings 19 件を、符号化と復号の両方で通している
（`url-model --punycode`、38 件）。復号は RFC の綴りをそのまま食わせるので、
§5 の case annotation（(I) の Russian に大文字が混じる）を受けることの検査にもなっている。

**`decode (encode s) = s` を証明した。**

```lean
theorem decode_encode (input : List Char) : decode (encode input) = some input
```

三層に分けてある。

| 層 | 定理 | 言っていること |
| --- | --- | --- |
| 枠 | `splitLastDelim_encode` | 最後の区切りでの分割が符号化の置いたとおりに戻る |
| 可変長整数 | `decodeDigits_encodeDigits` | 桁列を読むと元の差分が出る |
| ループ | `decode_scan`, `decode_outer` | 差分の列と挿入の列が一対一に対応する |

**枠。** 桁文字は `a`-`z` と `0`-`9` だけなので区切りより後ろに `-` は現れず、
基本部分に `-` が何個あっても分け方は一意である。

**可変長整数。** 符号化は差分を閾値 `t` と `36 - t` で割り、復号は重みを `36 - t` 倍しながら
足す。`Nat.mod_add_div'` がその二つを繋ぐ。後ろに何が続いていても触らずに返すので、
上の層からそのまま呼べる。

**ループ。** ここが本体で、不変条件が二本ある。

pass の中では、入力を走査済みとこれからに割ると復号の文字列が `A ++ B` の形になり、

```
A.length + (m - n) * N = i + delta        N = A.length + B.length + 1
```

が保たれる。`n` は復号がいま見ている code point で、pass の最初の吐き出しで `m` まで跳ぶ。
跳びが残っている段階と消えた段階を同じ式で書けるのが要点である。

**`B` を落とすことはできない。** `m` 未満の文字が来ると挿入位置は進むのに文字列は伸びないので、
「位置が長さを超えない」が単独では偽である。その文字が既に `B` にいること
（前の pass で挿さっているから）が効いている。

pass の境目では

```
i + delta = (nEnc - nDec) * (out.length + 1)
```

が保たれる。`nEnc` は `encodeLoop` の引数（前の code point + 1、最初は 128）、
`nDec` は復号がいま見ている code point（前の code point、最初は 128）である。
最初の pass では両者が等しく右辺は 0、二回目以降は 1 ずれて右辺は `out.length + 1` になる。
前の pass の最後の挿入位置を `pos`、その後ろに残る文字数を `k` とすると、復号の `i` は
`pos + 1`、符号化の `delta` は `k + 1`（pass の終わりに 1 足すため）、
`out.length = pos + 1 + k` で両辺が一致する。

外側の帰納法は「復号の文字列は入力を `nEnc` 未満で filter したもの」を担いで回す。
`todo` を使い切ると filter が入力そのものになり、`decodeLoop` が `some input` を返す。
終状態を式で書かずに済む。

### 表は証明の外に置く

`domain parser` は Unicode の ToASCII（UTS #46）に委ねている。
UTS #46 の残りは表に依存する。`IdnaMappingTable.txt` が 9,262 項目、
NFC の正準分解と結合クラスが約 4,500 項目、Joining_Type が 542、Bidi_Class が約 600 で、
合わせて 15,000 項目ほどになる。これを Lean の項として埋め込むと

* ビルド時間が現実的でなくなる（いま一番重い証明が 119 case で 37 秒である）
* Unicode の版ごとに書き換えが要る

表は規定データであって規則から導けるものではないので、Lean に導出させることもできない。
`native_decide` で判定する手もあるが、`Lean.ofReduceBool` が入るので axiom 監査の方針に反する。

そこで **算法は Lean に、表は実行時の fixture に** 置いた（`Url/Idna.lean`）。

境界は `IdnaTable` である。

```lean
structure IdnaTable where
  status : Char → IdnaStatus        -- valid / ignored / mapped / disallowed
  mapped : Char → List Char
  outOfModel : Char → Bool          -- 正規化・Bidi が要る code point の印

def IdnaTable.Resolved (t : IdnaTable) : Prop :=
  ∀ c, t.status c = .mapped → ∀ d ∈ t.mapped c, t.status d = .valid
```

`mapAll` / `labelToASCII` / `toASCII` は **どんな `IdnaTable` についても** 定義してあり、
性質は `Resolved` を仮定して証明する。表そのものは証明に現れない。

実行時は `tableOfRanges` が `IdnaRange` の配列（`test/url/uts46-table.json`、8,509 範囲）を
二分探索する `IdnaTable` に変える。`checkResolved` がその配列について `Resolved` を確かめ、
満たさなければ実行を止める。

この「実行時に検査する」は **証明で繋いである**。

```lean
theorem checkResolved_sound {rs : Array IdnaRange} (h : checkResolved rs = true) :
    (tableOfRanges rs).Resolved
```

足場は `findRange_mem`（二分探索が返す区間は配列の要素である）と
`toNat_ofNat_of_valid`（妥当な scalar value なら番号から `Char` を作って戻すと同じ番号）で、
`checkResolved` は写像先が妥当な scalar value であることも見る。
これが無いと「仮定は実行時検査で落ちる」という主張が文書の上だけのものになる。

`outOfModel` の印が付いた code point を含む domain では `toASCII` が `none` を返す。
正規化（NFC）と Bidi 検査をこの model が持たないためで、
「持っていない規則を持っているふりをしない」ようにしてある。

### ASCII だけの domain には UTS #46 を掛けない

URL Standard の domain parser は step 2 でこう決めている。

> If domain is an ASCII string, then set result to domain, lowercased.
>
> When beStrict is false and domain is an ASCII string, the algorithm returns
> domain lowercased **regardless of Unicode ToASCII's outcome**, due to web
> compatibility. IgnoreInvalidPunycode is not sufficient on its own, as Punycode
> can decode successfully yet still fail validity criteria. E.g., `xn--8i7caa`
> decodes to `ｗｗｗ`, whose code points have status "mapped".

つまり `http://xn--a/` も `http://xn--8i7caa/` も `http://xn--0.pt/` も成功する。
`toASCII` はこの近道を最初に持っていて、そこは `asciiDomainToASCII` に委ねる。
表を渡したときと渡さないときで ASCII の domain の扱いが変わらないことが、これで形から出る。

UTS #46 の Processing を通るのは **非 ASCII を含む domain だけ**である。
そこでは復号した A-label が §4.1 の validity criteria を満たす必要がある
（どの code point も status が `valid`。`mapped` や `ignored` や `disallowed` では駄目）。
`http://xn--a.日本/` は `xn--a` が U+0080（disallowed）に復号されるので失敗する。

WPT の機械可読の表には `xn--` が失敗する case が一件も無く、この経路が試されない。
`test/url/uts46-alabel.json` に両側の case を置いてある。

仕様自身が別仕様へ委譲していること、この model の他の hook
（custom element の steps、MutationObserver の callback、NodeFilter の callback）と
同じ扱いであることから、`hostParser` と basic URL parser は
**ToASCII を引数で受け取る**（`PCtx.toAscii`）。既定は `asciiDomainToASCII` で、
ASCII だけの domain は model 内で閉じる（UTS #46 の写像は ASCII では ASCII lowercase に
一致し、Punycode も走らない）。表を渡したときだけ非 ASCII の domain が通る。

`ValidUrl` の保存（119 case）は `toAscii` について一般に証明してある。
`ValidUrl` は host の中身に条件を置かないので、hook を差し替えても保存は変わらない。

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
| `urlencodedEncode_no_separator` | serialize した成分に `&` も `=` も現れない。parser が区切れる根拠 |
| `percentEncodeByte_alnum`, `hexDigitChar_alnum` | `%XX` は `%` と 16 進の数字からなる |
| `setUsername_cannot`, `setPassword_cannot`, `setPort_cannot` | credentials を置けない URL では、その setter は何もしない |
| `setHost_opaque`, `setHostname_opaque`, `setPathname_opaque` | opaque path を持つ URL では、その setter は何もしない |
| `not_opaque_of_canHaveCredentials` | credentials を置ける URL は host を持ち、opaque path でない |
| `setUsername_valid`, `setPassword_valid`, `setPort_empty_valid` | record の中で閉じる setter は `ValidUrl` を保つ |
| `setAttr_valid` | **どの IDL setter も `ValidUrl` を保つ** |
| `setProtocol_valid`, `setHost_valid`, `setHostname_valid`, `setPort_valid`, `setPathname_valid`, `setSearch_valid`, `setHash_valid` | 個々の setter |
| `run_port_valid`, `run_host_valid`, `run_fileHost_valid`, `run_scheme_valid`, `run_path_valid` ほか | override 付きの各 state が `ValidUrl` を保つ |
| `schemeOverride_valid` | protocol setter の四つの guard が record の形を守る |
| `shortenPath_spec`, `appendSegment_spec`, `appendOpaque_spec` | path をいじる三つは path 以外を変えず、path の種類も変えない |
| `portDone_spec` | port state の終わりは port 以外の成分を変えない |
| `userinfoFold_spec` | authority state の振り分けは username / password 以外を変えない |
| `PInv_empty`, `PInv.valid`, `valid_of_inv` | 不変条件の入口と出口 |
| `step_X_valid`（state ごと 20 個）, `step_valid`, `run_valid` | **state machine の 1 歩が `PInv` を保つ** |
| `basicUrlParse_valid`, `parseUrl_valid` | **parse が成功したら結果は `ValidUrl` を満たす** |
| `Params.getAll_sort` | **`sort` は安定である**。名前ごとに見た値の並びが変わらない |
| `Params.getAll_swap`, `Params.getAll_insert` | 上の足場。名前の違う隣どうしの入れ替えは名前ごとの並びを変えない |
| `Params.getAll_set`, `Params.getAll_delete`, `Params.getAll_append` | `set` / `delete` / `append` の効果 |
| `Params.get_eq_head`, `Params.has_eq` | `get` は `getAll` の先頭、`has` は `getAll` が空でないこと |
| `Params.length_sort` | `sort` は組を落とさない |
| `Infra.ne_of_strLt` | code unit 順で小さいなら等しくない。安定性の証明で使う |
| `Infra.utf8Decode_encodeChar` | 一文字を UTF-8 で符号化して読み直すと元に戻る |
| `Infra.utf8Decode_encode`, `Infra.utf8DecodeString_encode` | **文字列でも同じ** |
| `Infra.lor_add`, `lor_low`, `lor3`, `lor4` | 上位を空けた値への `\|\|\|` は足し算。UTF-8 の byte はすべてその形 |
| `Infra.charOfScalar_toNat` | `Char` の番号から作り直すと元に戻る |
| `parse_serialize` | **§5 の往復。** serialize して parse すると元に戻る |
| `decodeComponent` | 成分の往復。serialize した成分を読み戻すと元の文字列に戻る |
| `splitAmp_intercalate`, `splitFirstEq_append` | `&` と最初の `=` での分割は連結の逆である |
| `percentDecode_encodeByte`, `percentDecode_encodeBytes` | percent-encode した byte は読み戻せる |
| `decode_encodeChar` | serialize した一文字ぶんを読み戻すとその文字の UTF-8 になる |

`ipv4Parser_lt` を書いていて off-by-one を拾った。畳み込んだ値に掛けるのは
`256^(4−size)` ではなく `256^(5−size)` である。仕様の counter が
「最後の part を除いた後」に 0 から始まるためで、
差分テストでは 4 part の場合しか通らないので気づきにくい。

## 検証

`lake exe url-model --wpt test/url/wpt-ascii.json` が WPT の `urltestdata.json`
（ASCII だけの 820 件）を通す。

```
WPT: 一致 816 / 不一致 0 / 対象外 4
```

残る 4 件は percent-encode された非 ASCII host で UTS #46 の表が要るものである。
表を渡すとこの 4 件も対象に入る。

```
$ lake exe url-model --wpt test/url/wpt-ascii.json test/url/uts46-table.json
UTS #46 の表: 8509 範囲、Resolved を満たす
WPT: 一致 820 / 不一致 0 / 対象外 0
ValidUrl: 違反 0
origin: 一致 376 / 不一致 0
```

`Resolved` は `IdnaTable` の仮定（`mapAll_valid` などが使う）で、
それを満たすことを読み込み時に確かめてから使う。満たさなければ実行を止める。

**対象外かどうかは fixture の `out_of_model` が決める。実行結果から推測しない。**
以前は「不一致 かつ 非 ASCII を含む かつ model が失敗した」を対象外に分類していたが、
それだと host 以外（path・query）に非 ASCII を含む case が将来失敗するようになったとき、
退行が対象外に吸収されて気づけない。

印が古くなること（対象外としたのに一致するようになる）も検出する。
その場合は「対象外の印が古い」として報告し、終了コードを 1 にする。

origin（§4.7）も同じ表が期待値を持っている。

```
origin: 一致 373 / 不一致 0
```

`application/x-www-form-urlencoded`（§5）は WPT 側が JS のテストなので
機械可読の表が無い。仕様の記述とその例から固定 case を作り、
parse と「serialize してから読み直す」の両方を通している。

```
urlencoded: 一致 26 / 不一致 0
```

setter（§6.1）も WPT が `setters_tests.json` で表を配っている。
`lake exe url-model --setters test/url/wpt-setters.json` が、
ASCII だけの 258 件について「この URL のこの属性にこの値を入れると各属性がこうなる」を確かめる。

```
setters: 一致 699 / 不一致 0 / 対象外 6
ValidUrl（setter 後）: 違反 0
```

対象外の 6 件（2 case × 3 属性）は host / hostname に `a%C2%ADb` を入れるもので、
UTS #46 が soft hyphen を落とすことを期待している。こちらも `out_of_model` で明示する。
表を渡すとこの 6 件も通る。setter も同じ hook を受け取るようにしてある。

```
$ lake exe url-model --setters test/url/wpt-setters.json test/url/uts46-table.json
setters: 一致 705 / 不一致 0 / 対象外 0
ValidUrl（setter 後）: 違反 0
```

`URLSearchParams`（§6.2）は、`sort` だけ WPT が
`urlsearchparams-sort.any.js` に配列リテラルで期待値を持っている。
残りの操作は仕様の記述とその例から固定 case を作った。

```
searchparams: 一致 26 / 不一致 0
```

`sort` は **code point 順ではなく UTF-16 code unit 順**である。
BMP の外の code point は surrogate pair になるので、U+E000 以上の BMP 文字より前に来る。
WPT の `ﬃ&🌈` がこれを見分ける case で、code point 順に実装すると落ちる。

IPv4（10 件）、IPv6（15 件）、host（15 件）は Dommy の実装とも突き合わせた。
host の 2 件が IDNA の境界で、それ以外は一致した。

## WPT が見つけた仕様の読み違い

1. **"start over" は scheme state 限定。** 最初は「どこで失敗しても先頭からやり直す」に
   していたので、`http://[]` が base に対する相対 URL になっていた（本来は失敗）。
2. **scheme state では EOF も「alphanumeric でも `:` でもない」に当たる。**
   これを失敗にしていたので、`test` のような素の相対参照が全部失敗していた。
3. **state override 付きの失敗は、そこまでの書き換えを消さない。**
   上の「失敗しても書き換えは残る」節のとおり。
4. **empty host の表し方が二通りあった。** `opaqueHostParser` が空の入力に
   `.opaque ""` を返していたので、`.empty` を名指しで見る
   `cannotHaveCredentials` が `sc:///` で false になり、
   `sc:///` に username が付いてしまった。`opaqueHostParser` の側で `.empty` に正規化した。

## `ValidUrl` の保存

parse が成功したときの URL record が `ValidUrl` を満たすことを証明した
（`basicUrlParse_valid`、`parseUrl_valid`）。`checkValidUrl` を WPT の全 case で
走らせていたものが、これで証明に上がった。実行時の検査は交差検証として残してある。

`ValidUrl` が §4.1 の何を含み何を含まないかは「`ValidUrl` の範囲」に書いてある。

### setter の側

**どの IDL setter も `ValidUrl` を保つ**（`setAttr_valid`）。

state machine 全体の帰納法（`run_valid`）は使っていない。
`run_valid` の `PInv` は `over = none` を要求しているので、override に広げると
その 119 case をやり直すことになる。代わりに、**override 付きだと各 state から
行ける先が非常に狭い**ことを使う。

| 入口 | 行ける state |
| --- | --- |
| `.port` | 自分自身だけ（override では必ず返る） |
| `.fileHost` | 自分自身だけ |
| `.host` | 自分、`.fileHost`、`.port` |
| `.schemeStart` | `.scheme` だけ（そこで返る） |
| `.pathStart` | `.path` だけ |
| `.query` / `.fragment` | 自分自身だけ |

どれも入力の長さについての短い帰納法で閉じる。state をまたぐところ
（`.host` → `.port` など）は別の定理を呼ぶだけなので、相互再帰にならない。

setter 側の guard が要る条件を渡す。`host` / `hostname` / `pathname` は
path が opaque でないこと、`port` は host が決まっていることで、
どちらも setter が先に確かめている。

### `ValidUrl` 単独では帰納的でない

`ValidUrl` をそのまま「parse の途中でも成り立つ」としても帰納法は回らない。
`PInv` は破れるところを state で添字づけて緩めたものである。

* **authority state は host が決まる前に credentials を書く。**
  `http://user@host/` の `@` を見た時点で username に `user` が入るが host はまだ null。
  `mayCred` が true の state（authority と host）だけこれを許す。
* **`specialHasList` が保たれる理由が state に依る。**
  scheme state が `scheme := buffer` と書く瞬間、path が opaque だったら
  新しい scheme が special のときに破れる。実際には破れないが、その根拠は
  「opaque path を作るのは scheme state の一分岐だけで、そこから戻る道が無い」
  という state についての事実である。`mayOpaque` が true の三つ
  （opaquePath / query / fragment）だけ opaque path を許す。

証明を書いていて、さらに三つ要ることが分かった。

* **port state に入るのは host が決まった後だけ**（`portHost`）。
  これが無いと `nullHostNoPort` が帰納的にならない。
* **scheme state までは host が決まっていない**（`schemeNoHost`）。
  opaque path をそこで作るとき `opaqueNoHost` を出すのに要る。
* **host を決める前の state には credentials も port も無い**（`freshState`）。
  base から一部の成分だけ写す state（no scheme / file / file slash）が、
  写さない成分について `ValidUrl` を出すのに要る。

### 帰納段の回し方

`run.induct` は 113 の case に分かれる。自動化は三段。

1. url を変えない遷移と、失敗・即 `ok` の終端。
2. `isSpecial` / `hasOpaquePath` / `includesCredentials` を開いて判定するもの。
3. 遷移ごとの移送補題（`portStep`、`fileBasePath`、`fileSlashDrive`、`pathStepUrl` ほか）。

詰まったところは二つあった。

* **`rw [step]` が通らない case がある。** 等式 lemma で畳めないものがあり、
  `rw` は「equation theorems で書き換えられない」と言って失敗する。
  `simp only [step.eq_def]` へ落とす経路を用意した。これを入れるまで残り 51 だったものが
  22 まで落ちた。
* **record 更新をまたぐと simp が噛まない。** `Url.hasOpaquePath` を
  `Path.isOpaque` 経由にして正規形を揃え、path をいじる操作
  （`shortenPath` / `appendSegment` / `pathStepUrl` / `fileBasePath` / `fileSlashDrive`）を
  名前のある定義に切り出して成分保存の補題を付けた。

この証明の elaborate は、state ごとに割った後で 37 秒である（`Url/StepValid.lean`）。

## `ValidUrl` に足した条件

setter の保存を書こうとして、`ValidUrl` に一つ足りないことが分かった。

> opaque path を持つなら host は null。

仕様は §4.1 にこれを並べていないが、成り立つ。opaque path を作るのは
scheme state の一分岐だけで、そこでは host はまだ null、
そこから先（opaque path / query / fragment）に host を書く state が無いためである。

これが無いと `username` setter の保存に反例が立つ。
「opaque path かつ host が非空」という record は `ValidUrl` を満たしてしまい、
そこに username を入れると `opaqueNoCredentials` が壊れる。
parse では作れない record だが、`ValidUrl` がそれを言っていなかった。

足した条件は WPT の 816 件の parse と 258 件の setter 適用のすべてで
実行時に検査していて、違反はない。

## `run_valid` を state ごとに割った

`run_valid` は `run.induct` の 119 case を**一つの宣言**で閉じていた。
宣言が一つなので 1 コアしか使えず、147 秒が丸ごと直列だった。
state ごとの独立した定理に割ったところ、Lean が並列に elaborate するようになった。

| | 時間 | CPU |
| --- | --- | --- |
| 一つの宣言（`Url/Invariant.lean`） | 147s | 101% |
| state ごと 20 定理（`Url/StepValid.lean`） | **37s** | **811%** |

URL library 全体でも素から 42 秒（CPU 769%）である。

`Url/Invariant.lean` には `PInv` とその足場だけが残り、0.36 秒で終わる。
証明の中身（simp のやり方）は変えていない。変えたのは帰納法の回し方だけである。

### 測度は一つの自然数に潰せない

`run` / `step` の `termination_by` は `(stateRank st, input.length)` の辞書式である。
長さを先にすれば一つの自然数に潰せそうに見えるが、**できない**。
authority state が「pointer を buffer の長さだけ戻す」（§4.4 authority state の最後）ので、
そこでは入力が伸びる。rank が先に減るから停止するのであって、長さは減らない。

そこで rank について強い帰納法を回し、その中で長さについて強い帰納法を回している。

```lean
def RunIH (base : Option Url) (r n : Nat) : Prop :=
  ∀ (st : PState) (input : List Char) (ctx : PCtx) (u : Url),
    run base st input ctx = .ok u →
    (stateRank st < r ∨ (stateRank st = r ∧ input.length < n)) →
    PInv base st ctx → ValidUrl u
```

等式を先に置くのが要点で、`refine ih _ _ _ u heq ?_ ?_` の `_` がそこから決まる。

### `PInv` の成分は文脈に置く

`have ⟨hov, hbv, ...⟩ := hinv` の一行で出す。simp に lemma として渡すのでは足りない。
条件付き書き換えになってしまい、`mayCred st = false` から
「credentials を持てない」という否定側の帰結を引き出せない。

### 残っている粗さ

`step_X_valid` は 20 個とも同じ tactic（`repeat' split at heq` のあと汎用の closer）で
閉じている。どの case がどの枝で閉じるかは相変わらず探索である。
ただし探索の単位が state ごとに小さくなったので、
`Url/Invariant.lean` でやっていた case 番号の直書きは要らなくなった。

## 未着手

* **UTS #46 の写像表・NFC・Bidi。** 規定データなので `IdnaTable` の仮定に押し込み、
  実行時の fixture から与える。`Resolved` は `checkResolved` が実行時に検査する。
  `outOfModel` の印が付いた code point（結合クラス ≠ 0、NFC_QC ≠ Yes、
  Bidi_Class ∈ {R, AL, AN}、Hangul、deviation）を含む domain は `none` を返す。
* **encoding override。** HTML 由来の legacy 引数。UTF-8 に固定している。
  34 の索引に 91,504 項目あり、UTS #46 の表と同じ理由で入れていない。
  影響するのは query の符号化だけで、WPT の機械可読の表には `encoding` 欄が無い。
