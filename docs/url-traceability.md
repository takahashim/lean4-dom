# URL Standard のトレーサビリティ

WHATWG URL Standard の algorithm と、model の定義・定理・test の対応表。
書式は `docs/traceability.md`（DOM 側）に合わせてある。

## 読み方

* **Evaluator** — その algorithm を写した Lean の定義。
* **Contracts** — その algorithm について証明したこと。
* **Test** — 期待結果の根拠。`wpt` は `test/url/wpt-ascii.json`、
  `wpt-uni` は `test/url/wpt-unicode.json`（input か base に非 ASCII を含む case。UTS #46 の表を渡して回す）、
  `wpt-set` は `test/url/wpt-setters.json`、
  `wpt-sort` は `test/url/wpt-searchparams-sort.json`、
  `rfc3492` は `test/url/rfc3492-punycode.json` の中の case、
  `dommy` は実装との突き合わせ（`test/url_diff.rb`。basic URL parser 全体を通して、
  Dommy と whatwg-url と比べる。§5.1 は `test/urlencoded_diff.rb`）。
* **Status** — 済 / 部分 / 対象外。

## §1.3 percent-encoding

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| percent-encode set（C0 control / fragment / query / special-query / path / userinfo / component） | §1.3 | `c0ControlSet` ほか | — | wpt | 済 |
| UTF-8 percent-encode | 1-2 | `utf8PercentEncode` | `utf8PercentEncode_id` | wpt | 済 |
| percent-decode（byte 列） | 1-3 | `percentDecodeBytes` | **`Spec.percentDecodeBytes_iff`（step 2 の三分岐を写した関係 `PctDecodes` にちょうど一致。`Url/Spec/Percent.lean`）**、`Spec.PctDecodes.deterministic` | wpt | 済 |
| string percent-decode | 1-2 | `stringPercentDecode` | — | wpt | 済 |

## §3.2 host

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| host parser | 1-9 | `hostParser` | **`Spec.hostParser_iff`（関係 `HostParses` にちょうど一致。percent-decode・UTF-8 decode・ends in a number・IPv4 parser・IPv6 parser をそれぞれの関係で合成。`Url/Spec/Host.lean`）** | wpt, dommy | 済（ToASCII は引数） |
| opaque-host parser | 1-4 | `opaqueHostParser` | `opaqueHostParser_no_forbidden`、`Spec.hostParser_iff` の opaque の道 | wpt, dommy | 済 |
| domain parser | 1-5 | `asciiDomainToASCII`（ASCII の近道）、`toASCII`（非 ASCII） | `asciiDomainToASCII_no_forbidden`, `asciiDomainToASCII_ne_empty`, `toASCII_no_forbidden`, `toASCII_ne_empty` | wpt, uts46-alabel, dommy | 済 |
| ToASCII（UTS #46）の算法 | UTS #46 §4（validity criteria は §4.1 の 4・6・7） | `toASCII`, `labelToASCII`, `validALabel`, `mapAll` | `toASCII_ne_empty`, `toASCII_no_forbidden`, `mapAll_valid`, `mapAll_idempotent`, `labelToASCII_ascii`, `toAsciiOk_table`（往復の条件 `ToAsciiOk` を満たす） | wpt（表を渡して 820 件）, uts46-alabel, dommy | 済（表は `IdnaTable` の仮定。criterion 6 は対象外の印より先に見る） |
| UTS #46 の写像表と General_Category=Mark | — | `tableOfRanges`（実行時 fixture、8,724 範囲） | `checkResolved_sound`（検査が通れば `Resolved`）、`checkNoUpperValid_sound`（ASCII の大文字は valid でない）、`findRange_mem` | dommy の `Internal::IDNA` | 対象外（規定データ。証明には現れない） |
| NFC 正規化・Bidi 検査・Joining_Type | — | `IdnaTable.outOfModel` の印で弾く | — | — | 対象外（印の付いた domain は `none`） |
| Punycode（RFC 3492） | RFC 3492 | `Punycode.encode`, `Punycode.decode` | **`decode_encode`（往復）**、`encode_ascii`、停止性（fuel なし） | rfc3492（19 件 × 両方向） | 済 |
| forbidden host / domain code point | §1.3 | `isForbiddenHost`, `isForbiddenDomain` | 上記 | wpt | 済 |

## §3.3 IP address

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| IPv4 number parser | 1-8 | `ipv4NumberParser` | **`Spec.ipv4NumberParser_iff`（基数の三つの場合を構成子にした関係 `Ipv4Number` に一致。`Url/Spec/Ipv4.lean`）** | wpt, dommy | 済 |
| IPv4 parser | 1-13 | `ipv4Parser`, `ipv4Parts` | `ipv4Parser_lt`、**`Spec.ipv4Parser_iff`（strict split と counter の重みで書いた関係 `Ipv4Parses` に一致）** | wpt, dommy | 済 |
| ends in a number | 1-5 | `endsInANumber` | `Spec.endsInANumber_iff`（空でない入力について関係 `EndsInNumber` に一致） | wpt, dommy | 済 |
| IPv6 parser | 1-8 | `ipv6Parser`, `ipv6Loop`, `ipv4InIpv6`, `ipv6Expand` | `ipv6Parser_length`, `ipv6Parser_lt`、**`Spec.ipv6Parser_iff`（RFC 4291 §2.2 の形の文法 `Ipv6Text` に一致。`::` は一度だけ、dotted decimal は最後に置ける。`Url/Spec/Ipv6.lean`）** | wpt, dommy | 済 |

## §3.5 serializer

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| host serializer | 1-3 | `hostSerializer` | — | wpt, dommy | 済 |
| IPv4 serializer | 1-3 | `ipv4Serializer` | `ipv4Parser_lt`（全域性の根拠） | wpt, dommy | 済 |
| IPv6 serializer | 1-4 | `ipv6Serializer` | — | wpt, dommy | 済 |
| find the IPv6 address compressed piece index | 1-5 | `ipv6CompressIndex` | **`Spec.ipv6CompressIndex_iff` / `Spec.ipv6CompressIndex_none_iff`（一番長い 0 の並びのうち最初のものの先頭。長さ 2 以上の並びが無ければ null）**。本文の例 `0:f:0:0:f:f:0:0` を `example` で固定 | wpt, dommy | 済 |

## §4 URL

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| URL record と不変条件 | §4.1 | `Url`, `Path`, `checkValidUrl`, `checkStrictUrl` | `checkValidUrl_iff` / `checkStrictUrl_iff`（決定可能性）、`basicUrlParse_valid` / `parseUrl_valid`（parse が保つ）、`basicUrlParse_strict` / `setAttr_strict`（§4.1 の残りの三条件も parse と setter が保つ） | wpt, wpt-set | 済 |
| special scheme と既定の port | §4.2 | `isSpecialScheme`, `defaultPort` | `isSpecialScheme_of_defaultPort` | wpt | 済 |
| URL path serializer | §4.3 | `pathSerializer` | — | wpt | 済 |
| URL serializer | §4.3 1-7 | `urlSerializer` | `roundtrip_canonical_of`（canonical な record は parse し直すと戻る。ToASCII は一般）、`basicUrlParse_canonical` / `parseUrl_canonical`（parse の結果は canonical）、`parse_image`（parse の像は `ValidUrl ∧ canonicalUrl`）、`parse_serialize_of_parse` | wpt | 済 |
| basic URL parser（全 state） | §4.4 1-3 | `run`, `step`, `basicUrlParse` | 停止性（`termination_by (stateRank st, 残りの文字数, 位相)`）、**`Spec.parseUrl_eq_specParseUrl`（入力にも base にも制限なく、state を持たない関数的な仕様 `specParseUrl` に一致。`Url/Spec/ParseBase.lean`）**、`Spec.basicUrlParse_eq_specParse_all`（base 無し）、`Spec.basicUrlParse_eq_specParseBase`（base あり） | wpt, spec-batch | 済 |
| state override（setter が使う入口） | §4.4 | `SOverride`, `basicUrlParseOverride`, `schemeOverride`, `fail` | — | wpt-set | 済 |
| parse の途中の不変条件 | §4.1 / §4.4 | `PInv`, `mayOpaque`, `mayCred`, `usesBasePath`, `freshHost`, `freshCredPort` | `PInv_empty`（入口）、`PInv.valid`（出口）、`run_valid`（帰納段）、`shortenPath_spec`, `portDone_spec`, `userinfoFold_spec`, `pathStepUrl_spec`（遷移の成分保存） | — | 済 |
| shorten a URL's path / single-dot / double-dot / Windows drive letter | §4.4 | `shortenPath`, `isSingleDot`, `isDoubleDot`, `isWindowsDrive` ほか | `Spec.pathStepUrl_eq_segStep`（関係の側の `shorten` と `segStep` に一致） | wpt | 済 |
| path state | §4.4 path state 1-2 | `step`（`.path`）, `pathStepUrl` | **`Spec.run_path_spec` / `_query` / `_fragment`（区切りで割って畳む関係 `resolveSegs` に一致。`Url/Spec/Path.lean`）**、`Spec.splitSegs_iff` | wpt | 済 |
| relative state / relative slash state / special relative or authority state | §4.4 | `step`（`.relative` ほか） | **`Spec.basicUrlParse_pathRef`、`Spec.basicUrlParse_absRef`、`Spec.basicUrlParse_sameScheme`（相対参照の解決。`Url/Spec/Resolve.lean`）**、`Spec.basicUrlParse_fragment` / `_query` / `_empty`（`Url/Spec/Relative.lean`） | wpt（関係の側の解決を 54 件で照合）、RFC 3986 §5.4 の 25 例と URL Standard に固有の 3 例 | 済（`file` の base は除く） |

## §4.5 URL equivalence

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| URL equals（exclude fragments 付き） | §4.5 1-3 | `Url.equals` | `equals_iff_eq` / `parseUrl_equals_iff`（parse の像の上では record の等しさと一致）、`equals_excludeFragments_iff`（fragment を除いた record の等しさと一致）、`urlSerializer_excludeFragment` | — | 済 |
| URL path equals | §4.5 1-4 | `Path.equals` | `Path.equals_iff`（record の等しさと一致）。serialize して比べてはいけない例（空の opaque path と空の列）を `example` で固定 | — | 済 |
| URL path starts with | §4.5 1-4 | `Path.startsWith` | `Path.startsWith_iff`（列の前方部分列と一致）、`startsWith_trans`, `startsWith_antisymm`、**`Path.startsWith_iff_serialize`（注記：serialize の後ろが空か `/` で始まることと同値）**。文字列の前方一致では足りない例を `example` で固定 | — | 済 |

## §4.7 origin

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| origin | §4.7 全 | `origin`（ToASCII は引数。`blob` の path を読み直す basic URL parser に渡す） | `origin_of_special`、`origin_eq_none_of_other`、**`parseUrl_origin_tuple`（parse の結果の special URL は `file` を除き必ず tuple origin を持つ）**、`origin_blob`（`blob` は読み直した URL の origin）、`origin_blob_tuple`、`origin_blob_other`、`origin_blob_failure`（`Url/OriginProps.lean`） | wpt（`origin` の欄、373 件一致。表を渡して 376 件）, uts46-alabel | 済（`blob` は blob URL entry を持たない前提） |
| origin の serialize | HTML §origin | `originSerializer` | — | 同上 | 済 |

## §5 application/x-www-form-urlencoded

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| urlencoded percent-encode set | §1.3 | `urlencodedSet` | `urlencodedEncode_no_separator` | 固定 case | 済 |
| urlencoded parser | §5.1 1-4 | `parseUrlencoded`, `parsePiece`, `splitAmp`, `splitFirstEq`, `plusToSpace` | **`parseUrlencoded_iff`（関係 `FormParses` にちょうど一致。`Url/Spec/Urlencoded.lean`）** | 固定 case（13 件） | 済（encoding は UTF-8 固定） |
| urlencoded serializer | §5.2 1-4 | `serializeUrlencoded`, `urlencodedEncode`, `intercalateChars` | `urlencodedEncode_no_separator`、`parse_serialize`（**parse との往復**） | 固定 case（往復 13 件） | 済 |

## §6.1 `URL` の IDL 属性

setter は `state override` 付きの basic URL parser を呼ぶだけなので、
契約の大半は parser 側に載る。record の中で閉じるものだけ保存を証明した。

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| getter（`href` / `protocol` / `username` / `password` / `host` / `hostname` / `port` / `pathname` / `search` / `hash`） | §6.1 | `Url.href` ほか、`Url.getAttr` | — | wpt-set | 済 |
| `protocol` setter | §6.1 1 | `Url.setProtocol`, `schemeOverride` | `setProtocol_valid`, `schemeOverride_valid`、**`Spec.setProtocol_eq`（入力に制限なく `protocolSpec` に一致）** | wpt-set（33 件） | 済 |
| `username` / `password` setter | §6.1 1-2 | `Url.setUsername`, `Url.setPassword`, `userinfoEncode` | `setUsername_cannot`, `setPassword_cannot`, `setUsername_valid`, `setPassword_valid` | wpt-set（21 件） | 済 |
| `host` / `hostname` setter | §6.1 1-2 | `Url.setHost`, `Url.setHostname` | `setHost_opaque`, `setHostname_opaque`, `setHost_valid`, `setHostname_valid`、**`Spec.setHost_eq` / `Spec.setHostname_eq`（入力に制限なく `hostSetterSpec` に一致。`Url/Spec/Setters.lean`）** | wpt-set（111 件） | 済 |
| `port` setter | §6.1 1-3 | `Url.setPort` | `setPort_cannot`, `setPort_valid`、**`Spec.setPort_eq`（`portSpec` に一致）** | wpt-set（27 件） | 済 |
| `pathname` setter | §6.1 1-3 | `Url.setPathname` | `setPathname_opaque`, `setPathname_valid`、**`Spec.setPathname_eq`（`pathnameSpec` に一致）** | wpt-set（29 件） | 済 |
| `search` setter | §6.1 1-6 | `Url.setSearch`, `dropLeading` | `setSearch_valid`（`ValidUrl` を保つ）、`setSearch_path`（path に触れない） | wpt-set（14 件）、固定 case | 済（query object の list は `URLSearchParams` 側） |
| `hash` setter | §6.1 1-4 | `Url.setHash`, `dropLeading` | `setHash_valid`（`ValidUrl` を保つ）、`setHash_path`（path に触れない） | wpt-set（22 件）、固定 case | 済 |
| `href` setter | §6.1 1-3 | `Url.setHref` | `Spec.setHref_href`（parse の結果の `href` を代入しても変わらない） | wpt-set（1 件） | 済（失敗は `none`。例外は IDL 側） |
| getter と setter の往復、setter の冪等性 | §6.1 | `Url.setProtocol` ほか、getter | **`Spec.parseUrl_lens`（parse の結果では getter の値を setter に戻すと変わらない。例外は空の fragment・空の query・host が null の list path URL）**、`Spec.setAttr_idem`（同じ値を二度入れても一度と同じ）、反例の `example`（`Url/Spec/Lens.lean`） | 証明前に約 9 万件 × 25 値で確認 | 済 |
| API URL parser | §6.1 1-3 | `apiUrlParser`（= `parseUrl`） | `apiUrlParser_base_failure`（base の失敗を伝える）、`apiUrlParser_base` | wpt | 済 |
| `URL.parse()` / `URL.canParse()` | §6.1 | `apiUrlParser`, `canParse` | `canParse_iff` | wpt | 済（`URL` object の生成は IDL 側） |
| `toJSON()` | §6.1 | `Url.toJSON` | `toJSON_eq_href` | — | 済 |
| URL cannot have a username/password/port | §4.2 | `Url.cannotHaveCredentials` | 上記 3 つの `*_cannot` | wpt-set | 済 |
| opaque path は生の U+0020 で終わらない（parser と setter から到達できる record の性質） | §4.4 opaque path state 3 | — | `parseUrl_opaqueNoTrailingSpace`、`setAttr_opaqueNoTrailingSpace` | wpt, wpt-set（`canonicalUrl` の検査） | 済 |

## §6.2 `URLSearchParams`

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| constructor（文字列から） | §6.2 1-3 | `Params.ofString` | — | 固定 case | 済（sequence / record の形は IDL 側） |
| `get` / `getAll` / `has` / `size` | §6.2 | `Params.get`, `getAll`, `has`, `hasValue`, `size` | `get_eq_head`, `has_eq` | 固定 case | 済 |
| `append` / `delete` / `set` | §6.2 | `Params.append`, `delete`, `deleteValue`, `set` | `getAll_append`, `getAll_delete`, `getAll_set` | 固定 case | 済 |
| `sort` | §6.2 1-2 | `Params.sort`, `Params.insert` | `getAll_sort` / `filter_sort`（安定性）、`length_sort`、**`sort_perm`（並べ替え）、`sort_sorted`（code unit 順）、`sort_unique`（この三つで一つに決まる）** | wpt-sort（8 件） | 済 |
| stringifier | §6.2 | `Params.serialize` | — | 固定 case | 済 |
| update a URLSearchParams object | §6.2 1-4 | `Url.withParams` | `searchParams_withParams`、`withParams_path`（path に触れない） | 固定 case | 済（object identity は持たない） |
| §6.1 `searchParams` getter | §6.1 | `Url.searchParams` | — | 固定 case | 済 |
| code unit 順の比較 | WebIDL | `Infra.codeUnits`, `Infra.strLt` | `strLt_self`, `ne_of_strLt`、`strLt_asymm`, `strLt_trans`, `strLt_total`（全順序）、`utf16Units_inj`（UTF-16 への変換は単射） | wpt-sort | 済 |

## 未対応と対象外

| 項目 | 扱い | 根拠 |
| --- | --- | --- |
| IDNA / UTS #46 の写像表・NFC・Bidi | 対象外 | 数千 code point の規定データ。規則から導けず、Lean の項として埋め込むとビルドが現実的でない。算法（`toASCII`）は Lean にあり、表は `IdnaTable` という仮定にして実行時の fixture から与える。仮定（`Resolved` と `NoUpperValid`）は `checkResolved` と `checkNoUpperValid` が実行時に検査する |
| `URL` の constructor が投げる例外 | 対象外 | `TypeError`。model は `Option` で返す |
| `Location` の setter | 対象外 | HTML 側の概念（navigate、cross-origin の検査）を含む。URL record に効く部分は `URL` の setter と同じ |
| encoding override | 対象外 | HTML 由来の legacy 引数。UTF-8 に固定している |
| `_charset` の特別扱い | 対象外 | §5.1 の注記。仕様も「conforming なのは UTF-8 だけ」としている |
| blob URL entry | 対象外 | §4.7 の `blob` の分岐。entry は HTML 側の概念なので、常に null として path を読み直す |
| validation error | 対象外 | 仕様の validation error は parse の成否を変えない。`ipv4NumberParser` だけ、10 進でなかったことを boolean で返す |
| `URLPattern` | 未着手 | 別仕様 |

## 仕様改訂時の手順

1. `docs/url-spec-version.md` の commit から新しい commit までの `url.bs` の差分を取る。
2. 差分に現れた algorithm 名でこの表を検索し、その行を review する。
3. step 要約が変わっていれば要約を直し、意味が変わっていれば evaluator と契約を直す。
4. WPT の `urltestdata.json`、`setters_tests.json`、`urlsearchparams-sort.any.js` を
   取り直し、`url-model --wpt` と `--setters` と `--searchparams` を通す。
5. `docs/url-spec-version.md` を進める。
