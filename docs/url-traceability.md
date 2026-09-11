# URL Standard のトレーサビリティ

WHATWG URL Standard の algorithm と、model の定義・定理・test の対応表。
書式は `docs/traceability.md`（DOM 側）に合わせてある。

## 読み方

* **Evaluator** — その algorithm を写した Lean の定義。
* **Contracts** — その algorithm について証明したこと。
* **Test** — 期待結果の根拠。`wpt` は `test/url/wpt-ascii.json`、
  `wpt-set` は `test/url/wpt-setters.json`、
  `wpt-sort` は `test/url/wpt-searchparams-sort.json` の中の case、
  `dommy` は Dommy の実装との突き合わせ。
* **Status** — 済 / 部分 / 対象外。

## §1.3 percent-encoding

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| percent-encode set（C0 control / fragment / query / special-query / path / userinfo / component） | §1.3 | `c0ControlSet` ほか | — | wpt | 済 |
| UTF-8 percent-encode | 1-2 | `utf8PercentEncode` | `utf8PercentEncode_id` | wpt | 済 |
| percent-decode（byte 列） | 1-3 | `percentDecodeBytes` | — | wpt | 済 |
| string percent-decode | 1-2 | `stringPercentDecode` | — | wpt | 済 |

## §3.2 host

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| host parser | 1-9 | `hostParser` | — | wpt, dommy | 済（ToASCII は引数） |
| opaque-host parser | 1-4 | `opaqueHostParser` | `opaqueHostParser_no_forbidden` | wpt, dommy | 済 |
| domain parser | 1-5 | `asciiDomainToASCII` | `asciiDomainToASCII_no_forbidden`, `asciiDomainToASCII_ne_empty` | wpt, dommy | 部分（ASCII の domain のみ） |
| domain parser ToASCII（UTS #46） | — | 引数として受け取る | — | dommy の `Internal::IDNA` | 対象外 |
| forbidden host / domain code point | §1.3 | `isForbiddenHost`, `isForbiddenDomain` | 上記 | wpt | 済 |

## §3.3 IP address

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| IPv4 number parser | 1-8 | `ipv4NumberParser` | — | wpt, dommy | 済 |
| IPv4 parser | 1-13 | `ipv4Parser`, `ipv4Parts` | `ipv4Parser_lt` | wpt, dommy | 済 |
| ends in a number | 1-5 | `endsInANumber` | — | wpt, dommy | 済 |
| IPv6 parser | 1-8 | `ipv6Parser`, `ipv6Loop`, `ipv4InIpv6`, `ipv6Expand` | — | wpt, dommy | 済 |

## §3.5 serializer

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| host serializer | 1-3 | `hostSerializer` | — | wpt, dommy | 済 |
| IPv4 serializer | 1-3 | `ipv4Serializer` | `ipv4Parser_lt`（全域性の根拠） | wpt, dommy | 済 |
| IPv6 serializer | 1-4 | `ipv6Serializer` | — | wpt, dommy | 済 |
| find the IPv6 address compressed piece index | 1-5 | `ipv6CompressIndex` | — | wpt, dommy | 済 |

## §4 URL

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| URL record と不変条件 | §4.1 | `Url`, `Path`, `checkValidUrl` | `checkValidUrl_iff`（決定可能性）、`basicUrlParse_valid` / `parseUrl_valid`（parse が保つ） | wpt, wpt-set | 済 |
| special scheme と既定の port | §4.2 | `isSpecialScheme`, `defaultPort` | `isSpecialScheme_of_defaultPort` | wpt | 済 |
| URL path serializer | §4.3 | `pathSerializer` | — | wpt | 済 |
| URL serializer | §4.3 1-7 | `urlSerializer` | — | wpt | 済 |
| basic URL parser（全 state） | §4.4 1-3 | `run`, `step`, `basicUrlParse` | 停止性（`termination_by (stateRank st, 残りの文字数, 位相)`） | wpt | 済 |
| state override（setter が使う入口） | §4.4 | `SOverride`, `basicUrlParseOverride`, `schemeOverride`, `fail` | — | wpt-set | 済 |
| parse の途中の不変条件 | §4.1 / §4.4 | `PInv`, `mayOpaque`, `mayCred`, `usesBasePath`, `freshHost`, `freshCredPort` | `PInv_empty`（入口）、`PInv.valid`（出口）、`run_valid`（帰納段）、`shortenPath_spec`, `portDone_spec`, `userinfoFold_spec`, `pathStepUrl_spec`（遷移の成分保存） | — | 済 |
| shorten a URL's path / single-dot / double-dot / Windows drive letter | §4.4 | `shortenPath`, `isSingleDot`, `isDoubleDot`, `isWindowsDrive` ほか | — | wpt | 済 |

## §4.7 origin

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| origin | §4.7 全 | `origin` | — | wpt（`origin` の欄、373 件一致） | 済（`blob` は blob URL entry を持たない前提） |
| origin の serialize | HTML §origin | `originSerializer` | — | 同上 | 済 |

## §5 application/x-www-form-urlencoded

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| urlencoded percent-encode set | §1.3 | `urlencodedSet` | `urlencodedEncode_no_separator` | 固定 case | 済 |
| urlencoded parser | §5.1 1-4 | `parseUrlencoded`, `splitAmp`, `splitFirstEq`, `plusToSpace` | — | 固定 case（13 件） | 済（encoding は UTF-8 固定） |
| urlencoded serializer | §5.2 1-4 | `serializeUrlencoded`, `urlencodedEncode` | `urlencodedEncode_no_separator` | 固定 case（往復 13 件） | 済 |

## §6.1 `URL` の IDL 属性

setter は `state override` 付きの basic URL parser を呼ぶだけなので、
契約の大半は parser 側に載る。record の中で閉じるものだけ保存を証明した。

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| getter（`href` / `protocol` / `username` / `password` / `host` / `hostname` / `port` / `pathname` / `search` / `hash`） | §6.1 | `Url.href` ほか、`Url.getAttr` | — | wpt-set | 済 |
| `protocol` setter | §6.1 1 | `Url.setProtocol`, `schemeOverride` | — | wpt-set（33 件） | 済 |
| `username` / `password` setter | §6.1 1-2 | `Url.setUsername`, `Url.setPassword`, `userinfoEncode` | `setUsername_cannot`, `setPassword_cannot`, `setUsername_valid`, `setPassword_valid` | wpt-set（21 件） | 済 |
| `host` / `hostname` setter | §6.1 1-2 | `Url.setHost`, `Url.setHostname` | `setHost_opaque`, `setHostname_opaque` | wpt-set（111 件） | 済 |
| `port` setter | §6.1 1-3 | `Url.setPort` | `setPort_cannot`, `setPort_empty_valid` | wpt-set（27 件） | 済 |
| `pathname` setter | §6.1 1-3 | `Url.setPathname` | `setPathname_opaque` | wpt-set（29 件） | 済 |
| `search` setter | §6.1 1-6 | `Url.setSearch`, `stripTrailingSpaces` | — | wpt-set（14 件） | 済（query object の list は `URLSearchParams` 側） |
| `hash` setter | §6.1 1-4 | `Url.setHash`, `stripTrailingSpaces` | — | wpt-set（22 件） | 済 |
| `href` setter | §6.1 1-3 | `Url.setHref` | — | wpt-set（1 件） | 済（失敗は `none`。例外は IDL 側） |
| URL cannot have a username/password/port | §4.2 | `Url.cannotHaveCredentials` | 上記 3 つの `*_cannot` | wpt-set | 済 |
| potentially strip trailing spaces from an opaque path | §6.1 1-4 | `stripTrailingSpaces` | — | wpt-set | 済 |

## §6.2 `URLSearchParams`

| Algorithm | WHATWG steps | Evaluator | Contracts | Test | Status |
| --- | --- | --- | --- | --- | --- |
| constructor（文字列から） | §6.2 1-3 | `Params.ofString` | — | 固定 case | 済（sequence / record の形は IDL 側） |
| `get` / `getAll` / `has` / `size` | §6.2 | `Params.get`, `getAll`, `has`, `hasValue`, `size` | `get_eq_head`, `has_eq` | 固定 case | 済 |
| `append` / `delete` / `set` | §6.2 | `Params.append`, `delete`, `deleteValue`, `set` | `getAll_append`, `getAll_delete`, `getAll_set` | 固定 case | 済 |
| `sort` | §6.2 1-2 | `Params.sort`, `Params.insert` | `getAll_sort`（安定性）、`length_sort` | wpt-sort（8 件） | 済 |
| stringifier | §6.2 | `Params.serialize` | — | 固定 case | 済 |
| update a URLSearchParams object | §6.2 1-5 | `Url.withParams` | — | 固定 case | 済（object identity は持たない） |
| §6.1 `searchParams` getter | §6.1 | `Url.searchParams` | — | 固定 case | 済 |
| code unit 順の比較 | WebIDL | `Infra.codeUnits`, `Infra.strLt` | `strLt_self`, `ne_of_strLt` | wpt-sort | 済 |

## 未対応と対象外

| 項目 | 扱い | 根拠 |
| --- | --- | --- |
| IDNA / UTS #46（domain parser ToASCII） | 対象外 | 数千 code point の写像表 + Punycode + 正規化 + bidi 検査。仕様自身が別仕様へ委譲している。`hostParser` の引数として外から与える |
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
