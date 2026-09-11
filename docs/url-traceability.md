# URL Standard のトレーサビリティ

WHATWG URL Standard の algorithm と、model の定義・定理・test の対応表。
書式は `docs/traceability.md`（DOM 側）に合わせてある。

## 読み方

* **Evaluator** — その algorithm を写した Lean の定義。
* **Contracts** — その algorithm について証明したこと。
* **Test** — 期待結果の根拠。`wpt` は `test/url/wpt-ascii.json` の中の case、
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
| URL record と不変条件 | §4.1 | `Url`, `Path`, `checkValidUrl` | `checkValidUrl_iff`（決定可能性）。parser が保つことの証明は未着手で、WPT 全件で実行時検査している | wpt | 部分 |
| special scheme と既定の port | §4.2 | `isSpecialScheme`, `defaultPort` | `isSpecialScheme_of_defaultPort` | wpt | 済 |
| URL path serializer | §4.3 | `pathSerializer` | — | wpt | 済 |
| URL serializer | §4.3 1-7 | `urlSerializer` | — | wpt | 済 |
| basic URL parser（全 state） | §4.4 1-3 | `run`, `step`, `basicUrlParse` | 停止性（`termination_by (stateRank st, 残りの文字数, 位相)`） | wpt | 済（state override を除く） |
| shorten a URL's path / single-dot / double-dot / Windows drive letter | §4.4 | `shortenPath`, `isSingleDot`, `isDoubleDot`, `isWindowsDrive` ほか | — | wpt | 済 |

## 未対応と対象外

| 項目 | 扱い | 根拠 |
| --- | --- | --- |
| IDNA / UTS #46（domain parser ToASCII） | 対象外 | 数千 code point の写像表 + Punycode + 正規化 + bidi 検査。仕様自身が別仕様へ委譲している。`hostParser` の引数として外から与える |
| state override | 対象外 | `Location` と `URL` の setter 専用の引数。setter を入れるときに一緒に扱う |
| encoding override | 対象外 | HTML 由来の legacy 引数。UTF-8 に固定している |
| `URLSearchParams` | 未着手 | application/x-www-form-urlencoded の parse / serialize |
| validation error | 対象外 | 仕様の validation error は parse の成否を変えない。`ipv4NumberParser` だけ、10 進でなかったことを boolean で返す |
| origin | 未着手 | §4.7 |
| `URLPattern` | 未着手 | 別仕様 |

## 仕様改訂時の手順

1. `docs/url-spec-version.md` の commit から新しい commit までの `url.bs` の差分を取る。
2. 差分に現れた algorithm 名でこの表を検索し、その行を review する。
3. step 要約が変わっていれば要約を直し、意味が変わっていれば evaluator と契約を直す。
4. WPT の `urltestdata.json` を取り直し、`url-model --wpt` を通す。
5. `docs/url-spec-version.md` を進める。
