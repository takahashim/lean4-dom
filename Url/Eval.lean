import Url.Api
import Url.HostRoundtrip

/-!
# 具体的な入力で parser を評価する tactic

`run` と `step` は well-founded 再帰なので、`decide` も `rfl` も展開できない
（kernel の簡約は `WellFounded.fix` で止まる）。`native_decide` は axiom 監査の方針で使わない。

`url_eval` は等式 lemma で `run` と `step` を一段ずつ開く。入力が具体的なら
`match` はその場で潰れ、残るのは構造的な再帰だけになるので、最後を `decide` が閉じる。

UTF-8 の復号（`Infra.utf8Decode`）も well-founded 再帰なので、host parser の
percent-decode は開かずに `percentDecodeToString_ascii`（`%` の無い ASCII は変わらない）で
飛ばし、domain parser は `asciiDomainToASCII_id` で飛ばす。どちらも条件付きの書き換えで、
条件は `decide` が閉じる。したがって **`%` や非 ASCII を host に含む入力には使えない**。
-/

namespace Url

/-- 具体的な ASCII の入力について、parser と setter の結果を計算して等式を閉じる。 -/
macro "url_eval" : tactic => `(tactic|
  simp (config := { decide := true }) [basicUrlParse, basicUrlParseOverride, parseUrl,
    preprocess, stripTabNewline, run, step,
    Url.setProtocol, Url.setUsername, Url.setPassword, Url.setHost, Url.setHostname,
    Url.setPort, Url.setPathname, Url.setSearch, Url.setHash, Url.setHref,
    Url.cannotHaveCredentials, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
    SOverride.start, hostParser, Url.isSpecial, isSpecialScheme, defaultPort,
    pathStepUrl, fail, schemeOverride, Infra.asciiLowercase, portDone, portValue, portOf,
    portSet, isTerminator, opaqueHostParser, appendSegment, appendOpaque, shortenPath, queryOf,
    isSingleDot, isDoubleDot, isWindowsDrive, isNormalizedWindowsDrive, startsWithWindowsDrive,
    fileBasePath, fileSlashDrive, userinfoStep, userinfoEncode, dropLeading,
    percentDecodeToString_ascii, asciiDomainToASCII_id, endsInANumber, ipv4Parts,
    ipv4NumberParser] <;> decide)

end Url
