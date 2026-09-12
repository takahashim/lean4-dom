import Url.Parser

/-!
# `URL` の IDL 属性

WHATWG URL Standard §6.1 の `URL` class のうち、URL record だけで決まるもの。

getter は record からの射影、setter は `state override` 付きの basic URL parser で、
本体は `Url/Parser.lean` にある。`URLSearchParams` との連動
（`search` setter が query object の list を更新する）は
`Url/Urlencoded.lean` の関数で別に取れるので、ここでは record だけを扱う。

## 失敗したときに何が残るか

仕様の setter は URL record を **その場で書き換える**ので、
parse が途中で失敗しても、そこまでの書き換えは残る。setter 側は
basic URL parser の返り値を見ないので、失敗は「そこで止まる」以上の意味を持たない。

これは実際に効く。`u.host = "example.com:65536"` は host state が
host を書き換えてから port state へ渡り、port が範囲外で失敗する。
仕様どおりなら host は `example.com` に変わり、port は元のままになる
（WPT の setters_tests.json がそう要求している）。

そこで `Url/Parser.lean` の `fail` が、override が与えられているときの
「return failure」を「そこまでの record を返す」に読み替える。
ここで `.getD u` が効くのは、そもそも呼び出しの入口に届かない場合だけである。
-/

namespace Url

open Infra

/-! ## getter -/

/-- §4.2「URL cannot have a username/password/port」。 -/
def Url.cannotHaveCredentials (u : Url) : Bool :=
  u.host.isNone || u.host == some Host.empty || u.scheme == "file"

/-- §6.1 `href` getter。 -/
def Url.href (u : Url) : String := urlSerializer u

/-- §6.1 `protocol` getter。 -/
def Url.protocol (u : Url) : String := u.scheme ++ ":"

/-- §6.1 `host` getter。port があれば `host:port`。 -/
def Url.hostAttr (u : Url) : String :=
  match u.host with
  | none => ""
  | some h =>
    match u.port with
    | none => hostSerializer h
    | some p => hostSerializer h ++ ":" ++ toString p

/-- §6.1 `hostname` getter。 -/
def Url.hostname (u : Url) : String :=
  match u.host with
  | none => ""
  | some h => hostSerializer h

/-- §6.1 `port` getter。 -/
def Url.portAttr (u : Url) : String :=
  match u.port with
  | none => ""
  | some p => toString p

/-- §6.1 `pathname` getter。 -/
def Url.pathname (u : Url) : String := pathSerializer u.path

/-- §6.1 `search` getter。空の query は空文字列を返す（`?` は付かない）。 -/
def Url.search (u : Url) : String :=
  match u.query with
  | none => ""
  | some q => if q.isEmpty then "" else "?" ++ q

/-- §6.1 `hash` getter。 -/
def Url.hash (u : Url) : String :=
  match u.fragment with
  | none => ""
  | some f => if f.isEmpty then "" else "#" ++ f

/-! ## setter -/

/-- §4.4「set the username」「set the password」。userinfo set で percent-encode する。 -/
def userinfoEncode (v : String) : String :=
  String.ofList (utf8PercentEncode userinfoSet v.toList)

/--
§6.1「potentially strip trailing spaces from an opaque path」。

opaque path の末尾の空白は、query も fragment も無くなって初めて
serialize の結果に効いてくる（それまでは後ろに `?` や `#` が続くので
読み直しても同じ path に戻る）。そこで落とす。
-/
def stripTrailingSpaces (u : Url) : Url :=
  match u.path with
  | .list _ => u
  | .opaque p =>
    if u.fragment.isSome || u.query.isSome then u
    else { u with path := .opaque (String.ofList ((p.toList.reverse.dropWhile (· == ' ')).reverse)) }

/-- §6.1 `protocol` setter。 -/
def Url.setProtocol (u : Url) (v : String) : Url :=
  (basicUrlParseOverride (v ++ ":") u .scheme).getD u

/-- §6.1 `username` setter。 -/
def Url.setUsername (u : Url) (v : String) : Url :=
  if u.cannotHaveCredentials then u else { u with username := userinfoEncode v }

/-- §6.1 `password` setter。 -/
def Url.setPassword (u : Url) (v : String) : Url :=
  if u.cannotHaveCredentials then u else { u with password := userinfoEncode v }

/-- §6.1 `host` setter。 -/
def Url.setHost (u : Url) (v : String)
    (toAscii : List Char → Option String := asciiDomainToASCII) : Url :=
  if u.hasOpaquePath then u else (basicUrlParseOverride v u .host toAscii).getD u

/-- §6.1 `hostname` setter。 -/
def Url.setHostname (u : Url) (v : String)
    (toAscii : List Char → Option String := asciiDomainToASCII) : Url :=
  if u.hasOpaquePath then u else (basicUrlParseOverride v u .hostname toAscii).getD u

/-- §6.1 `port` setter。空文字列は port を消す。 -/
def Url.setPort (u : Url) (v : String) : Url :=
  if u.cannotHaveCredentials then u
  else if v.isEmpty then { u with port := none }
  else (basicUrlParseOverride v u .port).getD u

/-- §6.1 `pathname` setter。opaque path は書き換えられない。 -/
def Url.setPathname (u : Url) (v : String) : Url :=
  if u.hasOpaquePath then u
  else
    let u0 := { u with path := Path.list [] }
    (basicUrlParseOverride v u0 .path).getD u0

/-- 先頭の区切りを一つだけ落とす。 -/
def dropLeading (d : Char) (v : String) : String :=
  String.ofList (match v.toList with | c :: t => if c == d then t else v.toList | [] => [])

/-- §6.1 `search` setter。先頭の `?` は一つだけ落とす。 -/
def Url.setSearch (u : Url) (v : String) : Url :=
  if v.isEmpty then stripTrailingSpaces { u with query := none }
  else
    (basicUrlParseOverride (dropLeading '?' v) { u with query := some "" } .query).getD
      { u with query := some "" }

/-- §6.1 `hash` setter。先頭の `#` は一つだけ落とす。 -/
def Url.setHash (u : Url) (v : String) : Url :=
  if v.isEmpty then stripTrailingSpaces { u with fragment := none }
  else
    (basicUrlParseOverride (dropLeading '#' v) { u with fragment := some "" } .fragment).getD
      { u with fragment := some "" }

/-- §6.1 `href` setter。base なしで parse し直す。失敗は例外（ここでは `none`）。 -/
def Url.setHref (v : String) (toAscii : List Char → Option String := asciiDomainToASCII) :
    Option Url := basicUrlParse v none toAscii

/-! ## 名前で引く -/

/-- getter を属性名で引く。差分 test の期待値表が名前で書いてあるため。 -/
def Url.getAttr (u : Url) : String → Option String
  | "href" => some u.href
  | "protocol" => some u.protocol
  | "username" => some u.username
  | "password" => some u.password
  | "host" => some u.hostAttr
  | "hostname" => some u.hostname
  | "port" => some u.portAttr
  | "pathname" => some u.pathname
  | "search" => some u.search
  | "hash" => some u.hash
  | _ => none

/-- setter を属性名で引く。`href` だけは失敗しうるので、失敗したら元の record を返す。 -/
def Url.setAttr (u : Url) (name v : String)
    (toAscii : List Char → Option String := asciiDomainToASCII) : Option Url :=
  match name with
  | "href" => some ((Url.setHref v toAscii).getD u)
  | "protocol" => some (u.setProtocol v)
  | "username" => some (u.setUsername v)
  | "password" => some (u.setPassword v)
  | "host" => some (u.setHost v toAscii)
  | "hostname" => some (u.setHostname v toAscii)
  | "port" => some (u.setPort v)
  | "pathname" => some (u.setPathname v)
  | "search" => some (u.setSearch v)
  | "hash" => some (u.setHash v)
  | _ => none

/-! ## 性質 -/

/--
credentials を置けない URL では `username` setter は何もしない。

`password` / `port` も同じ形。仕様がこの guard を置いているのは、
host が無い（または空の）URL に credentials を付けると
serialize してから読み直したときに戻らないからである。
-/
theorem setUsername_cannot {u : Url} (h : u.cannotHaveCredentials = true) (v : String) :
    u.setUsername v = u := by
  simp [Url.setUsername, h]

theorem setPassword_cannot {u : Url} (h : u.cannotHaveCredentials = true) (v : String) :
    u.setPassword v = u := by
  simp [Url.setPassword, h]

theorem setPort_cannot {u : Url} (h : u.cannotHaveCredentials = true) (v : String) :
    u.setPort v = u := by
  simp [Url.setPort, h]

/-- opaque path を持つ URL では `host` setter は何もしない。`hostname` も同じ。 -/
theorem setHost_opaque {u : Url} (h : u.hasOpaquePath = true) (v : String) :
    u.setHost v = u := by
  simp [Url.setHost, h]

theorem setHostname_opaque {u : Url} (h : u.hasOpaquePath = true) (v : String) :
    u.setHostname v = u := by
  simp [Url.setHostname, h]

theorem setPathname_opaque {u : Url} (h : u.hasOpaquePath = true) (v : String) :
    u.setPathname v = u := by
  simp [Url.setPathname, h]

/-!
### `ValidUrl` の保存

parser を通らない setter については保存が示せる。
`username` / `password` は record を直接書き換えるだけ、
`port` は空文字列なら port を消すだけだからである。

`protocol` / `host` / `hostname` / `port`（非空）/ `pathname` / `search` / `hash` は
`basicUrlParseOverride` を通るので、parser 側の保存
（`docs/url-status.md` の未着手）に帰着する。
-/

/-- credentials を置ける URL は host を持ち、opaque path でない。 -/
theorem not_opaque_of_canHaveCredentials {u : Url} (h : ValidUrl u)
    (hc : u.cannotHaveCredentials = false) : u.host ≠ none ∧ u.hasOpaquePath = false := by
  have hhost : u.host ≠ none := by
    intro hn
    simp [Url.cannotHaveCredentials, hn] at hc
  refine ⟨hhost, ?_⟩
  cases ho : u.hasOpaquePath with
  | false => rfl
  | true => exact absurd (h.opaqueNoHost ho) hhost

/--
`username` setter は `ValidUrl` を保つ。

guard が通るとき host は非 null なので `nullHost*` は前提を持たない。
opaque path でないことは `opaqueNoHost` から出る。ここが、
仕様が §4.1 に並べていない条件を `ValidUrl` に入れている理由である。
-/
theorem setUsername_valid {u : Url} (h : ValidUrl u) (v : String) : ValidUrl (u.setUsername v) := by
  cases hc : u.cannotHaveCredentials with
  | true => rw [setUsername_cannot hc]; exact h
  | false =>
    obtain ⟨hhost, hop⟩ := not_opaque_of_canHaveCredentials h hc
    have he : u.setUsername v = { u with username := userinfoEncode v } := by
      simp [Url.setUsername, hc]
    rw [he]
    exact ⟨h.specialHasList, fun hn => (hhost hn).elim, fun hn => (hhost hn).elim,
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]),
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]),
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]), h.portRange,
      fun hf => by
        have hcc : u.cannotHaveCredentials = true := by
          simp [Url.cannotHaveCredentials, show u.scheme = "file" from hf]
        rw [hcc] at hc; simp at hc,
      fun hf => by
        have hcc : u.cannotHaveCredentials = true := by
          simp [Url.cannotHaveCredentials, show u.scheme = "file" from hf]
        rw [hcc] at hc; simp at hc⟩

theorem setPassword_valid {u : Url} (h : ValidUrl u) (v : String) : ValidUrl (u.setPassword v) := by
  cases hc : u.cannotHaveCredentials with
  | true => rw [setPassword_cannot hc]; exact h
  | false =>
    obtain ⟨hhost, hop⟩ := not_opaque_of_canHaveCredentials h hc
    have he : u.setPassword v = { u with password := userinfoEncode v } := by
      simp [Url.setPassword, hc]
    rw [he]
    exact ⟨h.specialHasList, fun hn => (hhost hn).elim, fun hn => (hhost hn).elim,
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]),
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]),
      fun ho => absurd (show u.hasOpaquePath = true from ho) (by simp [hop]), h.portRange,
      fun hf => by
        have hcc : u.cannotHaveCredentials = true := by
          simp [Url.cannotHaveCredentials, show u.scheme = "file" from hf]
        rw [hcc] at hc; simp at hc,
      fun hf => by
        have hcc : u.cannotHaveCredentials = true := by
          simp [Url.cannotHaveCredentials, show u.scheme = "file" from hf]
        rw [hcc] at hc; simp at hc⟩

/-- `port` setter に空文字列を渡すと port が消え、`ValidUrl` は保たれる。 -/
theorem setPort_empty_valid {u : Url} (h : ValidUrl u) : ValidUrl (u.setPort "") := by
  cases hc : u.cannotHaveCredentials with
  | true => rw [setPort_cannot hc]; exact h
  | false =>
    have he : u.setPort "" = { u with port := none } := by simp [Url.setPort, hc]
    rw [he]
    exact ⟨h.specialHasList, h.nullHostNoCredentials, fun _ => rfl,
      h.opaqueNoCredentials, fun _ => rfl, h.opaqueNoHost, by simp,
      h.fileNoCredentials, fun _ => rfl⟩

end Url
