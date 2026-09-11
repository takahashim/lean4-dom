import Url.Host

/-!
# URL record と serializer

WHATWG URL Standard §4.1 の URL record、§4.2 の special scheme、
§4.3 の URL serializer と URL path serializer。
-/

namespace Url

open Infra

/-- URL Standard §4.1 の path。opaque path か、segment の列。 -/
inductive Path where
  | opaque (s : String)
  | list (segments : List String)
deriving DecidableEq, Repr, Inhabited

/-- URL Standard §4.1 の URL record。 -/
structure Url where
  scheme : String := ""
  username : String := ""
  password : String := ""
  host : Option Host := none
  port : Option Nat := none
  path : Path := .list []
  query : Option String := none
  fragment : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- URL Standard §4.2 special scheme の既定の port。special でなければ `none`。 -/
def defaultPort (scheme : String) : Option Nat :=
  if scheme == "ftp" then some 21
  else if scheme == "http" then some 80
  else if scheme == "https" then some 443
  else if scheme == "ws" then some 80
  else if scheme == "wss" then some 443
  else none

/-- URL Standard §4.2 special scheme。`file` は既定の port を持たないので別に見る。 -/
def isSpecialScheme (scheme : String) : Bool :=
  scheme == "file" || (defaultPort scheme).isSome

/-- URL Standard §4.2「URL is special」。 -/
def Url.isSpecial (u : Url) : Bool := isSpecialScheme u.scheme

/-- URL Standard §4.2「URL includes credentials」。 -/
def Url.includesCredentials (u : Url) : Bool := !u.username.isEmpty || !u.password.isEmpty

/-- URL Standard §4.2「URL has an opaque path」。 -/
def Url.hasOpaquePath (u : Url) : Bool :=
  match u.path with
  | .opaque _ => true
  | .list _ => false

/-- URL Standard §4.3 URL path serializer。 -/
def pathSerializer : Path → String
  | .opaque s => s
  | .list segs => segs.foldl (fun acc s => acc ++ "/" ++ s) ""

/-- URL Standard §4.3 URL serializer。 -/
def urlSerializer (u : Url) (excludeFragment : Bool := false) : String :=
  let out := u.scheme ++ ":"
  let out := match u.host with
    | some h =>
      let out := out ++ "//"
      let out := if u.includesCredentials then
          out ++ u.username ++ (if u.password.isEmpty then "" else ":" ++ u.password) ++ "@"
        else out
      let out := out ++ hostSerializer h
      match u.port with
      | some p => out ++ ":" ++ toString p
      | none => out
    | none =>
      -- host が null で、opaque path でなく、先頭 segment が空なら `/.` を足す。
      -- これが無いと `web+demo:/.//x/` が parse し直しで host を持ってしまう。
      match u.path with
      | .list (seg :: _ :: _) => if seg.isEmpty then out ++ "/." else out
      | _ => out
  let out := out ++ pathSerializer u.path
  let out := match u.query with
    | some q => out ++ "?" ++ q
    | none => out
  match u.fragment with
  | some f => if excludeFragment then out else out ++ "#" ++ f
  | none => out

/-! ## 妥当な URL record -/

/--
URL record の局所不変条件。

仕様が §4.1 に並べている条件のうち、parse の結果が常に満たすものである。

* opaque path を持てるのは special でない URL だけ。
* host が null なら credentials も port も持てない。
* opaque path なら credentials も port も持てない。
-/
structure ValidUrl (u : Url) : Prop where
  specialHasList : u.isSpecial = true → u.hasOpaquePath = false
  nullHostNoCredentials : u.host = none → u.includesCredentials = false
  nullHostNoPort : u.host = none → u.port = none
  opaqueNoCredentials : u.hasOpaquePath = true → u.includesCredentials = false
  opaqueNoPort : u.hasOpaquePath = true → u.port = none

/-- 既定の port を持つ scheme は special である。 -/
theorem isSpecialScheme_of_defaultPort {scheme : String} {p : Nat}
    (h : defaultPort scheme = some p) : isSpecialScheme scheme = true := by
  unfold isSpecialScheme
  rw [h]
  simp

/-- `file` は special だが既定の port を持たない。 -/
theorem defaultPort_file : defaultPort "file" = none := by decide

theorem isSpecialScheme_file : isSpecialScheme "file" = true := by decide

end Url
