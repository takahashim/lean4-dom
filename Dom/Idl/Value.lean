import Dom.Idl.Number

/-!
# JavaScript の値と、WebIDL の boolean・dictionary・union への変換

scenario が JSON で運ぶ JavaScript の値（`JsValue`）と、WebIDL Standard（`docs/spec-version.md` の版）の
変換のうち、`addEventListener` と `removeEventListener` の options に要るものを書く。

* boolean への変換は ECMAScript の ToBoolean である（§3.2.2）。
* dictionary への変換は、継承の根から順に、各 dictionary の member を辞書順に `Get` で読み、undefined でなければ
  member の型へ変換し、undefined なら既定値を使う（§3.2.17）。
* union への変換は、null と undefined なら dictionary、object なら dictionary、boolean ならそのまま、
  それ以外（数と文字列）は union が string 型も numeric 型も含まないので boolean へ変換する（§3.2.24）。

## 対象外

object は JSON の object（プロパティの列）に限る。getter や prototype は無いので、`Get` は自分のプロパティを
引くだけで、利用者のコードは走らない。配列、関数、platform object（AbortSignal など）は表さない。
`AbortSignal` 型の member（`signal`）に undefined 以外の値が来れば、それは AbortSignal ではないので TypeError になる。
-/

namespace Dom.Idl

/-- JSON が運べる JavaScript の値。undefined は「プロパティが無い」ことで表す。 -/
inductive JsValue where
  | undefined
  | null
  | bool (b : Bool)
  | number (n : JsNumber)
  | string (s : String)
  | object (props : List (String × JsValue))
deriving Repr, Inhabited

namespace JsValue

/-- ECMAScript の `Get(O, key)`。自分のプロパティを引き、無ければ undefined。object でない値は使わない。 -/
def get : JsValue → String → JsValue
  | .object props, key => match props.find? (·.1 == key) with
    | some (_, v) => v
    | none => .undefined
  | _, _ => .undefined

/-- ECMAScript の ToBoolean。NaN は JSON に無いので、数は 0 かどうかだけで決まる。 -/
def toBoolean : JsValue → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !n.isZero
  | .string s => !s.isEmpty
  | .object _ => true

def isUndefined : JsValue → Bool
  | .undefined => true
  | _ => false

end JsValue

/-- dictionary の boolean の member を読む。undefined なら既定値。 -/
def boolMember (v : JsValue) (key : String) (default : Bool) : Bool :=
  let m := v.get key
  if m.isUndefined then default else m.toBoolean

/-- 既定値の無い boolean の member を読む。undefined なら無い。 -/
def boolMember? (v : JsValue) (key : String) : Option Bool :=
  let m := v.get key
  if m.isUndefined then none else some m.toBoolean

/-! ## `(EventListenerOptions or boolean)` -/

/-- IDL の `(EventListenerOptions or boolean)` の値。 -/
inductive EventListenerOptionsOrBoolean where
  | boolean (b : Bool)
  /-- `dictionary EventListenerOptions { boolean capture = false; }` -/
  | dict (capture : Bool)
deriving DecidableEq, Repr

/-- **JavaScript の値を `(EventListenerOptions or boolean)` に変換する。** 失敗しない。 -/
def toEventListenerOptions (v : JsValue) : EventListenerOptionsOrBoolean :=
  match v with
  | .undefined | .null | .object _ => .dict (boolMember v "capture" false)
  | .bool b => .boolean b
  | .number _ | .string _ => .boolean v.toBoolean

/-! ## `(AddEventListenerOptions or boolean)` -/

/-- IDL の `(AddEventListenerOptions or boolean)` の値。`signal` は model に無い。 -/
inductive AddEventListenerOptionsOrBoolean where
  | boolean (b : Bool)
  /--
  `dictionary AddEventListenerOptions : EventListenerOptions { boolean passive; boolean once = false;
  AbortSignal signal; }`。passive は既定値が無いので、無ければ `none`。
  -/
  | dict (capture : Bool) (once : Bool) (passive : Option Bool)
deriving DecidableEq, Repr

/--
**JavaScript の値を `(AddEventListenerOptions or boolean)` に変換する。**

dictionary は EventListenerOptions の `capture`、AddEventListenerOptions の `once`・`passive`・`signal` の順に読む。
`signal` が undefined でなければ AbortSignal への変換が TypeError になるので、`none` を返す。
-/
def toAddEventListenerOptions (v : JsValue) : Option AddEventListenerOptionsOrBoolean :=
  match v with
  | .undefined | .null | .object _ =>
    let capture := boolMember v "capture" false
    let once := boolMember v "once" false
    let passive := boolMember? v "passive"
    if (v.get "signal").isUndefined then some (.dict capture once passive) else none
  | .bool b => some (.boolean b)
  | .number _ | .string _ => some (.boolean v.toBoolean)

/-! ## 例 -/

example : toAddEventListenerOptions (.bool true) = some (.boolean true) := by decide
example : toAddEventListenerOptions .null = some (.dict false false none) := by decide
example : toAddEventListenerOptions (.string "") = some (.boolean false) := by decide
example : toAddEventListenerOptions (.object [("passive", .number ⟨0, 0⟩), ("once", .string "x")]) =
    some (.dict false true (some false)) := by decide
example : toAddEventListenerOptions (.object [("signal", .null)]) = none := by decide

end Dom.Idl
