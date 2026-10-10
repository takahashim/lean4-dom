import Dom.Idl.NumberString
import Dom.Basic.Exception

/-!
# JavaScript の値と、WebIDL の boolean・dictionary・union への変換

scenario が JSON で運ぶ JavaScript の値（`JsValue`）と、WebIDL Standard（`docs/spec-version.md` の版）の
変換のうち、`addEventListener` と `removeEventListener` の options と、`MutationObserverInit` に要るものを書く。

* boolean への変換は ECMAScript の ToBoolean である（§3.2.2）。
* dictionary への変換は、継承の根から順に、各 dictionary の member を辞書順に `Get` で読み、undefined でなければ
  member の型へ変換し、undefined なら既定値を使う（§3.2.17）。
* DOMString への変換は ECMAScript の ToString である（§3.2.10）。
* `sequence<T>` への変換は、object でなければ TypeError、`@@iterator` が無ければ TypeError、あれば
  iterator が返す値を順に T へ変換する（§3.2.20）。
* union への変換は、null と undefined なら dictionary、object なら dictionary、boolean ならそのまま、
  それ以外（数と文字列）は union が string 型も numeric 型も含まないので boolean へ変換する（§3.2.24）。

## 対象外

object は JSON の object（プロパティの列）と配列に限る。getter や prototype の上書きは無いので、`Get` は
自分のプロパティを引くだけで、利用者のコードは走らない。配列は組み込みの `Array` で、`@@iterator` は要素を
順に返し、ToString は `Array.prototype.join` で "," つなぎになる。普通の object は `@@iterator` を持たず、
ToString は "[object Object]" になる。関数と platform object（AbortSignal など）は表さない。
数の ToString は有効数字 15 桁以下の数に限る（`Dom/Idl/NumberString.lean`）。
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
  | array (elems : List JsValue)
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
  | .array _ => true

def isUndefined : JsValue → Bool
  | .undefined => true
  | _ => false

/-- object か（配列を含む）。 -/
def isObject : JsValue → Bool
  | .object _ | .array _ => true
  | _ => false

mutual

/--
**ECMAScript の ToString。** 数が対象外（有効数字が 15 桁を超えるなど）なら `none`。

object は ToPrimitive が `toString` を呼ぶ。普通の object は `Object.prototype.toString` で
"[object Object]"、配列は `Array.prototype.join` で、要素を "," でつなぐ（undefined と null の要素は空文字列）。
-/
def toJsString : JsValue → Option String
  | .undefined => some "undefined"
  | .null => some "null"
  | .bool b => some (if b then "true" else "false")
  | .number n => n.toJsString
  | .string s => some s
  | .object _ => some "[object Object]"
  | .array xs => joinElems xs

/-- `Array.prototype.join(",")`。 -/
def joinElems : List JsValue → Option String
  | [] => some ""
  | [x] => joinElem x
  | x :: rest => do
    let a ← joinElem x
    let b ← joinElems rest
    pure (a ++ "," ++ b)

/-- join の一つの要素。undefined と null は空文字列。 -/
def joinElem : JsValue → Option String
  | .undefined | .null => some ""
  | v => toJsString v

end

end JsValue

/-- **JavaScript の値を IDL の `DOMString` に変換する。** 数が対象外なら model の対象外。 -/
def toDOMString (v : JsValue) : Except IdlException String :=
  match v.toJsString with
  | some s => .ok s
  | none => .error (.dom .outsideModel)

/--
**JavaScript の値を IDL の `DOMString?` に変換する。** undefined と null は null、それ以外は DOMString へ
変換する（§3.2.22 nullable types）。
-/
def toNullableDOMString (v : JsValue) : Except IdlException (Option String) :=
  match v with
  | .undefined | .null => .ok none
  | _ => some <$> toDOMString v

/--
**`[LegacyNullToEmptyString]` の付いた `DOMString` に変換する。** null は ToString ではなく空文字列になる
（§3.3.11）。CharacterData の `data` の setter がこれである。
-/
def toLegacyNullDOMString (v : JsValue) : Except IdlException String :=
  match v with
  | .null => .ok ""
  | _ => toDOMString v

/--
**DOMString への変換は TypeError を投げない。** model が表す値（primitive、普通の object、配列）の ToString は
利用者のコードを呼ばず、失敗しない。失敗するのは model の対象外の数だけである。

このため、引数の DOMString への変換を、scenario を読むときに前もって行っても観測は変わらない
（`Dom/Exec/Json.lean`）。変換は副作用を持たず、this の検査やほかの引数の変換と順序を入れ替えても結果が同じである。
-/
theorem toDOMString_error {v : JsValue} {e : IdlException} (h : toDOMString v = .error e) :
    e = .dom .outsideModel := by
  unfold toDOMString at h
  split at h
  · cases h
  · cases h; rfl

theorem toNullableDOMString_error {v : JsValue} {e : IdlException}
    (h : toNullableDOMString v = .error e) : e = .dom .outsideModel := by
  unfold toNullableDOMString at h
  split at h
  · cases h
  · cases h
  · cases hv : toDOMString v with
    | ok s => rw [hv] at h; cases h
    | error e' => rw [hv] at h; cases h; exact toDOMString_error hv

theorem toLegacyNullDOMString_error {v : JsValue} {e : IdlException}
    (h : toLegacyNullDOMString v = .error e) : e = .dom .outsideModel := by
  unfold toLegacyNullDOMString at h
  split at h
  · cases h
  · exact toDOMString_error h

/--
**JavaScript の値を IDL の `sequence<DOMString>` に変換する。**

1. object でなければ TypeError。
2. `@@iterator` を引く。undefined なら TypeError（普通の object がこれに当たる）。
3. iterator が返す値を順に DOMString に変換する（配列は要素を順に返す）。
-/
def toSequenceDOMString : JsValue → Except IdlException (List String)
  | .array xs => xs.mapM toDOMString
  | _ => .error .typeError

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
  | .undefined | .null | .object _ | .array _ => .dict (boolMember v "capture" false)
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
  | .undefined | .null | .object _ | .array _ =>
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

#guard JsValue.toJsString (.array [.number ⟨1, 0⟩, .null, .array [.bool true, .string "a"]]) = some "1,,true,a"
#guard JsValue.toJsString (.object []) = some "[object Object]"
#guard (toSequenceDOMString (.object [])).toOption = none

end Dom.Idl
