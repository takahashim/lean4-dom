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
ToString は "[object Object]" になる。JSON の値は呼べないので、自分の `toString` を持つ object の ToString と
ToNumber は TypeError になる（`JsValue.ownsToString`）。関数と platform object（AbortSignal など）は表さない。
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

/--
ECMAScript の ToBoolean。数は Number の値に丸めてから 0 か（NaN は JSON に無い）を見る。1e-400 のように
0 に丸まる数は false である。有効数字が 20 桁を超える数も、RoundMVResult の二つの候補がどちらも ±0 なら false、
どちらも ±0 でないなら true である（`JsNumber.zeroAfterRounding?`）。候補で結果が割れる数は、scenario の読み取りが
断る（`Dom/Exec/Json.lean` の `jsValueOfJson`）ので、ここには来ない。
-/
def toBoolean : JsValue → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n.zeroAfterRounding?.getD false)
  | .string s => !s.isEmpty
  | .object _ => true
  | .array _ => true

def isUndefined : JsValue → Bool
  | .undefined => true
  | _ => false

/-- dictionary への変換が受ける値か（undefined・null・object。配列を含む）。 -/
def isObjectOrNullish : JsValue → Bool
  | .undefined | .null | .object _ | .array _ => true
  | _ => false

/-- object か（配列を含む）。 -/
def isObject : JsValue → Bool
  | .object _ | .array _ => true
  | _ => false

/--
**自分の `toString` プロパティを持つ object か。** JSON の値は関数を持てないので、そのプロパティは呼べない。

OrdinaryToPrimitive（ECMA-262 §7.1.1.1）は hint が string なら `toString`、`valueOf` の順に、number なら逆の順に
method を引く（step 1-2）。step 3.1 の `Get` は自分のプロパティを先に見るので、自分の `toString` を持つ object では
`Object.prototype.toString` に届かず、呼べない値なので step 3.2 を飛ばす。`valueOf` は、自分のプロパティなら
呼べないので飛ばし、無ければ `Object.prototype.valueOf` が object 自身を返すので step 3.2.2 を通らない。
どちらの hint でも step 4 の TypeError になる。自分の `toString` を持たなければ、`Object.prototype.toString` が
"[object Object]" を返す。
-/
def ownsToString (props : List (String × JsValue)) : Bool :=
  props.any (·.1 == "toString")

/-- 結果が一つに決まらない値（`none`）を model の対象外にする。 -/
def outsideModelOfNone {α : Type} : Option α → Except IdlException α
  | some a => .ok a
  | none => .error (.dom .outsideModel)

mutual

/--
**ECMAScript の ToString。** 数が対象外（有効数字が 15 桁を超えるなど）なら model の対象外。

object は ToPrimitive が OrdinaryToPrimitive を hint string で呼ぶ。普通の object は `Object.prototype.toString` で
"[object Object]"、自分の `toString` を持つ object は TypeError（`ownsToString`）、配列は `Array.prototype.join` で、
要素を "," でつなぐ（undefined と null の要素は空文字列）。
-/
def toJsString : JsValue → Except IdlException String
  | .undefined => .ok "undefined"
  | .null => .ok "null"
  | .bool b => .ok (if b then "true" else "false")
  | .number n => outsideModelOfNone n.toJsString
  | .string s => .ok s
  | .object props => if ownsToString props then .error .typeError else .ok "[object Object]"
  | .array xs => joinElems xs

/-- `Array.prototype.join(",")`。要素の ToString の失敗はそのまま返す（step 7.3.1 の `?`）。 -/
def joinElems : List JsValue → Except IdlException String
  | [] => .ok ""
  | [x] => joinElem x
  | x :: rest => do
    let a ← joinElem x
    let b ← joinElems rest
    pure (a ++ "," ++ b)

/-- join の一つの要素。undefined と null は空文字列。 -/
def joinElem : JsValue → Except IdlException String
  | .undefined | .null => .ok ""
  | v => toJsString v

end

/-- 失敗するなら TypeError か model の対象外であること。 -/
def ErrTypeOrOutside {α : Type} (r : Except IdlException α) : Prop :=
  ∀ e, r = .error e → e = .typeError ∨ e = .dom .outsideModel

mutual

/--
**ToString が投げるのは TypeError だけである。** ほかの失敗は model の対象外（`outsideModel`）で、
DOMException は投げない。
-/
theorem toJsString_errTypeOrOutside : (v : JsValue) → ErrTypeOrOutside v.toJsString
  | .undefined | .null | .bool _ | .string _ => by intro e h; simp [toJsString] at h
  | .number n => by
    intro e h
    simp only [toJsString, outsideModelOfNone] at h
    split at h <;> cases h
    exact .inr rfl
  | .object props => by
    intro e h
    simp only [toJsString] at h
    split at h <;> cases h
    exact .inl rfl
  | .array xs => by
    intro e h
    simp only [toJsString] at h
    exact joinElems_errTypeOrOutside xs e h

theorem joinElems_errTypeOrOutside : (xs : List JsValue) → ErrTypeOrOutside (joinElems xs)
  | [] => by intro e h; simp [joinElems] at h
  | [x] => by
    intro e h
    simp only [joinElems] at h
    exact joinElem_errTypeOrOutside x e h
  | x :: y :: rest => by
    intro e h
    simp only [joinElems, bind, Except.bind] at h
    split at h
    · cases h; exact joinElem_errTypeOrOutside x e (by assumption)
    · split at h
      · cases h; exact joinElems_errTypeOrOutside (y :: rest) e (by assumption)
      · cases h

theorem joinElem_errTypeOrOutside : (x : JsValue) → ErrTypeOrOutside (joinElem x)
  | .undefined | .null => by intro e h; simp [joinElem] at h
  | .bool b => fun e h => toJsString_errTypeOrOutside (.bool b) e (by simpa only [joinElem] using h)
  | .number n => fun e h => toJsString_errTypeOrOutside (.number n) e (by simpa only [joinElem] using h)
  | .string t => fun e h => toJsString_errTypeOrOutside (.string t) e (by simpa only [joinElem] using h)
  | .object p => fun e h => toJsString_errTypeOrOutside (.object p) e (by simpa only [joinElem] using h)
  | .array a => fun e h => toJsString_errTypeOrOutside (.array a) e (by simpa only [joinElem] using h)

end

/-- `Except` が TypeError で失敗したか（例のための判定）。 -/
def isTypeError {α : Type} : Except IdlException α → Bool
  | .error .typeError => true
  | _ => false

end JsValue

/-- **JavaScript の値を IDL の `DOMString` に変換する。** ToString（§3.2.10 step 2）である。 -/
def toDOMString (v : JsValue) : Except IdlException String := v.toJsString

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
**DOMString への変換が投げるのは TypeError だけである。** model が表す値の ToString は利用者のコードを呼ばず、
副作用を持たない。失敗するのは、自分の `toString` を持つ object（TypeError）と、model の対象外の数だけである。

このため、引数の DOMString への変換を、scenario を読むときに前もって行っても観測は変わらない
（`Dom/Exec/Json.lean`）。method steps より前に起きる WebIDL の失敗（this の検査、interface 型と DOMString の
引数の変換）はどれも TypeError なので、どれが先に起きても結果は同じである。model の対象外の値を含む scenario は、
読み取りの段階で丸ごと断る。
-/
theorem toDOMString_error {v : JsValue} {e : IdlException} (h : toDOMString v = .error e) :
    e = .typeError ∨ e = .dom .outsideModel :=
  JsValue.toJsString_errTypeOrOutside v e h

theorem toNullableDOMString_error {v : JsValue} {e : IdlException}
    (h : toNullableDOMString v = .error e) : e = .typeError ∨ e = .dom .outsideModel := by
  unfold toNullableDOMString at h
  split at h
  · cases h
  · cases h
  · cases hv : toDOMString v with
    | ok s => rw [hv] at h; cases h
    | error e' => rw [hv] at h; cases h; exact toDOMString_error hv

theorem toLegacyNullDOMString_error {v : JsValue} {e : IdlException}
    (h : toLegacyNullDOMString v = .error e) : e = .typeError ∨ e = .dom .outsideModel := by
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

/-- **`(AddEventListenerOptions or boolean)` への変換が TypeError になるのは、dictionary として読む値（undefined・null・
object）に undefined でない `signal` があるときだけである。** -/
theorem toAddEventListenerOptions_eq_none_iff (v : JsValue) :
    toAddEventListenerOptions v = none ↔ v.isObjectOrNullish = true ∧ (v.get "signal").isUndefined = false := by
  cases v <;> simp [toAddEventListenerOptions, JsValue.isObjectOrNullish] <;> split <;> simp_all

/-! ## `(boolean or ImportNodeOptions)` -/

/-- IDL の `(boolean or ImportNodeOptions)` の値。`customElementRegistry` は model に無い。 -/
inductive ImportNodeOptionsOrBoolean where
  | boolean (b : Bool)
  /-- `dictionary ImportNodeOptions { CustomElementRegistry customElementRegistry; boolean selfOnly = false; }` -/
  | dict (selfOnly : Bool)
deriving DecidableEq, Repr

/--
**JavaScript の値を `(boolean or ImportNodeOptions)` に変換する。**

null、undefined、object は dictionary、boolean はそのまま、数と文字列は boolean へ変換する。dictionary は
`customElementRegistry`、`selfOnly` の順に読む。CustomElementRegistry を表せないので、undefined でない
`customElementRegistry` は TypeError（`none`）になる。
-/
def toImportNodeOptions (v : JsValue) : Option ImportNodeOptionsOrBoolean :=
  match v with
  | .undefined | .null | .object _ | .array _ =>
    if (v.get "customElementRegistry").isUndefined then some (.dict (boolMember v "selfOnly" false))
    else none
  | .bool b => some (.boolean b)
  | .number _ | .string _ => some (.boolean v.toBoolean)

/-- **`(boolean or ImportNodeOptions)` への変換が TypeError になるのは、dictionary として読む値に undefined でない
`customElementRegistry` があるときだけである。** -/
theorem toImportNodeOptions_eq_none_iff (v : JsValue) :
    toImportNodeOptions v = none ↔
      v.isObjectOrNullish = true ∧ (v.get "customElementRegistry").isUndefined = false := by
  cases v <;> simp [toImportNodeOptions, JsValue.isObjectOrNullish] <;> split <;> simp_all

/-! ## `(DOMString or ElementCreationOptions)` -/

/--
**`(DOMString or ElementCreationOptions)` への変換が通るか。** null、undefined、object は
`dictionary ElementCreationOptions { CustomElementRegistry? customElementRegistry; DOMString is; }` に、それ以外は
DOMString に変換する。`customElementRegistry` は nullable なので null も受ける。
TypeError になるのは、dictionary として読む値に undefined でも null でもない `customElementRegistry` があるとき
（CustomElementRegistry を表せない）と、`is` の member や DOMString として読む値が自分の `toString` を持つ object
のとき（`JsValue.ownsToString`）である。`ImportNodeOptions` の同名の member は nullable でないので、
そちらは null も TypeError になる（`toImportNodeOptions`）。

`is` と registry は custom element の仕組みで、model は使わない。`is` と null の registry を両方書くと、
"flatten element creation options" の step 3.2.1 が NotSupportedError を投げるが、この step は対象外である。
-/
def elementCreationOptionsOk (v : JsValue) : Bool :=
  if v.isObjectOrNullish then
    registryOk && isOk
  else
    -- DOMString への変換（§3.2.24 step 12 以降）
    !(match v.toJsString with | .error .typeError => true | _ => false)
where
  /-- `customElementRegistry` は nullable で、CustomElementRegistry を表せないので undefined と null だけ通る。 -/
  registryOk : Bool :=
    match v.get "customElementRegistry" with
    | .undefined | .null => true
    | _ => false
  /-- `is` は DOMString の member で、自分の `toString` を持つ object なら TypeError。 -/
  isOk : Bool :=
    match (v.get "is").toJsString with
    | .error .typeError => false
    | _ => true

/-! ## 例 -/

example : toAddEventListenerOptions (.bool true) = some (.boolean true) := by decide
example : toAddEventListenerOptions .null = some (.dict false false none) := by decide
example : toAddEventListenerOptions (.string "") = some (.boolean false) := by decide
example : toAddEventListenerOptions (.object [("passive", .number ⟨0, 0⟩), ("once", .string "x")]) =
    some (.dict false true (some false)) := by decide
example : toAddEventListenerOptions (.object [("signal", .null)]) = none := by decide

#guard (JsValue.toJsString (.array [.number ⟨1, 0⟩, .null, .array [.bool true, .string "a"]])).toOption == some "1,,true,a"
#guard (JsValue.toJsString (.object [])).toOption == some "[object Object]"
#guard (JsValue.toJsString (.object [("valueOf", .number ⟨1, 0⟩)])).toOption == some "[object Object]"
#guard JsValue.isTypeError (JsValue.toJsString (.object [("toString", .number ⟨1, 0⟩)]))
#guard JsValue.isTypeError (JsValue.toJsString (.array [.object [("toString", .null)]]))
#guard (toSequenceDOMString (.object [])).toOption = none

end Dom.Idl
