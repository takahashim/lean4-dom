import Dom.Idl.Value

/-!
# ECMAScript の ToNumber と StringToNumber

WebIDL の整数型への変換（ConvertToInt）の step 4 は ToNumber(V) である（ECMA-262 §7.1.4）。

* undefined は NaN、null は +0、boolean は 1 か +0、Number はそのまま。
* String は StringToNumber（§7.1.4.1.1）で、`StringNumericLiteral` の文法で読めなければ NaN である。
* object は ToPrimitive（hint number）で primitive にしてから ToNumber する。普通の object と配列は
  `valueOf` が自分を返すので `toString` が使われ、普通の object は "[object Object]"（NaN）、配列は
  `join` の結果の文字列になる。

ToNumber は model が表す値について失敗も副作用も無い（利用者のコードを呼ばない）。結果が一つに決まらない値
（有効数字が 20 桁を超える十進表記、DOMString への変換が対象外の数を含む配列）は `none` である。

## StringToNumber の文法

```
StringNumericLiteral ::: StrWhiteSpace_opt
                       | StrWhiteSpace_opt StrNumericLiteral StrWhiteSpace_opt
StrNumericLiteral ::: StrDecimalLiteral | NonDecimalIntegerLiteral
StrDecimalLiteral ::: StrUnsignedDecimalLiteral | + StrUnsignedDecimalLiteral | - StrUnsignedDecimalLiteral
StrUnsignedDecimalLiteral ::: Infinity
                            | DecimalDigits . DecimalDigits_opt ExponentPart_opt
                            | . DecimalDigits ExponentPart_opt
                            | DecimalDigits ExponentPart_opt
NonDecimalIntegerLiteral ::: 0b BinaryDigits | 0o OctalDigits | 0x HexDigits（大文字の B・O・X も）
```

数字の区切り（`1_000`）は StringNumericLiteral には無い。NonDecimalIntegerLiteral に符号は付かない。
-/

namespace Dom.Idl

/--
StrWhiteSpaceChar：WhiteSpace（TAB、VT、FF、ZWNBSP、Zs の文字）と LineTerminator（LF、CR、LS、PS）。
Zs は U+0020、U+00A0、U+1680、U+2000–U+200A、U+202F、U+205F、U+3000 である。
-/
def isStrWhiteSpace (c : Char) : Bool :=
  let n := c.toNat
  n == 0x09 || n == 0x0B || n == 0x0C || n == 0xFEFF ||
  n == 0x20 || n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
  n == 0x202F || n == 0x205F || n == 0x3000 ||
  n == 0x0A || n == 0x0D || n == 0x2028 || n == 0x2029

/-- 基数 radix の数字の値。数字でなければ `none`。 -/
def digitValue (radix : Nat) (c : Char) : Option Nat :=
  let v :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
    else none
  match v with
  | some d => if d < radix then some d else none
  | none => none

/-- 一つ以上の数字の列を基数 radix の自然数として読む。 -/
def readDigits (radix : Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldlM (fun acc c => (digitValue radix c).map (acc * radix + ·)) 0

/-- 十進の数字だけからなる列か（空でもよい）。 -/
private def allDecimal (cs : List Char) : Bool := cs.all (fun c => '0' ≤ c && c ≤ '9')

/--
`StrUnsignedDecimalLiteral` のうち Infinity 以外。仮数の数字列と十進の指数を返す。
-/
def readUnsignedDecimal (cs : List Char) : Option (Nat × Int) := do
  -- 指数部で分ける
  let (body, expPart) := match cs.findIdx? (fun c => c == 'e' || c == 'E') with
    | some i => (cs.take i, some (cs.drop (i + 1)))
    | none => (cs, none)
  let exp : Int ← match expPart with
    | none => pure 0
    | some ('+' :: ds) => do pure ((← readDigits 10 ds : Nat) : Int)
    | some ('-' :: ds) => do pure (-((← readDigits 10 ds : Nat) : Int))
    | some ds => do pure ((← readDigits 10 ds : Nat) : Int)
  let (intPart, fracPart) := match body.findIdx? (· == '.') with
    | some i => (body.take i, body.drop (i + 1))
    | none => (body, [])
  -- 数字が一つも無い（"." や ""）なら読めない
  if intPart.isEmpty && fracPart.isEmpty then none
  else if !(allDecimal intPart && allDecimal fracPart) then none
  else
    let m ← readDigits 10 (intPart ++ fracPart)
    pure (m, exp - fracPart.length)

/-- **ECMAScript の StringToNumber。** 結果が一つに決まらない（有効数字が 20 桁を超える）なら `none`。 -/
def stringToNumber (s : String) : Option JsNum :=
  let cs := ((s.toList.dropWhile isStrWhiteSpace).reverse.dropWhile isStrWhiteSpace).reverse
  match cs with
  | [] => some (.finite false 0 0)
  | '0' :: r :: ds =>
    if r == 'x' || r == 'X' then some (nonDecimal 16 ds)
    else if r == 'o' || r == 'O' then some (nonDecimal 8 ds)
    else if r == 'b' || r == 'B' then some (nonDecimal 2 ds)
    else signed false cs
  | '+' :: rest => signed false rest
  | '-' :: rest => signed true rest
  | _ => signed false cs
where
  /-- NonDecimalIntegerLiteral。値は整数で、丸めは 𝔽(MV)（20 桁の規則は無い）。 -/
  nonDecimal (radix : Nat) (ds : List Char) : JsNum :=
    match readDigits radix ds with
    | some v => JsNum.ofRat false v 1
    | none => .nan
  signed (neg : Bool) (cs : List Char) : Option JsNum :=
    if cs == "Infinity".toList then some (.infinity neg)
    else match readUnsignedDecimal cs with
      | some (m, e) => JsNum.ofDecimal? neg m e
      | none => some .nan

/-- **ECMAScript の ToNumber。** 結果が一つに決まらない値は `none`。 -/
def JsValue.toNumber : JsValue → Option JsNum
  | .undefined => some .nan
  | .null => some (.finite false 0 0)
  | .bool b => some (.finite false (if b then 1 else 0) 0)
  | .number n => n.toNum?
  | .string s => stringToNumber s
  | .object _ => stringToNumber "[object Object]"
  | .array xs => (JsValue.array xs).toJsString.bind stringToNumber

/-! ## 例 -/

private def u32 (v : JsValue) : Option Nat := v.toNumber.map toUnsignedLong

#guard u32 .null == some 0
#guard u32 (.bool true) == some 1
#guard u32 (.string "  12\n") == some 12
#guard u32 (.string "") == some 0
#guard u32 (.string "0x10") == some 16
#guard u32 (.string "0b101") == some 5
#guard u32 (.string "-0x10") == some 0
#guard u32 (.string "1_000") == some 0
#guard u32 (.string "1e3") == some 1000
#guard u32 (.string ".5") == some 0
#guard u32 (.string "5.") == some 5
#guard u32 (.string "-1") == some 4294967295
#guard u32 (.string "Infinity") == some 0
#guard u32 (.string " 1　") == some 1
#guard u32 (.string "1 2") == some 0
#guard u32 (.array [.number ⟨7, 0⟩]) == some 7
#guard u32 (.array []) == some 0
#guard u32 (.array [.number ⟨1, 0⟩, .number ⟨2, 0⟩]) == some 0
#guard u32 (.object []) == some 0
#guard u32 .undefined == some 0

end Dom.Idl
