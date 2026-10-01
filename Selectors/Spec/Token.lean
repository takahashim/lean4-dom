import Infra.Ascii

/-!
# CSS tokenizer の関係仕様（CSS Syntax Level 3 §3.3・§4）

`Selectors/Token.lean` の tokenizer を、**実行関数を呼ばずに**関係として書く。
版は `docs/selectors-spec-version.md` に固定した Editor's Draft で、§ 番号もその版のものである。

規則は本文のアルゴリズムの分岐に一対一で対応させる。差分テストで tokenizer に起因する
不一致が出たとき、どの § のどの分岐で割れたかを名指しできるようにするためである。

使ってよいのは code point の数値範囲と list の添字だけで、`Selectors/Token.lean` の
関数（`isIdentStart`・`startsValidEscape` など）は呼ばない。code point の分類も
`Infra.Ascii` ではなく CSS Syntax §4.2 の定義から書き写す。

`Selectors/Spec/TokenSound.lean` で実行関数がこれを満たすことを、
`Selectors/Spec/TokenDeterministic.lean` で関係が結果を一意に決めることを示す。

## 本文との差（`Selectors/Token.lean` 冒頭と同じ）

* surrogate を U+FFFD にする前処理は無い。Lean の `Char` は surrogate を持てない。
-/

namespace Selectors.Spec

/-! ## code point の分類（§4.2） -/

/-- digit：U+0030..U+0039。 -/
def Digit (c : Char) : Prop := 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39

/-- hex digit：digit、U+0041..U+0046、U+0061..U+0066。 -/
def HexDigit (c : Char) : Prop :=
  Digit c ∨ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46) ∨ (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x66)

/-- letter：uppercase letter（U+0041..U+005A）か lowercase letter（U+0061..U+007A）。 -/
def Letter (c : Char) : Prop :=
  (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) ∨ (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A)

/-- non-ASCII ident code point。本文の 15 項目をそのまま並べる（範囲はすべて両端を含む）。 -/
def NonAsciiIdentCp (c : Char) : Prop :=
  let n := c.toNat
  n = 0xB7 ∨ (0xC0 ≤ n ∧ n ≤ 0xD6) ∨ (0xD8 ≤ n ∧ n ≤ 0xF6) ∨ (0xF8 ≤ n ∧ n ≤ 0x37D) ∨
    (0x37F ≤ n ∧ n ≤ 0x1FFF) ∨ n = 0x200C ∨ n = 0x200D ∨ n = 0x203F ∨ n = 0x2040 ∨
    (0x2070 ≤ n ∧ n ≤ 0x218F) ∨ (0x2C00 ≤ n ∧ n ≤ 0x2FEF) ∨ (0x3001 ≤ n ∧ n ≤ 0xD7FF) ∨
    (0xF900 ≤ n ∧ n ≤ 0xFDCF) ∨ (0xFDF0 ≤ n ∧ n ≤ 0xFFFD) ∨ 0x10000 ≤ n

/-- ident-start code point：letter、non-ASCII ident code point、U+005F LOW LINE。 -/
def IdentStartCp (c : Char) : Prop := Letter c ∨ NonAsciiIdentCp c ∨ c = '_'

/-- ident code point：ident-start code point、digit、U+002D HYPHEN-MINUS。 -/
def IdentCp (c : Char) : Prop := IdentStartCp c ∨ Digit c ∨ c = '-'

/-- newline：U+000A LINE FEED。CR と FF は前処理で LF になっている。 -/
def Newline (c : Char) : Prop := c = '\n'

/-- whitespace：newline、U+0009 CHARACTER TABULATION、U+0020 SPACE。 -/
def Whitespace (c : Char) : Prop := Newline c ∨ c = '\t' ∨ c = ' '

/-! ## 前処理（§3.3 "filter code points"） -/

/--
`Preprocessed input out`：`input` を filter した結果が `out`。

CR・FF・CRLF の組を LF 一つに、NULL を U+FFFD にする。
-/
inductive Preprocessed : List Char → List Char → Prop where
  | nil : Preprocessed [] []
  /-- CR に LF が続く組は LF 一つ。 -/
  | crlf {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\r' :: '\n' :: rest) ('\n' :: out)
  /-- LF が続かない CR は LF。 -/
  | cr {rest out : List Char} (hn : ∀ r, rest ≠ '\n' :: r) (h : Preprocessed rest out) :
      Preprocessed ('\r' :: rest) ('\n' :: out)
  /-- FF は LF。 -/
  | ff {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\x0c' :: rest) ('\n' :: out)
  /-- NULL は U+FFFD。 -/
  | null {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\x00' :: rest) ('\uFFFD' :: out)
  /-- それ以外はそのまま。 -/
  | other {c : Char} {rest out : List Char} (hc : c ≠ '\r' ∧ c ≠ '\x0c' ∧ c ≠ '\x00')
      (h : Preprocessed rest out) :
      Preprocessed (c :: rest) (c :: out)

/-! ## 先読みの判定（§4.3.8–§4.3.10）

本文は「二つ（三つ）の code point」について判定する。入力が尽きた先は EOF code point で、
ここでは `none` で表す。入力の流れに対して呼ぶときは、先頭からの添字で取り出す。
-/

/-- `o` が digit である。EOF は digit でない。 -/
def DigitAt (o : Option Char) : Prop := ∃ d, o = some d ∧ Digit d

/-- §4.3.8 "check if two code points are a valid escape"。 -/
def ValidEscape (a b : Option Char) : Prop :=
  a = some '\\' ∧ ∀ d, b = some d → ¬ Newline d

/--
§4.3.9 "check if three code points would start an ident sequence"。

本文は先頭の code point で場合分けする。`-` と `\` は ident-start code point ではないので、
三つの場合を `∨` で並べても排他である。
-/
def WouldStartIdent (a b c : Option Char) : Prop :=
  (a = some '-' ∧ ((∃ d, b = some d ∧ (IdentStartCp d ∨ d = '-')) ∨ ValidEscape b c)) ∨
  (∃ d, a = some d ∧ IdentStartCp d) ∨
  (a = some '\\' ∧ ValidEscape a b)

/-- §4.3.10 "check if three code points would start a number"。 -/
def WouldStartNumber (a b c : Option Char) : Prop :=
  ((a = some '+' ∨ a = some '-') ∧ (DigitAt b ∨ (b = some '.' ∧ DigitAt c))) ∨
  (a = some '.' ∧ DigitAt b) ∨
  DigitAt a

/-- 入力の流れの先頭が valid escape で始まる。 -/
def StartsValidEscape (l : List Char) : Prop := ValidEscape l[0]? l[1]?

/-- 入力の流れの先頭が ident sequence を始める。 -/
def StartsIdent (l : List Char) : Prop := WouldStartIdent l[0]? l[1]? l[2]?

/-- 入力の流れの先頭が number を始める。 -/
def StartsNumber (l : List Char) : Prop := WouldStartNumber l[0]? l[1]? l[2]?

end Selectors.Spec
