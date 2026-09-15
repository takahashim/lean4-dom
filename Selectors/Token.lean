import Infra.Ascii

/-!
# CSS の token（CSS Syntax Level 3 §4）

selector を読むのに要る範囲の tokenizer。版は `docs/selectors-spec-version.md` に固定してある。

## 仕様との差

* **`<url-token>` と `<bad-url-token>` を作らない。** `url(` は普通の function-token として
  読む。selector に `url()` は現れないので、どちらの読み方でも `parse a selector` は失敗する。
* **`<unicode-range-token>` を作らない。** "consume a token" の `unicode ranges allowed` は
  selector では false である。
* **surrogate を U+FFFD にする前処理は無い。** Lean の `Char` は surrogate を持てないので
  入力にそもそも現れない（DOM 側の lone surrogate と同じ扱い）。
* 数値は **整数のときだけ値を持つ**。`<an+b>` は整数しか受け付けないので、
  それ以外は「整数ではない」ことが分かれば足りる。
-/

namespace Selectors

open Infra

/-! ## 文字の別名

制御文字と引用符は、source に直接置かずに番号で書く。
-/

def CH_LF : Char := Char.ofNat 0x0A
def CH_CR : Char := Char.ofNat 0x0D
def CH_FF : Char := Char.ofNat 0x0C
def CH_TAB : Char := Char.ofNat 0x09
def CH_SPACE : Char := Char.ofNat 0x20
def CH_NULL : Char := Char.ofNat 0x00
def CH_REPLACEMENT : Char := Char.ofNat 0xFFFD
def CH_QUOTE : Char := Char.ofNat 0x22
def CH_APOS : Char := Char.ofNat 0x27
def CH_BACKSLASH : Char := Char.ofNat 0x5C
def CH_UNDERSCORE : Char := Char.ofNat 0x5F
def CH_HYPHEN : Char := Char.ofNat 0x2D
def CH_PLUS : Char := Char.ofNat 0x2B
def CH_DOT : Char := Char.ofNat 0x2E
def CH_HASH : Char := Char.ofNat 0x23
def CH_COMMA : Char := Char.ofNat 0x2C
def CH_COLON : Char := Char.ofNat 0x3A
def CH_SEMICOLON : Char := Char.ofNat 0x3B
def CH_LPAREN : Char := Char.ofNat 0x28
def CH_RPAREN : Char := Char.ofNat 0x29
def CH_LBRACKET : Char := Char.ofNat 0x5B
def CH_RBRACKET : Char := Char.ofNat 0x5D
def CH_LBRACE : Char := Char.ofNat 0x7B
def CH_RBRACE : Char := Char.ofNat 0x7D
def CH_LT : Char := Char.ofNat 0x3C
def CH_GT : Char := Char.ofNat 0x3E
def CH_AT : Char := Char.ofNat 0x40
def CH_BANG : Char := Char.ofNat 0x21
def CH_PERCENT : Char := Char.ofNat 0x25
def CH_STAR : Char := Char.ofNat 0x2A
def CH_SLASH : Char := Char.ofNat 0x2F
def CH_UPPER_E : Char := Char.ofNat 0x45
def CH_LOWER_E : Char := Char.ofNat 0x65

/-! ## code point の分類（§4.2） -/

/-- 仕様の non-ASCII ident code point。 -/
def isNonAsciiIdent (c : Char) : Bool :=
  let n := c.toNat
  n == 0xB7 || (0xC0 <= n && n <= 0xD6) || (0xD8 <= n && n <= 0xF6) ||
    (0xF8 <= n && n <= 0x37D) || (0x37F <= n && n <= 0x1FFF) ||
    n == 0x200C || n == 0x200D || n == 0x203F || n == 0x2040 ||
    (0x2070 <= n && n <= 0x218F) || (0x2C00 <= n && n <= 0x2FEF) ||
    (0x3001 <= n && n <= 0xD7FF) || (0xF900 <= n && n <= 0xFDCF) ||
    (0xFDF0 <= n && n <= 0xFFFD) || 0x10000 <= n

/-- 仕様の ident-start code point。 -/
def isIdentStart (c : Char) : Bool :=
  isAsciiAlpha c || isNonAsciiIdent c || c == CH_UNDERSCORE

/-- 仕様の ident code point。 -/
def isIdentChar (c : Char) : Bool :=
  isIdentStart c || isAsciiDigit c || c == CH_HYPHEN

/-- 仕様の whitespace。前処理のあとなので改行は LF だけである。 -/
def isWhitespace (c : Char) : Bool := c == CH_LF || c == CH_TAB || c == CH_SPACE

/-! ## token -/

/-- 数値 token が持つもの。値は整数のときだけ意味がある。 -/
structure Num where
  /-- 仕様の type flag が "integer" か。 -/
  isInteger : Bool
  /-- 仕様の value。`isInteger` が false のときは使わない。 -/
  value : Int
  /-- 仕様の sign character。 -/
  sign : Option Char
deriving DecidableEq, Repr, Inhabited

/-- CSS Syntax Level 3 §4 の token。 -/
inductive Token where
  | whitespace
  | string (value : String)
  | badString
  | hash (value : String) (isId : Bool)
  | delim (c : Char)
  | comma
  | colon
  | semicolon
  | lparen
  | rparen
  | lbracket
  | rbracket
  | lbrace
  | rbrace
  | ident (value : String)
  | function (value : String)
  | atKeyword (value : String)
  | number (n : Num)
  | percentage (n : Num)
  | dimension (n : Num) (unit : String)
  | cdo
  | cdc
deriving DecidableEq, Repr, Inhabited

/-! ## 前処理（§3.3） -/

/-- 一文字ぶんの置き換え。CR と FF は LF に、NULL は U+FFFD にする。 -/
def filterChar (c : Char) : Char :=
  if c == CH_CR || c == CH_FF then CH_LF
  else if c == CH_NULL then CH_REPLACEMENT
  else c

/-- CR・FF・CRLF を LF にし、NULL を U+FFFD にする。 -/
def filterCodePoints : List Char -> List Char
  | [] => []
  | [c] => [filterChar c]
  | c :: d :: rest =>
    if c == CH_CR && d == CH_LF then CH_LF :: filterCodePoints rest
    else filterChar c :: filterCodePoints (d :: rest)

/-! ## 先読みの判定（§4.3.8-4.3.11） -/

/-- §4.3.10 "check if two code points are a valid escape"。 -/
def startsValidEscape : List Char -> Bool
  | [] => false
  | [c] => c == CH_BACKSLASH
  | c :: d :: _ => c == CH_BACKSLASH && d != CH_LF

/-- §4.3.11 "check if three code points would start an ident sequence"。 -/
def startsIdentSeq : List Char -> Bool
  | [] => false
  | c :: rest =>
    if c == CH_HYPHEN then
      match rest with
      | [] => false
      | d :: _ => isIdentStart d || d == CH_HYPHEN || startsValidEscape rest
    else if c == CH_BACKSLASH then startsValidEscape (c :: rest)
    else isIdentStart c

/-- §4.3.12 "check if three code points would start a number"。 -/
def startsNumber : List Char -> Bool
  | [] => false
  | c :: rest =>
    if isAsciiDigit c then true
    else if c == CH_PLUS || c == CH_HYPHEN then
      (rest.head?.map isAsciiDigit).getD false ||
        ((rest.head?.map (fun d => d == CH_DOT)).getD false &&
          (rest.tail.head?.map isAsciiDigit).getD false)
    else if c == CH_DOT then (rest.head?.map isAsciiDigit).getD false
    else false

/-! ## escape（§4.3.7） -/

/-- 16 進の値。 -/
def hexNumber (l : List Char) : Nat :=
  l.foldl (fun acc c => acc * 16 + (hexValue c).getD 0) 0

/-- 先頭から高々 `n` 個の hex digit を取る。 -/
def takeHex : Nat -> List Char -> List Char × List Char
  | 0, l => ([], l)
  | _ + 1, [] => ([], [])
  | n + 1, c :: rest =>
    if isAsciiHexDigit c then
      let (ds, rest') := takeHex n rest
      (c :: ds, rest')
    else ([], c :: rest)

theorem takeHex_le : ∀ (n : Nat) (l : List Char), (takeHex n l).2.length <= l.length
  | 0, l => by simp [takeHex]
  | _ + 1, [] => by simp [takeHex]
  | n + 1, c :: rest => by
    simp only [takeHex]
    by_cases h : isAsciiHexDigit c
    · simp only [h, if_pos]
      have := takeHex_le n rest
      simp only [List.length_cons]
      omega
    · simp [h]

/-- escape が表す code point。0・surrogate・範囲外は U+FFFD にする。 -/
def escapedCodePoint (n : Nat) : Char :=
  if n == 0 || 0x10FFFF < n || (0xD800 <= n && n <= 0xDFFF) then CH_REPLACEMENT
  else Char.ofNat n

/-- §4.3.7 "consume an escaped code point"。逆斜線は既に読んだものとする。 -/
def consumeEscape : List Char -> Char × List Char
  | [] => (CH_REPLACEMENT, [])
  | c :: rest =>
    if isAsciiHexDigit c then
      match takeHex 5 rest with
      | (ds, []) => (escapedCodePoint (hexNumber (c :: ds)), [])
      | (ds, w :: r) =>
        if isWhitespace w then (escapedCodePoint (hexNumber (c :: ds)), r)
        else (escapedCodePoint (hexNumber (c :: ds)), w :: r)
    else (c, rest)

theorem consumeEscape_le (c : Char) (rest : List Char) :
    (consumeEscape (c :: rest)).2.length <= rest.length := by
  have h1 := takeHex_le 5 rest
  simp only [consumeEscape]
  split
  · split
    · simp
    · next ds w r heq =>
      rw [heq] at h1
      simp only [List.length_cons] at h1
      split <;> simp only [List.length_cons] <;> omega
  · simp

theorem consumeEscape_lt {l : List Char} (h : l ≠ []) :
    (consumeEscape l).2.length < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons c rest =>
    have := consumeEscape_le c rest
    simp only [List.length_cons]
    omega

theorem consumeEscape_le_self : ∀ (l : List Char), (consumeEscape l).2.length <= l.length
  | [] => by simp [consumeEscape]
  | c :: rest => Nat.le_trans (consumeEscape_le c rest) (Nat.le_succ _)

/-! ## ident sequence（§4.3.12）

仕様は「読んだ文字を result に足す」と書く。ここでは accumulator に逆順で貯めて
最後に反転する。再帰呼び出しが末尾にあるほうが、長さの補題が短く済む。
-/

def identSeqAux (acc : List Char) : List Char -> List Char × List Char
  | [] => (acc.reverse, [])
  | c :: rest =>
    if isIdentChar c then identSeqAux (c :: acc) rest
    else if startsValidEscape (c :: rest) then
      identSeqAux ((consumeEscape rest).1 :: acc) (consumeEscape rest).2
    else (acc.reverse, c :: rest)
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals have := consumeEscape_le_self rest
  all_goals omega

/-- §4.3.12 "consume an ident sequence"。読んだ文字列と残りを返す。 -/
def consumeIdentSeq (l : List Char) : List Char × List Char := identSeqAux [] l

theorem identSeqAux_le : ∀ (acc l : List Char), (identSeqAux acc l).2.length <= l.length
  | _, [] => by simp [identSeqAux]
  | acc, c :: rest => by
    rw [identSeqAux]
    split
    · have := identSeqAux_le (c :: acc) rest
      simp only [List.length_cons]; omega
    · split
      · have h1 := consumeEscape_le_self rest
        have h2 := identSeqAux_le ((consumeEscape rest).1 :: acc) (consumeEscape rest).2
        simp only [List.length_cons]; omega
      · simp
termination_by _ l => l.length
decreasing_by
  all_goals simp_wf
  all_goals have := consumeEscape_le_self rest
  all_goals omega

theorem consumeIdentSeq_le (l : List Char) : (consumeIdentSeq l).2.length <= l.length :=
  identSeqAux_le [] l

/-- ident sequence の先頭にいるなら、少なくとも一文字は読む。 -/
theorem consumeIdentSeq_le_of_start {c : Char} {rest : List Char}
    (h : isIdentChar c = true ∨ startsValidEscape (c :: rest) = true) :
    (consumeIdentSeq (c :: rest)).2.length <= rest.length := by
  simp only [consumeIdentSeq]
  rw [identSeqAux]
  by_cases hc : isIdentChar c
  · simp only [hc, if_pos]
    exact identSeqAux_le _ rest
  · have hesc : startsValidEscape (c :: rest) = true := h.resolve_left (by simpa using hc)
    simp only [hc, Bool.false_eq_true, if_false, hesc, if_pos]
    exact Nat.le_trans (identSeqAux_le _ _) (consumeEscape_le_self rest)

/-- §4.3.11 の判定が通ったなら、先頭は ident code point か escape の始まりである。 -/
theorem identChar_or_escape_of_startsIdentSeq {c : Char} {rest : List Char}
    (h : startsIdentSeq (c :: rest) = true) :
    isIdentChar c = true ∨ startsValidEscape (c :: rest) = true := by
  simp only [startsIdentSeq] at h
  split at h
  · next hc => exact Or.inl (by simp [isIdentChar, hc])
  · split at h
    · next hb => exact Or.inr (by simpa [startsValidEscape] using h)
    · exact Or.inl (by simp [isIdentChar, h])

/-! ## string token（§4.3.5） -/

def stringAux (ending : Char) (acc : List Char) : List Char -> Token × List Char
  | [] => (Token.string (String.ofList acc.reverse), [])
  | c :: rest =>
    if c == ending then (Token.string (String.ofList acc.reverse), rest)
    else if c == CH_LF then (Token.badString, c :: rest)
    else if c == CH_BACKSLASH then
      if rest.isEmpty then (Token.string (String.ofList acc.reverse), [])
      else if (rest.head?.map (fun d => d == CH_LF)).getD false then stringAux ending acc rest.tail
      else stringAux ending ((consumeEscape rest).1 :: acc) (consumeEscape rest).2
    else stringAux ending (c :: acc) rest
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals have := consumeEscape_le_self rest
  all_goals have := @List.length_tail _ rest
  all_goals omega

theorem stringAux_le (e : Char) : ∀ (acc l : List Char), (stringAux e acc l).2.length <= l.length
  | _, [] => by simp [stringAux]
  | acc, c :: rest => by
    rw [stringAux]
    split
    · simp
    · split
      · simp
      · split
        · split
          · simp
          · split
            · have := stringAux_le e acc rest.tail
              have := @List.length_tail _ rest
              simp only [List.length_cons]; omega
            · have h1 := consumeEscape_le_self rest
              have h2 := stringAux_le e ((consumeEscape rest).1 :: acc) (consumeEscape rest).2
              simp only [List.length_cons]; omega
        · have := stringAux_le e (c :: acc) rest
          simp only [List.length_cons]; omega
termination_by _ l => l.length
decreasing_by
  all_goals simp_wf
  all_goals have := consumeEscape_le_self rest
  all_goals have := @List.length_tail _ rest
  all_goals omega

/-! ## number（§4.3.13）

仕様は number part と exponent part を組み立てて十進として読む。ここでは
**整数のときだけ値を持つ**（冒頭の差の項を見よ）。小数点や指数が現れたら
`isInteger` を false にし、`value` は使わない。
-/

/-- 先頭の符号。 -/
def takeSign : List Char -> Option Char × List Char
  | [] => (none, [])
  | c :: rest => if c == CH_PLUS || c == CH_HYPHEN then (some c, rest) else (none, c :: rest)

theorem takeSign_le : ∀ (l : List Char), (takeSign l).2.length <= l.length
  | [] => by simp [takeSign]
  | c :: rest => by
    rw [takeSign]; split
    · simp
    · simp

def digitsAux (acc : List Char) : List Char -> List Char × List Char
  | [] => (acc.reverse, [])
  | c :: rest => if isAsciiDigit c then digitsAux (c :: acc) rest else (acc.reverse, c :: rest)

/-- 続く限り digit を読む。 -/
def takeDigits (l : List Char) : List Char × List Char := digitsAux [] l

theorem digitsAux_le : ∀ (acc l : List Char), (digitsAux acc l).2.length <= l.length
  | _, [] => by simp [digitsAux]
  | acc, c :: rest => by
    rw [digitsAux]; split
    · have := digitsAux_le (c :: acc) rest
      simp only [List.length_cons]; omega
    · simp

theorem takeDigits_le (l : List Char) : (takeDigits l).2.length <= l.length := digitsAux_le [] l

theorem takeDigits_le_of_digit {c : Char} (h : isAsciiDigit c = true) (rest : List Char) :
    (takeDigits (c :: rest)).2.length <= rest.length := by
  simp only [takeDigits]
  rw [digitsAux, if_pos h]
  exact digitsAux_le _ rest

/-- 小数部。`.` に digit が続くときだけ読む。 -/
def takeFraction : List Char -> Bool × List Char
  | c :: d :: rest =>
    if c == CH_DOT && isAsciiDigit d then (true, (takeDigits (d :: rest)).2)
    else (false, c :: d :: rest)
  | l => (false, l)

theorem takeFraction_le : ∀ (l : List Char), (takeFraction l).2.length <= l.length
  | [] => by simp [takeFraction]
  | [_] => by simp [takeFraction]
  | c :: d :: rest => by
    rw [takeFraction]; split
    · have := takeDigits_le (d :: rest)
      simp only [List.length_cons] at *; omega
    · simp

/-- 指数部。`e`/`E` のあとに（符号を挟んで）digit が続くときだけ読む。 -/
def takeExponent : List Char -> Bool × List Char
  | [] => (false, [])
  | c :: rest =>
    if c == CH_UPPER_E || c == CH_LOWER_E then
      if (rest.head?.map isAsciiDigit).getD false then (true, (takeDigits rest).2)
      else if (rest.head?.map (fun d => d == CH_PLUS || d == CH_HYPHEN)).getD false
          && (rest.tail.head?.map isAsciiDigit).getD false then
        (true, (takeDigits rest.tail).2)
      else (false, c :: rest)
    else (false, c :: rest)

theorem takeExponent_le : ∀ (l : List Char), (takeExponent l).2.length <= l.length
  | [] => by simp [takeExponent]
  | c :: rest => by
    rw [takeExponent]; split
    · split
      · have := takeDigits_le rest
        simp only [List.length_cons]; omega
      · split
        · have h1 := takeDigits_le rest.tail
          have h2 := @List.length_tail _ rest
          simp only [List.length_cons]; omega
        · simp
    · simp

/-- digit の並びを十進として読む。 -/
def digitsToNat (l : List Char) : Nat :=
  l.foldl (fun acc c => acc * 10 + (c.toNat - 0x30)) 0

/-- §4.3.13 "consume a number"。 -/
def consumeNumber (l : List Char) : Num × List Char :=
  let s := takeSign l
  let d := takeDigits s.2
  let f := takeFraction d.2
  let e := takeExponent f.2
  ({ isInteger := !f.1 && !e.1,
     value := if s.1 == some CH_HYPHEN then -(digitsToNat d.1 : Int) else (digitsToNat d.1 : Int),
     sign := s.1 }, e.2)

theorem consumeNumber_le (l : List Char) : (consumeNumber l).2.length <= l.length := by
  show (takeExponent (takeFraction (takeDigits (takeSign l).2).2).2).2.length <= l.length
  have h1 := takeSign_le l
  have h2 := takeDigits_le (takeSign l).2
  have h3 := takeFraction_le (takeDigits (takeSign l).2).2
  have h4 := takeExponent_le (takeFraction (takeDigits (takeSign l).2).2).2
  omega

/-- §4.3.12 の判定を、`consumeNumber` の場合分けに合う形にほどく。 -/
theorem startsNumber_cases {c : Char} {rest : List Char} (h : startsNumber (c :: rest) = true) :
    (c == CH_PLUS || c == CH_HYPHEN) = true ∨ isAsciiDigit c = true ∨
      ((c == CH_DOT) = true ∧ (rest.head?.map isAsciiDigit).getD false = true) := by
  rw [startsNumber] at h
  split at h
  · next hd => exact Or.inr (Or.inl hd)
  · split at h
    · next hs => exact Or.inl hs
    · split at h
      · next hdot => exact Or.inr (Or.inr ⟨hdot, h⟩)
      · simp at h

/-- number の先頭にいるなら、少なくとも一文字は読む。 -/
theorem consumeNumber_le_of_start {c : Char} {rest : List Char}
    (h : startsNumber (c :: rest) = true) :
    (consumeNumber (c :: rest)).2.length <= rest.length := by
  show (takeExponent (takeFraction (takeDigits (takeSign (c :: rest)).2).2).2).2.length
    <= rest.length
  by_cases hs : (c == CH_PLUS || c == CH_HYPHEN) = true
  · rw [takeSign, if_pos hs]
    dsimp only
    have h2 := takeDigits_le rest
    have h3 := takeFraction_le (takeDigits rest).2
    have h4 := takeExponent_le (takeFraction (takeDigits rest).2).2
    omega
  · rw [takeSign, if_neg hs]
    dsimp only
    by_cases hd : isAsciiDigit c = true
    · have h2 := takeDigits_le_of_digit hd rest
      have h3 := takeFraction_le (takeDigits (c :: rest)).2
      have h4 := takeExponent_le (takeFraction (takeDigits (c :: rest)).2).2
      omega
    · -- digit でないなら、`.` に digit が続く場合しかない
      have hdot := (startsNumber_cases h).resolve_left hs |>.resolve_left hd
      have hdig : (takeDigits (c :: rest)).2 = c :: rest := by
        simp only [takeDigits]; rw [digitsAux, if_neg hd]
      rw [hdig]
      cases rest with
      | nil => simp at hdot
      | cons d r =>
        have hd2 : isAsciiDigit d = true := by simpa using hdot.2
        rw [takeFraction, if_pos (by simp [hdot.1, hd2])]
        have h3 := takeDigits_le (d :: r)
        have h4 := takeExponent_le (takeDigits (d :: r)).2
        simp only [List.length_cons] at *; omega

/-! ## 数値 token と ident 風 token（§4.3.3-4.3.4） -/

/-- §4.3.3 "consume a numeric token"。 -/
def consumeNumericToken (l : List Char) : Token × List Char :=
  let n := consumeNumber l
  if startsIdentSeq n.2 then
    let u := consumeIdentSeq n.2
    (Token.dimension n.1 (String.ofList u.1), u.2)
  else if (n.2.head?.map (fun c => c == CH_PERCENT)).getD false then
    (Token.percentage n.1, n.2.tail)
  else (Token.number n.1, n.2)

theorem consumeNumericToken_le (l : List Char) :
    (consumeNumericToken l).2.length <= (consumeNumber l).2.length := by
  show (if startsIdentSeq (consumeNumber l).2 then
      (Token.dimension _ (String.ofList (consumeIdentSeq (consumeNumber l).2).1),
        (consumeIdentSeq (consumeNumber l).2).2)
    else if ((consumeNumber l).2.head?.map (fun c => c == CH_PERCENT)).getD false then
      (Token.percentage _, (consumeNumber l).2.tail)
    else (Token.number _, (consumeNumber l).2)).2.length <= (consumeNumber l).2.length
  split
  · exact consumeIdentSeq_le _
  · split
    · have := @List.length_tail _ (consumeNumber l).2
      simp only []; omega
    · simp

/--
§4.3.4 "consume an ident-like token"。

**`url(` を特別扱いしない**（冒頭の差の項を見よ）。`url(` は function-token になる。
-/
def consumeIdentLike (l : List Char) : Token × List Char :=
  let s := consumeIdentSeq l
  if (s.2.head?.map (fun c => c == CH_LPAREN)).getD false then
    (Token.function (String.ofList s.1), s.2.tail)
  else (Token.ident (String.ofList s.1), s.2)

theorem consumeIdentLike_le (l : List Char) :
    (consumeIdentLike l).2.length <= (consumeIdentSeq l).2.length := by
  show (if ((consumeIdentSeq l).2.head?.map (fun c => c == CH_LPAREN)).getD false then
      (Token.function (String.ofList (consumeIdentSeq l).1), (consumeIdentSeq l).2.tail)
    else (Token.ident (String.ofList (consumeIdentSeq l).1), (consumeIdentSeq l).2)).2.length
    <= (consumeIdentSeq l).2.length
  split
  · have := @List.length_tail _ (consumeIdentSeq l).2
    simp only []; omega
  · simp

/-! ## whitespace と comment -/

def skipWhitespace : List Char -> List Char
  | [] => []
  | c :: rest => if isWhitespace c then skipWhitespace rest else c :: rest

theorem skipWhitespace_le : ∀ (l : List Char), (skipWhitespace l).length <= l.length
  | [] => by simp [skipWhitespace]
  | c :: rest => by
    rw [skipWhitespace]; split
    · have := skipWhitespace_le rest
      simp only [List.length_cons]; omega
    · simp

/-- `*/` までを読み飛ばす。閉じずに終わってもそこで止める（仕様の parse error）。 -/
def skipCommentBody : List Char -> List Char
  | [] => []
  | [_] => []
  | c :: d :: rest => if c == CH_STAR && d == CH_SLASH then rest else skipCommentBody (d :: rest)

theorem skipCommentBody_le : ∀ (l : List Char), (skipCommentBody l).length <= l.length
  | [] => by simp [skipCommentBody]
  | [_] => by simp [skipCommentBody]
  | c :: d :: rest => by
    rw [skipCommentBody]; split
    · simp only [List.length_cons]; omega
    · have := skipCommentBody_le (d :: rest)
      simp only [List.length_cons] at *; omega

/-- §4.3.2 "consume comments"。 -/
def skipComments : List Char -> List Char
  | [] => []
  | [c] => [c]
  | c :: d :: rest =>
    if c == CH_SLASH && d == CH_STAR then skipComments (skipCommentBody rest)
    else c :: d :: rest
termination_by l => l.length
decreasing_by
  simp_wf
  have := skipCommentBody_le rest
  omega

theorem skipComments_le : ∀ (l : List Char), (skipComments l).length <= l.length
  | [] => by simp [skipComments]
  | [_] => by simp [skipComments]
  | c :: d :: rest => by
    rw [skipComments]; split
    · have h1 := skipCommentBody_le rest
      have h2 := skipComments_le (skipCommentBody rest)
      simp only [List.length_cons]; omega
    · simp
termination_by l => l.length
decreasing_by
  simp_wf
  have := skipCommentBody_le rest
  omega

/-! ## token を一つ読む（§4.3.1） -/

/-- 一文字がそのまま一つの token になるもの。 -/
def simpleToken (c : Char) : Option Token :=
  if c == CH_COMMA then some Token.comma
  else if c == CH_COLON then some Token.colon
  else if c == CH_SEMICOLON then some Token.semicolon
  else if c == CH_LPAREN then some Token.lparen
  else if c == CH_RPAREN then some Token.rparen
  else if c == CH_LBRACKET then some Token.lbracket
  else if c == CH_RBRACKET then some Token.rbracket
  else if c == CH_LBRACE then some Token.lbrace
  else if c == CH_RBRACE then some Token.rbrace
  else none

/-- `-` のあとが `->` か。 -/
def startsCdc (l : List Char) : Bool :=
  (l.head?.map (fun d => d == CH_HYPHEN)).getD false &&
    (l.tail.head?.map (fun e => e == CH_GT)).getD false

/-- `<` のあとが `!--` か。 -/
def startsCdo (l : List Char) : Bool :=
  (l.head?.map (fun a => a == CH_BANG)).getD false &&
    (l.tail.head?.map (fun b => b == CH_HYPHEN)).getD false &&
    (l.tail.tail.head?.map (fun d => d == CH_HYPHEN)).getD false

/--
§4.3.1 "consume a token" の本体。`c` は読んだ一文字、`rest` はその後ろ。

`unicode ranges allowed` は常に false なので、`U`/`u` の分岐は無い（冒頭の差の項）。
-/
def tokenAt (c : Char) (rest : List Char) : Token × List Char :=
  if isWhitespace c then (Token.whitespace, skipWhitespace rest)
  else if c == CH_QUOTE || c == CH_APOS then stringAux c [] rest
  else
    match simpleToken c with
    | some t => (t, rest)
    | none =>
      if c == CH_HASH then
        if (rest.head?.map isIdentChar).getD false || startsValidEscape rest then
          (Token.hash (String.ofList (consumeIdentSeq rest).1) (startsIdentSeq rest),
            (consumeIdentSeq rest).2)
        else (Token.delim c, rest)
      else if c == CH_PLUS || c == CH_DOT then
        if startsNumber (c :: rest) then consumeNumericToken (c :: rest)
        else (Token.delim c, rest)
      else if c == CH_HYPHEN then
        if startsNumber (c :: rest) then consumeNumericToken (c :: rest)
        else if startsCdc rest then (Token.cdc, rest.tail.tail)
        else if startsIdentSeq (c :: rest) then consumeIdentLike (c :: rest)
        else (Token.delim c, rest)
      else if c == CH_LT then
        if startsCdo rest then (Token.cdo, rest.tail.tail.tail)
        else (Token.delim c, rest)
      else if c == CH_AT then
        if startsIdentSeq rest then
          (Token.atKeyword (String.ofList (consumeIdentSeq rest).1), (consumeIdentSeq rest).2)
        else (Token.delim c, rest)
      else if c == CH_BACKSLASH then
        if startsValidEscape (c :: rest) then consumeIdentLike (c :: rest)
        else (Token.delim c, rest)
      else if isAsciiDigit c then consumeNumericToken (c :: rest)
      else if isIdentStart c then consumeIdentLike (c :: rest)
      else (Token.delim c, rest)

/-- **一文字読んだぶんは必ず進む。** これが tokenizer の停止性を支える。 -/
theorem tokenAt_le (c : Char) (rest : List Char) : (tokenAt c rest).2.length <= rest.length := by
  have htail : ∀ (l : List Char), l.tail.length <= l.length := fun l => by
    have := @List.length_tail _ l; omega
  have hnum : ∀ (h : startsNumber (c :: rest) = true),
      (consumeNumericToken (c :: rest)).2.length <= rest.length := fun h =>
    Nat.le_trans (consumeNumericToken_le _) (consumeNumber_le_of_start h)
  have hident : ∀ (h : isIdentChar c = true ∨ startsValidEscape (c :: rest) = true),
      (consumeIdentLike (c :: rest)).2.length <= rest.length := fun h =>
    Nat.le_trans (consumeIdentLike_le _) (consumeIdentSeq_le_of_start h)
  rw [tokenAt]
  split
  · exact skipWhitespace_le rest
  split
  · exact stringAux_le c [] rest
  split
  · simp
  split
  · split
    · exact consumeIdentSeq_le rest
    · simp
  split
  · split
    · next h => exact hnum h
    · simp
  split
  · split
    · next h => exact hnum h
    · split
      · exact Nat.le_trans (htail _) (htail _)
      · split
        · next h => exact hident (identChar_or_escape_of_startsIdentSeq h)
        · simp
  split
  · split
    · exact Nat.le_trans (htail _) (Nat.le_trans (htail _) (htail _))
    · simp
  split
  · split
    · exact consumeIdentSeq_le rest
    · simp
  split
  · split
    · next h => exact hident (Or.inr h)
    · simp
  split
  · next h => exact hnum (by simp [startsNumber, h])
  split
  · next h => exact hident (Or.inl (by simp [isIdentChar, h]))
  · simp

/-- comment を読み飛ばしてから token を一つ読む。入力が尽きたら `none`。 -/
def nextToken (l : List Char) : Option (Token × List Char) :=
  match skipComments l with
  | [] => none
  | c :: rest => some (tokenAt c rest)

theorem nextToken_lt {l : List Char} {t : Token} {r : List Char}
    (h : nextToken l = some (t, r)) : r.length < l.length := by
  rw [nextToken] at h
  have hle := skipComments_le l
  split at h
  · simp at h
  · next c rest heq =>
    rw [heq] at hle
    simp only [Option.some.injEq] at h
    have hr : (tokenAt c rest).2 = r := by rw [h]
    have hb := tokenAt_le c rest
    rw [hr] at hb
    simp only [List.length_cons] at hle
    omega

/-! ## token 列 -/

def tokenizeAux (acc : List Token) (l : List Char) : List Token :=
  match _h : nextToken l with
  | none => acc.reverse
  | some (t, r) => tokenizeAux (t :: acc) r
termination_by l.length
decreasing_by exact nextToken_lt _h

/-- 文字列を token 列にする。前処理（§3.3）から始める。 -/
def tokenize (input : String) : List Token :=
  tokenizeAux [] (filterCodePoints input.toList)
