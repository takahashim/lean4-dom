import Selectors.Token
import Selectors.Spec.Token

/-!
# tokenizer は関係仕様を満たす

`Selectors/Spec/Token.lean` の関係を、`Selectors/Token.lean` の実行関数が満たすことを示す。
code point の分類と先読みの判定は Bool の関数なので、関係との `↔` を示す。
-/

namespace Selectors.Spec

open Selectors Infra

/-! ## code point の分類 -/

theorem ch_underscore : CH_UNDERSCORE = '_' := by decide
theorem ch_hyphen : CH_HYPHEN = '-' := by decide
theorem ch_lf : CH_LF = '\n' := by decide
theorem ch_tab : CH_TAB = '\t' := by decide
theorem ch_space : CH_SPACE = ' ' := by decide

theorem not_identStart_hyphen : ¬ IdentStartCp '-' := by
  simp [IdentStartCp, Letter, NonAsciiIdentCp]

theorem not_identStart_backslash : ¬ IdentStartCp '\\' := by
  simp [IdentStartCp, Letter, NonAsciiIdentCp]

theorem isAsciiDigit_iff (c : Char) : isAsciiDigit c = true ↔ Digit c := by
  simp [isAsciiDigit, Digit]

theorem isAsciiHexDigit_iff (c : Char) : isAsciiHexDigit c = true ↔ HexDigit c := by
  simp [isAsciiHexDigit, isAsciiUpperHexDigit, isAsciiLowerHexDigit, isAsciiDigit, HexDigit,
    Digit]
  omega

theorem isNonAsciiIdent_iff (c : Char) : isNonAsciiIdent c = true ↔ NonAsciiIdentCp c := by
  simp [isNonAsciiIdent, NonAsciiIdentCp, or_assoc]

theorem isIdentStart_iff (c : Char) : isIdentStart c = true ↔ IdentStartCp c := by
  simp only [isIdentStart, IdentStartCp, Bool.or_eq_true, isNonAsciiIdent_iff, beq_iff_eq]
  have : isAsciiAlpha c = true ↔ Letter c := by
    simp [isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha, Letter]
  rw [this, ch_underscore, or_assoc]

theorem isIdentChar_iff (c : Char) : isIdentChar c = true ↔ IdentCp c := by
  simp only [isIdentChar, IdentCp, Bool.or_eq_true, isIdentStart_iff, isAsciiDigit_iff,
    beq_iff_eq, ch_hyphen, or_assoc]

theorem isWhitespace_iff (c : Char) : isWhitespace c = true ↔ Whitespace c := by
  simp only [isWhitespace, Whitespace, Newline, Bool.or_eq_true, beq_iff_eq, ch_lf, ch_tab,
    ch_space, or_assoc]

/-! ## 前処理 -/

/-- **`filterCodePoints` は `Preprocessed` を満たす。** -/
theorem filterCodePoints_spec : ∀ l : List Char, Preprocessed l (filterCodePoints l)
  | [] => .nil
  | [c] => by
    simp only [filterCodePoints, filterChar]
    by_cases hcr : c = '\r'
    · subst hcr; exact .cr (fun _ h => nomatch h) .nil
    by_cases hff : c = '\x0c'
    · subst hff; exact .ff .nil
    by_cases hnul : c = '\x00'
    · subst hnul; exact .null .nil
    have h1 : (c == CH_CR || c == CH_FF) = false := by
      simp [CH_CR, CH_FF]; exact ⟨hcr, hff⟩
    have h2 : (c == CH_NULL) = false := by simp [CH_NULL]; exact hnul
    rw [h1, h2]
    exact .other ⟨hcr, hff, hnul⟩ .nil
  | c :: d :: rest => by
    have ih := filterCodePoints_spec (d :: rest)
    have ih2 := filterCodePoints_spec rest
    rw [filterCodePoints]
    by_cases hcrlf : c = '\r' ∧ d = '\n'
    · obtain ⟨rfl, rfl⟩ := hcrlf
      rw [if_pos (by decide)]
      exact .crlf ih2
    rw [if_neg (by simpa [CH_CR, CH_LF] using hcrlf)]
    simp only [filterChar]
    by_cases hcr : c = '\r'
    · subst hcr
      have hd : d ≠ '\n' := fun h => hcrlf ⟨rfl, h⟩
      exact .cr (fun r h => hd (List.cons.inj h).1) ih
    by_cases hff : c = '\x0c'
    · subst hff; exact .ff ih
    by_cases hnul : c = '\x00'
    · subst hnul; exact .null ih
    have h1 : (c == CH_CR || c == CH_FF) = false := by
      simp [CH_CR, CH_FF]; exact ⟨hcr, hff⟩
    have h2 : (c == CH_NULL) = false := by simp [CH_NULL]; exact hnul
    rw [h1, h2]
    exact .other ⟨hcr, hff, hnul⟩ ih

/-! ## 先読みの判定 -/

theorem startsValidEscape_iff (l : List Char) :
    startsValidEscape l = true ↔ StartsValidEscape l := by
  unfold StartsValidEscape ValidEscape Newline
  match l with
  | [] => simp [startsValidEscape]
  | [c] => simp [startsValidEscape, CH_BACKSLASH]
  | c :: d :: _ => simp [startsValidEscape, CH_BACKSLASH, CH_LF]

theorem startsIdentSeq_iff (l : List Char) : startsIdentSeq l = true ↔ StartsIdent l := by
  unfold StartsIdent WouldStartIdent
  match l with
  | [] => simp [startsIdentSeq]
  | c :: rest =>
    have hesc := startsValidEscape_iff rest
    have hesc2 := startsValidEscape_iff (c :: rest)
    unfold StartsValidEscape at hesc hesc2
    simp only [startsIdentSeq, CH_HYPHEN, CH_BACKSLASH]
    by_cases hh : c = '-'
    · subst hh
      match rest with
      | [] => simp [ValidEscape, not_identStart_hyphen]
      | d :: r =>
        simp only [beq_self_eq_true, if_true, Bool.or_eq_true, isIdentStart_iff, beq_iff_eq] at *
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at *
        rw [hesc]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl ⟨trivial, Or.inl ⟨d, rfl, Or.inl h⟩⟩
          · exact Or.inl ⟨trivial, Or.inl ⟨d, rfl, Or.inr h⟩⟩
          · exact Or.inl ⟨trivial, Or.inr h⟩
        · rintro (⟨_, ⟨d', hd', h⟩ | h⟩ | ⟨d', hd', h⟩ | ⟨h, _⟩)
          · cases hd'; rcases h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · cases hd'; exact absurd h not_identStart_hyphen
          · cases h
    by_cases hb : c = '\\'
    · subst hb
      have hne : ('\\' == '-') = false := by decide
      simp only [hne, Bool.false_eq_true, if_false, beq_self_eq_true, if_true] at *
      rw [hesc2]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨rfl, h⟩)
      · rintro (⟨h, _⟩ | ⟨d', hd', h⟩ | ⟨_, h⟩)
        · cases h
        · cases hd'; exact absurd h not_identStart_backslash
        · exact h
    · have h1 : (c == '-') = false := by simpa using hh
      have h2 : (c == '\\') = false := by simpa using hb
      simp only [h1, h2, Bool.false_eq_true, if_false, isIdentStart_iff,
        List.getElem?_cons_zero]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨c, rfl, h⟩)
      · rintro (⟨h, _⟩ | ⟨d', hd', h⟩ | ⟨h, _⟩)
        · cases h; exact absurd rfl hh
        · cases hd'; exact h
        · cases h; exact absurd rfl hb

theorem startsNumber_iff (l : List Char) : startsNumber l = true ↔ StartsNumber l := by
  unfold StartsNumber WouldStartNumber DigitAt
  match l with
  | [] => simp [startsNumber]
  | c :: rest =>
    match rest with
    | [] =>
      simp [startsNumber, CH_PLUS, CH_HYPHEN, CH_DOT, isAsciiDigit_iff]
      all_goals by_cases h1 : c = '+' <;> by_cases h2 : c = '-' <;> by_cases h3 : c = '.' <;>
        simp_all [Digit]
    | d :: r =>
      match r with
      | [] =>
        simp [startsNumber, CH_PLUS, CH_HYPHEN, CH_DOT, isAsciiDigit_iff]
        all_goals by_cases h1 : c = '+' <;> by_cases h2 : c = '-' <;> by_cases h3 : c = '.' <;>
          simp_all [Digit]
      | e :: r' =>
        simp [startsNumber, CH_PLUS, CH_HYPHEN, CH_DOT, isAsciiDigit_iff]
        all_goals by_cases h1 : c = '+' <;> by_cases h2 : c = '-' <;> by_cases h3 : c = '.' <;>
          simp_all [Digit]

end Selectors.Spec
