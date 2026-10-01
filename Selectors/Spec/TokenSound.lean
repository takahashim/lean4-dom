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
theorem ch_backslash : CH_BACKSLASH = '\\' := by decide
theorem ch_star : CH_STAR = '*' := by decide
theorem ch_slash : CH_SLASH = '/' := by decide

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


/-! ## escape -/

theorem hexValue_of_hexDigit {c : Char} (h : HexDigit c) : hexValue c = some (HexDigitValue c) := by
  unfold HexDigit Digit at h
  unfold hexValue HexDigitValue
  by_cases h1 : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39
  · simp [h1]
  by_cases h2 : 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46
  · simp [h1, h2]
  have h3 : 0x61 ≤ c.toNat ∧ c.toNat ≤ 0x66 := by omega
  simp [h1, h2, h3]

theorem hexNumber_foldl : ∀ (l ds : List Char) (v : Nat), HexNumber ds v →
    (∀ d ∈ l, HexDigit d) →
    HexNumber (ds ++ l) (l.foldl (fun acc c => acc * 16 + (hexValue c).getD 0) v)
  | [], ds, v, h, _ => by simpa using h
  | d :: l, ds, v, h, hall => by
    have hd := hall d (by simp)
    have h' : HexNumber (ds ++ [d]) (v * 16 + (hexValue d).getD 0) := by
      rw [hexValue_of_hexDigit hd]; exact HexNumber.snoc d h
    have := hexNumber_foldl l (ds ++ [d]) _ h' (fun x hx => hall x (by simp [hx]))
    simpa [List.foldl_cons] using this

theorem hexNumber_spec (ds : List Char) (h : ∀ d ∈ ds, HexDigit d) :
    HexNumber ds (hexNumber ds) := by
  simpa [hexNumber] using hexNumber_foldl ds [] 0 .nil h

theorem escapedCodePoint_spec (n : Nat) : EscapedValue n (escapedCodePoint n) := by
  unfold escapedCodePoint
  by_cases h : n = 0 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) ∨ 0x10FFFF < n
  · have : (n == 0 || 0x10FFFF < n || (0xD800 <= n && n <= 0xDFFF)) = true := by
      simp; omega
    rw [if_pos this]
    exact .replacement h
  · have : (n == 0 || 0x10FFFF < n || (0xD800 <= n && n <= 0xDFFF)) = false := by
      simp; omega
    rw [if_neg (by simp [this])]
    refine .scalar h ?_
    have hv : n.isValidChar := by unfold Nat.isValidChar; omega
    simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem takeHex_spec : ∀ (n : Nat) (l : List Char),
    l = (takeHex n l).1 ++ (takeHex n l).2 ∧ (takeHex n l).1.length ≤ n ∧
      (∀ d ∈ (takeHex n l).1, HexDigit d) ∧
      ((takeHex n l).1.length = n ∨ ∀ d, (takeHex n l).2[0]? = some d → ¬ HexDigit d)
  | 0, l => by simp [takeHex]
  | _ + 1, [] => by simp [takeHex]
  | n + 1, c :: rest => by
    by_cases hc : isAsciiHexDigit c = true
    · obtain ⟨h1, h2, h3, h4⟩ := takeHex_spec n rest
      simp only [takeHex, hc, if_true]
      refine ⟨by simp; exact h1, by simp; omega, ?_, ?_⟩
      · intro d hd
        simp at hd
        rcases hd with rfl | hd
        · exact (isAsciiHexDigit_iff _).mp hc
        · exact h3 d hd
      · rcases h4 with h4 | h4
        · left; simp [h4]
        · right; exact h4
    · simp only [takeHex, hc, Bool.false_eq_true, if_false]
      refine ⟨by simp, by simp, by simp, Or.inr ?_⟩
      intro d hd
      simp at hd; subst hd
      exact fun h => hc ((isAsciiHexDigit_iff _).mpr h)

/-- **`consumeEscape` は `Escape` を満たす。** -/
theorem consumeEscape_spec (l : List Char) :
    Escape l (consumeEscape l).1 (consumeEscape l).2 := by
  match l with
  | [] => exact .eof
  | c :: rest =>
    by_cases hc : isAsciiHexDigit c = true
    · obtain ⟨h1, h2, h3, h4⟩ := takeHex_spec 5 rest
      have hall : ∀ d ∈ c :: (takeHex 5 rest).1, HexDigit d := by
        intro d hd; simp at hd
        rcases hd with rfl | hd
        · exact (isAsciiHexDigit_iff _).mp hc
        · exact h3 d hd
      have hmax : (c :: (takeHex 5 rest).1).length = 6 ∨
          ∀ d, (takeHex 5 rest).2[0]? = some d → ¬ HexDigit d := by
        rcases h4 with h4 | h4
        · left; simp [h4]
        · right; exact h4
      have hsplit : c :: rest = (c :: (takeHex 5 rest).1) ++ (takeHex 5 rest).2 := by
        simp; exact h1
      have hv := hexNumber_spec _ hall
      simp only [consumeEscape, hc, if_true]
      generalize hT : takeHex 5 rest = T at *
      obtain ⟨ds, r⟩ := T
      simp only at hsplit hall hmax hv h2 ⊢
      match r with
      | [] =>
        simp only
        exact .hex hsplit (by simp) (by simp; omega) hall hmax (Or.inr ⟨by simp, rfl⟩) hv
          (escapedCodePoint_spec _)
      | w :: r' =>
        simp only
        by_cases hw : isWhitespace w = true
        · rw [if_pos hw]
          exact .hex hsplit (by simp) (by simp; omega) hall hmax
            (Or.inl ⟨w, rfl, (isWhitespace_iff w).mp hw⟩) hv (escapedCodePoint_spec _)
        · rw [if_neg hw]
          refine .hex hsplit (by simp) (by simp; omega) hall hmax (Or.inr ⟨?_, rfl⟩) hv
            (escapedCodePoint_spec _)
          intro x hx; simp at hx; subst hx
          exact fun h => hw ((isWhitespace_iff _).mpr h)
    · simp only [consumeEscape, hc, Bool.false_eq_true, if_false]
      exact .other (fun h => hc ((isAsciiHexDigit_iff _).mpr h))

/-! ## ident sequence -/

theorem backslash_of_startsValidEscape {c : Char} {rest : List Char}
    (h : startsValidEscape (c :: rest) = true) : c = '\\' := by
  have := (startsValidEscape_iff _).mp h
  unfold StartsValidEscape ValidEscape at this
  simpa using this.1

theorem identSeqAux_spec (acc l : List Char) :
    ∃ r, (identSeqAux acc l).1 = acc.reverse ++ r ∧ IdentSeq l r (identSeqAux acc l).2 := by
  induction acc, l using identSeqAux.induct with
  | case1 acc =>
    refine ⟨[], by simp [identSeqAux], ?_⟩
    rw [identSeqAux]
    exact .stop (by simp) (by simp [StartsValidEscape, ValidEscape])
  | case2 acc c rest hc ih =>
    obtain ⟨r, h1, h2⟩ := ih
    refine ⟨c :: r, ?_, ?_⟩
    · rw [identSeqAux, if_pos hc, h1]; simp
    · rw [identSeqAux, if_pos hc]
      exact .cp ((isIdentChar_iff c).mp hc) h2
  | case3 acc c rest hc hesc ih =>
    obtain ⟨r, h1, h2⟩ := ih
    have hb := backslash_of_startsValidEscape hesc
    refine ⟨(consumeEscape rest).1 :: r, ?_, ?_⟩
    · rw [identSeqAux, if_neg hc, if_pos hesc, h1]; simp
    · rw [identSeqAux, if_neg hc, if_pos hesc]
      subst hb
      exact .escape ((startsValidEscape_iff _).mp hesc) (consumeEscape_spec rest) h2
  | case4 acc c rest hc hesc =>
    refine ⟨[], ?_, ?_⟩
    · rw [identSeqAux, if_neg hc, if_neg hesc]; simp
    · rw [identSeqAux, if_neg hc, if_neg hesc]
      refine .stop ?_ (fun h => hesc ((startsValidEscape_iff _).mpr h))
      intro x hx; simp at hx; subst hx
      exact fun h => hc ((isIdentChar_iff _).mpr h)

/-- **`consumeIdentSeq` は `IdentSeq` を満たす。** -/
theorem consumeIdentSeq_spec (l : List Char) :
    IdentSeq l (consumeIdentSeq l).1 (consumeIdentSeq l).2 := by
  obtain ⟨r, h1, h2⟩ := identSeqAux_spec [] l
  unfold consumeIdentSeq
  rw [h1]; simpa using h2

/-! ## string token -/

theorem stringAux_spec (e : Char) (acc l : List Char) :
    ∃ v b, StringRun e l v b (stringAux e acc l).2 ∧
      (stringAux e acc l).1 =
        if b then Token.badString else Token.string (String.ofList (acc.reverse ++ v)) := by
  induction acc, l using stringAux.induct e with
  | case1 acc =>
    exact ⟨[], false, by rw [stringAux]; exact .eof, by simp [stringAux]⟩
  | case2 acc d tail he =>
    have : d = e := by simpa using he
    subst this
    exact ⟨[], false, by rw [stringAux, if_pos he]; exact .close, by simp [stringAux]⟩
  | case3 acc d tail he hlf =>
    have hd : d = '\n' := by simpa [ch_lf] using hlf
    subst hd
    have he' : '\n' ≠ e := by simpa using he
    exact ⟨[], true, by rw [stringAux, if_neg he, if_pos hlf]; exact .newline he',
      by simp [stringAux, he, hlf]⟩
  | case4 acc d tail he hlf hbs hemp =>
    have hd : d = '\\' := by simpa [ch_backslash] using hbs
    have ht : tail = [] := by simpa using hemp
    subst hd ht
    have he' : '\\' ≠ e := by simpa using he
    refine ⟨[], false, ?_, by simp [stringAux, he, hlf, hbs]⟩
    rw [stringAux, if_neg he, if_neg hlf, if_pos hbs, if_pos hemp]
    exact .backslashEof he'
  | case5 acc d tail he hlf hbs hemp hnl ih =>
    have hd : d = '\\' := by simpa [ch_backslash] using hbs
    subst hd
    have he' : '\\' ≠ e := by simpa using he
    obtain ⟨v, b, h1, h2⟩ := ih
    match tail, hemp, hnl with
    | x :: t, _, hnl =>
      have hx : x = '\n' := by simpa [ch_lf] using hnl
      subst hx
      refine ⟨v, b, ?_, ?_⟩
      · rw [stringAux, if_neg he, if_neg hlf, if_pos hbs, if_neg (by simp), if_pos hnl]
        exact .backslashNewline he' h1
      · rw [stringAux, if_neg he, if_neg hlf, if_pos hbs, if_neg (by simp), if_pos hnl]
        exact h2
  | case6 acc d tail he hlf hbs hemp hnl ih =>
    have hd : d = '\\' := by simpa [ch_backslash] using hbs
    subst hd
    have he' : '\\' ≠ e := by simpa using he
    obtain ⟨v, b, h1, h2⟩ := ih
    match tail, hemp, hnl, h1, h2 with
    | x :: t, _, hnl, h1, h2 =>
      have hx : x ≠ '\n' := by simpa [ch_lf] using hnl
      refine ⟨(consumeEscape (x :: t)).1 :: v, b, ?_, ?_⟩
      · rw [stringAux, if_neg he, if_neg hlf, if_pos hbs, if_neg (by simp), if_neg hnl]
        exact .backslashEscape he' hx (consumeEscape_spec _) h1
      · rw [stringAux, if_neg he, if_neg hlf, if_pos hbs, if_neg (by simp), if_neg hnl, h2]
        simp
  | case7 acc d tail he hlf hbs ih =>
    obtain ⟨v, b, h1, h2⟩ := ih
    refine ⟨d :: v, b, ?_, ?_⟩
    · rw [stringAux, if_neg he, if_neg hlf, if_neg hbs]
      exact .other (by simpa using he) (by simpa [ch_lf] using hlf)
        (by simpa [ch_backslash] using hbs) h1
    · rw [stringAux, if_neg he, if_neg hlf, if_neg hbs, h2]
      simp

/-- **string token の読み取りは `StringTok` を満たす。** -/
theorem stringAux_tok_spec (e : Char) (l : List Char) :
    StringTok e l (stringAux e [] l).1 (stringAux e [] l).2 := by
  obtain ⟨v, b, h1, h2⟩ := stringAux_spec e [] l
  exact ⟨v, b, h1, by simpa using h2⟩

/-! ## comment -/

theorem noCommentEnd_cons {c : Char} {l : List Char} (hl : NoCommentEnd l)
    (hc : c = '*' → ∀ t, l ≠ '/' :: t) : NoCommentEnd (c :: l) := by
  intro x y h
  match x with
  | [] =>
    simp at h
    exact hc h.1 y h.2
  | x0 :: x' =>
    simp at h
    exact hl x' y h.2

theorem skipCommentBody_spec (l : List Char) : CommentBody l (skipCommentBody l) := by
  induction l using skipCommentBody.induct with
  | case1 => exact Or.inr ⟨fun x y h => by simp at h, by simp [skipCommentBody]⟩
  | case2 c =>
    refine Or.inr ⟨fun x y h => ?_, by simp [skipCommentBody]⟩
    match x with
    | [] => simp at h
    | _ :: x' => simp at h
  | case3 c d rest h =>
    rw [skipCommentBody, if_pos h]
    simp only [Bool.and_eq_true, beq_iff_eq, ch_star, ch_slash] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨[], rfl, fun x y h => by simp at h⟩
  | case4 c d rest h ih =>
    rw [skipCommentBody, if_neg h]
    simp only [Bool.and_eq_true, beq_iff_eq, ch_star, ch_slash] at h
    have hc : c = '*' → ∀ t, (d :: rest) ≠ '/' :: t := fun hc t ht =>
      h ⟨hc, (List.cons.inj ht).1⟩
    generalize hS : skipCommentBody (d :: rest) = S at *
    rcases ih with ⟨pre, hpre, hno⟩ | ⟨hno, hr⟩
    · refine Or.inl ⟨c :: pre, by simp [hpre], noCommentEnd_cons hno ?_⟩
      intro hc' t ht
      apply hc hc' (t ++ '*' :: '/' :: S)
      rw [hpre, ht]; simp
    · exact Or.inr ⟨noCommentEnd_cons hno hc, hr⟩

/-- **`skipComments` は `Comments` を満たす。** -/
theorem skipComments_spec (l : List Char) : Comments l (skipComments l) := by
  induction l using skipComments.induct with
  | case1 => rw [skipComments]; exact .done (fun r h => nomatch h)
  | case2 c => rw [skipComments]; exact .done (fun r h => by simp at h)
  | case3 c d rest h ih =>
    rw [skipComments, if_pos h]
    simp only [Bool.and_eq_true, beq_iff_eq, ch_star, ch_slash] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .comment (skipCommentBody_spec rest) ih
  | case4 c d rest h =>
    rw [skipComments, if_neg h]
    simp only [Bool.and_eq_true, beq_iff_eq, ch_star, ch_slash] at h
    exact .done (fun r hr => by simp at hr; exact h ⟨hr.1, hr.2.1⟩)

end Selectors.Spec
