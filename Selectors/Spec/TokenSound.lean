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
theorem ch_plus : CH_PLUS = '+' := by decide
theorem ch_dot : CH_DOT = '.' := by decide
theorem ch_upper_e : CH_UPPER_E = 'E' := by decide
theorem ch_lower_e : CH_LOWER_E = 'e' := by decide
theorem ch_percent : CH_PERCENT = '%' := by decide
theorem ch_lparen : CH_LPAREN = '(' := by decide
theorem ch_comma : CH_COMMA = ',' := by decide
theorem ch_colon : CH_COLON = ':' := by decide
theorem ch_semicolon : CH_SEMICOLON = ';' := by decide
theorem ch_rparen : CH_RPAREN = ')' := by decide
theorem ch_lbracket : CH_LBRACKET = '[' := by decide
theorem ch_rbracket : CH_RBRACKET = ']' := by decide
theorem ch_lbrace : CH_LBRACE = '{' := by decide
theorem ch_rbrace : CH_RBRACE = '}' := by decide
theorem ch_quote : CH_QUOTE = '"' := by decide
theorem ch_apos : CH_APOS = '\'' := by decide
theorem ch_hash : CH_HASH = '#' := by decide
theorem ch_lt : CH_LT = '<' := by decide
theorem ch_at : CH_AT = '@' := by decide
theorem ch_gt : CH_GT = '>' := by decide
theorem ch_bang : CH_BANG = '!' := by decide

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

/-! ## number -/

theorem decimalNumber_foldl : ∀ (l ds : List Char) (v : Nat), DecimalNumber ds v →
    DecimalNumber (ds ++ l) (l.foldl (fun acc c => acc * 10 + (c.toNat - 0x30)) v)
  | [], ds, v, h => by simpa using h
  | d :: l, ds, v, h => by
    have := decimalNumber_foldl l (ds ++ [d]) _ (DecimalNumber.snoc d h)
    simpa [List.foldl_cons] using this

theorem digitsToNat_spec (ds : List Char) : DecimalNumber ds (digitsToNat ds) := by
  simpa [digitsToNat] using decimalNumber_foldl ds [] 0 .nil

theorem digitAt_iff (o : Option Char) :
    (o.map isAsciiDigit).getD false = true ↔ DigitAt o := by
  cases o <;> simp [DigitAt, isAsciiDigit_iff]

theorem digitsAux_spec : ∀ (acc l : List Char),
    (digitsAux acc l).1 = acc.reverse ++ (takeDigits l).1 ∧
      DigitRun l (takeDigits l).1 (takeDigits l).2 ∧ (digitsAux acc l).2 = (takeDigits l).2
  | acc, [] => by simp [digitsAux, takeDigits, DigitRun, DigitAt]
  | acc, c :: rest => by
    by_cases hc : isAsciiDigit c = true
    · obtain ⟨h1, h2, h3⟩ := digitsAux_spec (c :: acc) rest
      obtain ⟨h1', -, h3'⟩ := digitsAux_spec [c] rest
      have hd1 : (digitsAux acc (c :: rest)).1 = (digitsAux (c :: acc) rest).1 := by
        rw [digitsAux, if_pos hc]
      have ht1 : (takeDigits (c :: rest)).1 = (digitsAux [c] rest).1 := by
        simp only [takeDigits]; rw [digitsAux, if_pos hc]
      have hd2 : (digitsAux acc (c :: rest)).2 = (digitsAux (c :: acc) rest).2 := by
        rw [digitsAux, if_pos hc]
      have ht2 : (takeDigits (c :: rest)).2 = (digitsAux [c] rest).2 := by
        simp only [takeDigits]; rw [digitsAux, if_pos hc]
      obtain ⟨hs, ha, hm⟩ := h2
      refine ⟨by rw [hd1, ht1, h1, h1']; simp, ⟨?_, ?_, ?_⟩, by rw [hd2, ht2, h3, h3']⟩
      · rw [ht1, ht2, h1', h3']
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append]
        exact congrArg _ hs
      · rw [ht1, h1']; intro d hd; simp at hd
        rcases hd with rfl | hd
        · exact (isAsciiDigit_iff _).mp hc
        · exact ha d hd
      · rw [ht2, h3']; exact hm
    · have hn : ¬ DigitAt (c :: rest)[0]? := by
        rintro ⟨d, hd, hdd⟩; simp at hd; subst hd; exact hc ((isAsciiDigit_iff _).mpr hdd)
      simp [digitsAux, takeDigits, hc, DigitRun]
      exact hn

theorem takeDigits_spec (l : List Char) : DigitRun l (takeDigits l).1 (takeDigits l).2 :=
  (digitsAux_spec [] l).2.1

theorem takeSign_spec (l : List Char) : SignPart l (takeSign l).1 (takeSign l).2 := by
  match l with
  | [] => exact Or.inr ⟨by simp, by simp, rfl, rfl⟩
  | c :: rest =>
    by_cases hs : (c == CH_PLUS || c == CH_HYPHEN) = true
    · rw [takeSign, if_pos hs]
      have : c = '+' ∨ c = '-' := by simpa [ch_plus, ch_hyphen] using hs
      exact Or.inl ⟨c, rfl, this, rfl⟩
    · rw [takeSign, if_neg hs]
      have : c ≠ '+' ∧ c ≠ '-' := by simpa [ch_plus, ch_hyphen] using hs
      exact Or.inr ⟨by simpa using this.1, by simpa using this.2, rfl, rfl⟩

theorem takeFraction_spec (l : List Char) :
    FractionPart l (takeFraction l).1 (takeFraction l).2 := by
  match l with
  | c :: d :: rest =>
    by_cases h : (c == CH_DOT && isAsciiDigit d) = true
    · rw [takeFraction, if_pos h]
      simp only [Bool.and_eq_true, beq_iff_eq, ch_dot] at h
      obtain ⟨rfl, hd⟩ := h
      refine Or.inl ⟨d :: rest, (takeDigits (d :: rest)).1,
        ⟨by simp, ⟨d, by simp, (isAsciiDigit_iff _).mp hd⟩⟩, rfl, ?_, rfl⟩
      exact takeDigits_spec _
    · rw [takeFraction, if_neg h]
      refine Or.inr ⟨?_, rfl, rfl⟩
      rintro ⟨h1, ⟨x, hx, hxd⟩⟩
      simp at h1 hx; subst h1 hx
      exact h (by simp [ch_dot, (isAsciiDigit_iff _).mpr hxd])
  | [] => exact Or.inr ⟨by simp [FractionStart], rfl, rfl⟩
  | [c] => exact Or.inr ⟨by simp [FractionStart, DigitAt], rfl, rfl⟩

theorem takeExponent_spec (l : List Char) :
    ExponentPart l (takeExponent l).1 (takeExponent l).2 := by
  match l with
  | [] => exact Or.inr ⟨by simp [ExponentStart], rfl, rfl⟩
  | c :: rest =>
    by_cases he : (c == CH_UPPER_E || c == CH_LOWER_E) = true
    · have he' : c = 'E' ∨ c = 'e' := by simpa [ch_upper_e, ch_lower_e] using he
      have hstart0 : (c :: rest)[0]? = some 'E' ∨ (c :: rest)[0]? = some 'e' := by
        rcases he' with rfl | rfl <;> simp
      by_cases hd : (rest.head?.map isAsciiDigit).getD false = true
      · rw [takeExponent, if_pos he, if_pos hd]
        have hd' : DigitAt rest[0]? := by
          rw [← digitAt_iff]; cases rest <;> simp_all
        have hns : rest[0]? ≠ some '+' ∧ rest[0]? ≠ some '-' := by
          obtain ⟨x, hx, hxd⟩ := hd'
          rw [hx]; constructor <;> intro h <;> simp at h <;> subst h <;>
            simp [Digit] at hxd
        exact Or.inl ⟨c, rest, rest, (takeDigits rest).1,
          ⟨hstart0, Or.inl (by simpa using hd')⟩, rfl, Or.inr ⟨hns.1, hns.2, rfl⟩,
          takeDigits_spec rest, rfl⟩
      · by_cases hs : ((rest.head?.map (fun d => d == CH_PLUS || d == CH_HYPHEN)).getD false
            && (rest.tail.head?.map isAsciiDigit).getD false) = true
        · rw [takeExponent, if_pos he, if_neg hd, if_pos hs]
          simp only [Bool.and_eq_true] at hs
          obtain ⟨hs1, hs2⟩ := hs
          have hsg : rest[0]? = some '+' ∨ rest[0]? = some '-' := by
            cases rest <;> simp_all [ch_plus, ch_hyphen]
          have hd2 : DigitAt rest[1]? := by
            rw [← digitAt_iff]; cases rest with
            | nil => simp at hs1
            | cons x t => cases t <;> simp_all
          exact Or.inl ⟨c, rest, rest.tail, (takeDigits rest.tail).1,
            ⟨hstart0, Or.inr ⟨by simpa using hsg, by simpa using hd2⟩⟩, rfl,
            Or.inl ⟨hsg, rfl⟩, takeDigits_spec _, rfl⟩
        · rw [takeExponent, if_pos he, if_neg hd, if_neg hs]
          refine Or.inr ⟨?_, rfl, rfl⟩
          rintro ⟨-, h | ⟨hsg, hd2⟩⟩
          · apply hd; rw [digitAt_iff]; cases rest <;> simp_all
          · apply hs
            cases rest with
            | nil => simp at hsg
            | cons x t =>
              cases t with
              | nil => simp [DigitAt] at hd2
              | cons y u =>
                simp at hsg hd2 ⊢
                refine ⟨by rcases hsg with rfl | rfl <;> simp [ch_plus, ch_hyphen], ?_⟩
                exact (isAsciiDigit_iff _).mpr (by obtain ⟨z, hz, hzd⟩ := hd2; cases hz; exact hzd)
    · rw [takeExponent, if_neg he]
      refine Or.inr ⟨?_, rfl, rfl⟩
      rintro ⟨h, -⟩
      apply he
      rcases h with h | h <;> simp at h <;> subst h <;> simp [ch_upper_e, ch_lower_e]

/-- **`consumeNumber` は `Number` を満たす。** -/
theorem consumeNumber_spec (l : List Char) :
    Number l (consumeNumber l).1 (consumeNumber l).2 := by
  refine ⟨(takeSign l).1, (takeSign l).2, (takeDigits (takeSign l).2).1,
    (takeDigits (takeSign l).2).2, (takeFraction (takeDigits (takeSign l).2).2).1,
    (takeFraction (takeDigits (takeSign l).2).2).2,
    (takeExponent (takeFraction (takeDigits (takeSign l).2).2).2).1,
    digitsToNat (takeDigits (takeSign l).2).1,
    takeSign_spec l, takeDigits_spec _, takeFraction_spec _, takeExponent_spec _,
    digitsToNat_spec _, ?_⟩
  simp only [consumeNumber, ch_hyphen]
  congr 1
  by_cases h : (takeSign l).1 = some '-' <;> simp [h]

/-! ## numeric token・ident-like token -/

/-- **`consumeNumericToken` は `NumericTok` を満たす。** -/
theorem consumeNumericToken_spec (l : List Char) :
    NumericTok l (consumeNumericToken l).1 (consumeNumericToken l).2 := by
  refine ⟨(consumeNumber l).1, (consumeNumber l).2, consumeNumber_spec l, ?_⟩
  generalize hr : (consumeNumber l).2 = r
  by_cases hi : startsIdentSeq r = true
  · left
    refine ⟨(startsIdentSeq_iff r).mp hi, (consumeIdentSeq r).1, ?_, ?_⟩
    · simp only [consumeNumericToken, hr, hi, if_true]; exact consumeIdentSeq_spec r
    · simp [consumeNumericToken, hr, hi]
  · have hi' : ¬ StartsIdent r := fun h => hi ((startsIdentSeq_iff r).mpr h)
    by_cases hp : (r.head?.map (fun c => c == CH_PERCENT)).getD false = true
    · right; left
      match r, hp with
      | x :: t, hp =>
        have hx : x = '%' := by simpa [ch_percent] using hp
        subst hx
        refine ⟨hi', ?_, ?_⟩
        · simp [consumeNumericToken, hr, hi, ch_percent]
        · simp [consumeNumericToken, hr, hi, ch_percent]
    · right; right
      refine ⟨hi', ?_, ?_, ?_⟩
      · intro h; apply hp; cases r <;> simp_all [ch_percent]
      · simp only [consumeNumericToken, hr]; simp [hi, hp]
      · simp only [consumeNumericToken, hr]; simp [hi, hp]

/-- **`consumeIdentLike` は `IdentLikeTok` を満たす。** -/
theorem consumeIdentLike_spec (l : List Char) :
    IdentLikeTok l (consumeIdentLike l).1 (consumeIdentLike l).2 := by
  refine ⟨(consumeIdentSeq l).1, (consumeIdentSeq l).2, consumeIdentSeq_spec l, ?_⟩
  generalize hr : (consumeIdentSeq l).2 = r
  by_cases hp : (r.head?.map (fun c => c == CH_LPAREN)).getD false = true
  · left
    match r, hp with
    | x :: t, hp =>
      have hx : x = '(' := by simpa [ch_lparen] using hp
      subst hx
      refine ⟨?_, ?_⟩
      · simp [consumeIdentLike, hr, ch_lparen]
      · simp [consumeIdentLike, hr, ch_lparen]
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply hp; cases r <;> simp_all [ch_lparen]
    · simp only [consumeIdentLike, hr]; simp [hp]
    · simp only [consumeIdentLike, hr]; simp [hp]

/-! ## token を一つ読む -/

theorem skipWhitespace_spec : ∀ l : List Char, WhitespaceRun l (skipWhitespace l)
  | [] => ⟨[], by simp [skipWhitespace], by simp, by simp [skipWhitespace]⟩
  | c :: rest => by
    by_cases hc : isWhitespace c = true
    · obtain ⟨ws, h1, h2, h3⟩ := skipWhitespace_spec rest
      refine ⟨c :: ws, ?_, ?_, ?_⟩
      · rw [skipWhitespace, if_pos hc]; simp [← h1]
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · exact (isWhitespace_iff _).mp hc
        · exact h2 w hw
      · rw [skipWhitespace, if_pos hc]; exact h3
    · refine ⟨[], by rw [skipWhitespace, if_neg hc]; simp, by simp, ?_⟩
      rw [skipWhitespace, if_neg hc]
      intro x hx; simp at hx; subst hx
      exact fun h => hc ((isWhitespace_iff _).mpr h)


set_option linter.unusedSimpArgs false in
theorem simpleToken_iff (c : Char) (t : Token) : simpleToken c = some t ↔ Punct c t := by
  constructor
  · intro h
    by_cases h0 : c = ','
    · subst h0; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .comma
    by_cases h1 : c = ':'
    · subst h1; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .colon
    by_cases h2 : c = ';'
    · subst h2; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .semicolon
    by_cases h3 : c = '('
    · subst h3; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .lparen
    by_cases h4 : c = ')'
    · subst h4; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .rparen
    by_cases h5 : c = '['
    · subst h5; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .lbracket
    by_cases h6 : c = ']'
    · subst h6; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .rbracket
    by_cases h7 : c = '{'
    · subst h7; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .lbrace
    by_cases h8 : c = '}'
    · subst h8; simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace] at h; subst h; exact .rbrace
    simp [simpleToken, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, h0, h1, h2, h3, h4, h5, h6, h7, h8] at h
  · intro h; cases h <;> rfl


theorem startsCdc_iff (l : List Char) : startsCdc l = true ↔ ∃ r, l = '-' :: '>' :: r := by
  match l with
  | [] => simp [startsCdc]
  | [x] => simp [startsCdc]
  | x :: y :: r => simp [startsCdc, ch_hyphen, ch_gt]

theorem startsCdo_iff (l : List Char) : startsCdo l = true ↔ ∃ r, l = '!' :: '-' :: '-' :: r := by
  match l with
  | [] => simp [startsCdo]
  | [x] => simp [startsCdo]
  | [x, y] => simp [startsCdo]
  | x :: y :: z :: r => simp [startsCdo, ch_hyphen, ch_bang, and_assoc]

theorem hashCond_iff (rest : List Char) :
    ((rest.head?.map isIdentChar).getD false || startsValidEscape rest) = true ↔
      ((∃ x, rest[0]? = some x ∧ IdentCp x) ∨ StartsValidEscape rest) := by
  rw [Bool.or_eq_true, startsValidEscape_iff]
  cases rest <;> simp [isIdentChar_iff]

/-- **`tokenAt` は `TokenAt` を満たす。** -/
theorem tokenAt_spec (c : Char) (rest : List Char) :
    TokenAt c rest (tokenAt c rest).1 (tokenAt c rest).2 := by
  rw [tokenAt]
  split
  · next hw => exact .whitespace ((isWhitespace_iff c).mp hw) (skipWhitespace_spec rest)
  next hw =>
  split
  · next hq =>
    have : c = '"' ∨ c = '\'' := by simpa [ch_quote, ch_apos] using hq
    exact .string this (stringAux_tok_spec c rest)
  next hq =>
  split
  · next t ht => exact .punct ((simpleToken_iff c t).mp ht)
  next hnone =>
  have hp : ∀ t, ¬ Punct c t := fun t h => by
    rw [(simpleToken_iff c t).mpr h] at hnone; simp at hnone
  split
  · next hh =>
    have : c = '#' := by simpa [ch_hash] using hh
    subst this
    split
    · next hcond =>
      exact .hash ((hashCond_iff rest).mp hcond) (startsIdentSeq_iff rest)
        (consumeIdentSeq_spec rest)
    · next hcond => exact .hashDelim (fun h => hcond ((hashCond_iff rest).mpr h))
  next hh =>
  split
  · next hpd =>
    have hpd' : c = '+' ∨ c = '.' := by simpa [ch_plus, ch_dot] using hpd
    split
    · next hn =>
      exact .numericSign (by rcases hpd' with h | h <;> simp [h]) ((startsNumber_iff _).mp hn)
        (consumeNumericToken_spec _)
    · next hn => exact .signDelim hpd' (fun h => hn ((startsNumber_iff _).mpr h))
  next hpd =>
  split
  · next hy =>
    have : c = '-' := by simpa [ch_hyphen] using hy
    subst this
    split
    · next hn =>
      exact .numericSign (by simp) ((startsNumber_iff _).mp hn) (consumeNumericToken_spec _)
    · next hn =>
      have hn' : ¬ StartsNumber ('-' :: rest) := fun h => hn ((startsNumber_iff _).mpr h)
      split
      · next hcdc =>
        obtain ⟨r, rfl⟩ := (startsCdc_iff rest).mp hcdc
        exact .cdc hn'
      · next hcdc =>
        have hc' : ¬ ∃ r, rest = '-' :: '>' :: r := fun h => hcdc ((startsCdc_iff rest).mpr h)
        split
        · next hi =>
          exact .hyphenIdent hn' hc' ((startsIdentSeq_iff _).mp hi) (consumeIdentLike_spec _)
        · next hi => exact .hyphenDelim hn' hc' (fun h => hi ((startsIdentSeq_iff _).mpr h))
  next hy =>
  split
  · next hl =>
    have : c = '<' := by simpa [ch_lt] using hl
    subst this
    split
    · next hcdo =>
      obtain ⟨r, rfl⟩ := (startsCdo_iff rest).mp hcdo
      exact .cdo
    · next hcdo => exact .ltDelim (fun h => hcdo ((startsCdo_iff rest).mpr h))
  next hl =>
  split
  · next ha =>
    have : c = '@' := by simpa [ch_at] using ha
    subst this
    split
    · next hi => exact .atKeyword ((startsIdentSeq_iff _).mp hi) (consumeIdentSeq_spec rest)
    · next hi => exact .atDelim (fun h => hi ((startsIdentSeq_iff _).mpr h))
  next ha =>
  split
  · next hb =>
    have : c = '\\' := by simpa [ch_backslash] using hb
    subst this
    split
    · next hv => exact .backslashIdent ((startsValidEscape_iff _).mp hv) (consumeIdentLike_spec _)
    · next hv => exact .backslashDelim (fun h => hv ((startsValidEscape_iff _).mpr h))
  next hb =>
  split
  · next hd => exact .digit ((isAsciiDigit_iff c).mp hd) (consumeNumericToken_spec _)
  next hd =>
  split
  · next hi => exact .identStart ((isIdentStart_iff c).mp hi) (consumeIdentLike_spec _)
  next hi =>
  refine .other ⟨fun h => hw ((isWhitespace_iff c).mpr h),
    fun h => hd ((isAsciiDigit_iff c).mpr h), fun h => hi ((isIdentStart_iff c).mpr h), ?_⟩
  simp only [ch_quote, ch_apos, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at,
    ch_backslash, Bool.or_eq_true, beq_iff_eq, not_or] at hq hh hpd hy hl ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨hq.1, hh, hq.2, fun h => by subst h; exact hp _ Punct.lparen, fun h => by subst h; exact hp _ Punct.rparen, hpd.1,
    fun h => by subst h; exact hp _ Punct.comma, hy, hpd.2, fun h => by subst h; exact hp _ Punct.colon,
    fun h => by subst h; exact hp _ Punct.semicolon, hl, ha, fun h => by subst h; exact hp _ Punct.lbracket, hb,
    fun h => by subst h; exact hp _ Punct.rbracket, fun h => by subst h; exact hp _ Punct.lbrace, fun h => by subst h; exact hp _ Punct.rbrace⟩

/-! ## token 列 -/

theorem tokenizeAux_spec (acc : List Token) (l : List Char) :
    ∃ ts, tokenizeAux acc l = acc.reverse ++ ts ∧ Tokenizes l ts := by
  induction acc, l using tokenizeAux.induct with
  | case1 acc l h =>
    refine ⟨[], ?_, ?_⟩
    · rw [tokenizeAux]; split
      · simp
      · next heq => rw [h] at heq; cases heq
    · unfold nextToken at h
      split at h
      · next hs => exact .eof (hs ▸ skipComments_spec l)
      · cases h
  | case2 acc l t r h ih =>
    obtain ⟨ts, h1, h2⟩ := ih
    refine ⟨t :: ts, ?_, ?_⟩
    · rw [tokenizeAux]; split
      · next heq => rw [h] at heq; cases heq
      · next t' r' heq =>
        rw [h] at heq; cases heq
        rw [h1]; simp
    · unfold nextToken at h
      split at h
      · cases h
      · next c rest hs =>
        simp only [Option.some.injEq] at h
        have ht := tokenAt_spec c rest
        rw [h] at ht
        exact .step (hs ▸ skipComments_spec l) ht h2

/-- **`tokenize` は `TokenizesInput` を満たす。** -/
theorem tokenize_spec (input : String) : TokenizesInput input (tokenize input) := by
  obtain ⟨ts, h1, h2⟩ := tokenizeAux_spec [] (filterCodePoints input.toList)
  refine ⟨filterCodePoints input.toList, filterCodePoints_spec _, ?_⟩
  unfold tokenize; rw [h1]; simpa using h2

end Selectors.Spec
