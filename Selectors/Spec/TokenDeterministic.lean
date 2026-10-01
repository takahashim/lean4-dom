import Selectors.Spec.Token
import Selectors.Spec.TokenSound

/-!
# tokenizer の関係仕様は決定的である

`Selectors/Spec/Token.lean` の各関係は入力の形で規則が排他なので、結果を一意に決める。
`Selectors/Spec/TokenSound.lean` と合わせると、関係が実行関数を特徴づける。
-/

namespace Selectors.Spec

open Selectors Infra

/-- `Preprocessed` は結果を一意に決める。 -/
theorem Preprocessed.deterministic : ∀ {l o1 o2 : List Char},
    Preprocessed l o1 → Preprocessed l o2 → o1 = o2
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .crlf h1, .crlf h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .crlf _, .cr hn _ => absurd rfl (hn _)
  | _, _, _, .cr hn _, .crlf _ => absurd rfl (hn _)
  | _, _, _, .cr _ h1, .cr _ h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .ff h1, .ff h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .null h1, .null h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .other _ h1, .other _ h2 => by rw [Preprocessed.deterministic h1 h2]
  | _, _, _, .crlf _, .other hc _ => absurd rfl hc.1
  | _, _, _, .other hc _, .crlf _ => absurd rfl hc.1
  | _, _, _, .cr _ _, .other hc _ => absurd rfl hc.1
  | _, _, _, .other hc _, .cr _ _ => absurd rfl hc.1
  | _, _, _, .ff _, .other hc _ => absurd rfl hc.2.1
  | _, _, _, .other hc _, .ff _ => absurd rfl hc.2.1
  | _, _, _, .null _, .other hc _ => absurd rfl hc.2.2
  | _, _, _, .other hc _, .null _ => absurd rfl hc.2.2

/-- **前処理の関係と実行関数は一致する。** -/
theorem Preprocessed.eq_filterCodePoints_iff {l out : List Char} :
    Preprocessed l out ↔ out = filterCodePoints l :=
  ⟨fun h => Preprocessed.deterministic h (filterCodePoints_spec l),
   fun h => h ▸ filterCodePoints_spec l⟩


/-! ## escape -/

theorem HexNumber.deterministic_aux {a b : List Char} {v1 v2 : Nat}
    (h1 : HexNumber a v1) (h2 : HexNumber b v2) (hab : a = b) : v1 = v2 := by
  induction h1 generalizing b v2 with
  | nil =>
    cases h2 with
    | nil => rfl
    | snoc d h => simp at hab
  | snoc d h ih =>
    cases h2 with
    | nil => simp at hab
    | snoc d' h' =>
      obtain ⟨hds, hd⟩ := List.append_inj' hab rfl
      simp at hd
      subst hd
      rw [ih h' hds]

theorem HexNumber.deterministic {ds : List Char} {v1 v2 : Nat}
    (h1 : HexNumber ds v1) (h2 : HexNumber ds v2) : v1 = v2 :=
  HexNumber.deterministic_aux h1 h2 rfl

theorem EscapedValue.deterministic {v : Nat} {c1 c2 : Char}
    (h1 : EscapedValue v c1) (h2 : EscapedValue v c2) : c1 = c2 := by
  cases h1 with
  | replacement h => cases h2 with
    | replacement _ => rfl
    | scalar hn _ => exact absurd h hn
  | scalar hn hc => cases h2 with
    | replacement h => exact absurd h hn
    | scalar _ hc' => exact Char.toNat_inj.mp (hc.trans hc'.symm)

/-- 最長一致で読んだ hex digit の並びは一つに決まる。 -/
theorem hexPrefix_unique {ds1 ds2 r1 r2 : List Char} (h : ds1 ++ r1 = ds2 ++ r2)
    (ha1 : ∀ d ∈ ds1, HexDigit d) (ha2 : ∀ d ∈ ds2, HexDigit d)
    (hl1 : ds1.length ≤ 6) (hl2 : ds2.length ≤ 6)
    (hm1 : ds1.length = 6 ∨ ∀ d, r1[0]? = some d → ¬ HexDigit d)
    (hm2 : ds2.length = 6 ∨ ∀ d, r2[0]? = some d → ¬ HexDigit d) : ds1 = ds2 := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h2, h1'⟩ | ⟨c', h1'', h2'⟩
  · match a', h2, h1' with
    | [], h2, _ => simp [h2]
    | x :: a'', h2, h1' =>
      exfalso
      have hx : HexDigit x := ha2 x (by simp [h2])
      rcases hm1 with hm1 | hm1
      · have : ds2.length = ds1.length + a''.length + 1 := by simp [h2]; omega
        omega
      · exact hm1 x (by simp [h1']) hx
  · match c', h1'', h2' with
    | [], h1'', _ => simp [h1'']
    | x :: c'', h1'', h2' =>
      exfalso
      have hx : HexDigit x := ha1 x (by simp [h1''])
      rcases hm2 with hm2 | hm2
      · have : ds1.length = ds2.length + c''.length + 1 := by simp [h1'']; omega
        omega
      · exact hm2 x (by simp [h2']) hx

theorem hexDigit_head_of_split {c : Char} {rest ds r : List Char} (hl : c :: rest = ds ++ r)
    (hne : ds ≠ []) (hall : ∀ d ∈ ds, HexDigit d) : HexDigit c := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds' =>
    simp only [List.cons_append, List.cons.injEq] at hl
    exact hl.1 ▸ hall d (by simp)

theorem Escape.deterministic {l : List Char} {c1 c2 : Char} {r1 r2 : List Char}
    (h1 : Escape l c1 r1) (h2 : Escape l c2 r2) : c1 = c2 ∧ r1 = r2 := by
  cases h1 with
  | hex hl hne hlen hall hmax hws hv hc =>
    cases h2 with
    | hex hl' hne' hlen' hall' hmax' hws' hv' hc' =>
      have hds := hexPrefix_unique (hl.symm.trans hl') hall hall' hlen hlen' hmax hmax'
      subst hds
      have hr := List.append_cancel_left (hl.symm.trans hl')
      subst hr
      have hvv := HexNumber.deterministic hv hv'
      subst hvv
      refine ⟨EscapedValue.deterministic hc hc', ?_⟩
      rcases hws with ⟨w, hw, hws1⟩ | ⟨hnw, he⟩ <;>
        rcases hws' with ⟨w', hw', hws2⟩ | ⟨hnw', he'⟩
      · have := hw.symm.trans hw'
        simp only [List.cons.injEq] at this
        exact this.2
      · exact absurd hws1 (hnw' w (by simp [hw]))
      · exact absurd hws2 (hnw w' (by simp [hw']))
      · rw [he, he']
    | eof => exact absurd (List.append_eq_nil_iff.mp hl.symm).1 hne
    | other h => exact absurd (hexDigit_head_of_split hl hne hall) h
  | eof => cases h2 with
    | eof => exact ⟨rfl, rfl⟩
    | hex hl hne => exact absurd (List.append_eq_nil_iff.mp hl.symm).1 hne
  | other h => cases h2 with
    | other _ => exact ⟨rfl, rfl⟩
    | hex hl hne hlen hall => exact absurd (hexDigit_head_of_split hl hne hall) h

/-! ## ident sequence -/

theorem not_identCp_backslash : ¬ IdentCp '\\' := by
  simp [IdentCp, IdentStartCp, Letter, NonAsciiIdentCp, Digit]

theorem IdentSeq.deterministic {l r1 r2 o1 o2 : List Char}
    (h1 : IdentSeq l r1 o1) (h2 : IdentSeq l r2 o2) : r1 = r2 ∧ o1 = o2 := by
  induction h1 generalizing r2 o2 with
  | cp hc ih1 ih =>
    cases h2 with
    | cp _ h2 => obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩
    | escape => exact absurd hc not_identCp_backslash
    | stop hc' _ => exact absurd hc (hc' _ rfl)
  | escape hv he ih1 ih =>
    cases h2 with
    | cp hc _ => exact absurd hc not_identCp_backslash
    | escape _ he' h2 =>
      obtain ⟨rfl, rfl⟩ := Escape.deterministic he he'
      obtain ⟨rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl⟩
    | stop _ he' => exact absurd hv he'
  | stop hc he =>
    cases h2 with
    | cp hc' _ => exact absurd hc' (hc _ rfl)
    | escape hv _ _ => exact absurd hv he
    | stop _ _ => exact ⟨rfl, rfl⟩

/-! ## string token -/

theorem StringRun.deterministic {e : Char} {l v1 v2 o1 o2 : List Char} {b1 b2 : Bool}
    (h1 : StringRun e l v1 b1 o1) (h2 : StringRun e l v2 b2 o2) :
    v1 = v2 ∧ b1 = b2 ∧ o1 = o2 := by
  induction h1 generalizing v2 b2 o2 with
  | close => cases h2 <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; simp_all)
  | eof => cases h2; exact ⟨rfl, rfl, rfl⟩
  | newline he => cases h2 <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; simp_all)
  | backslashEof he => cases h2 <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; simp_all)
  | backslashNewline he ih1 ih =>
    cases h2 with
    | backslashNewline _ h2 => exact ih h2
    | close => exact absurd rfl he
    | backslashEscape _ hd => exact absurd rfl hd
    | other _ _ hb => exact absurd rfl hb
  | backslashEscape he hd hx ih1 ih =>
    cases h2 with
    | backslashEscape _ _ hx' h2 =>
      obtain ⟨rfl, rfl⟩ := Escape.deterministic hx hx'
      obtain ⟨rfl, rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl, rfl⟩
    | close => exact absurd rfl he
    | backslashNewline => exact absurd rfl hd
    | other _ _ hb => exact absurd rfl hb
  | other he hn hb ih1 ih =>
    cases h2 with
    | other _ _ _ h2 =>
      obtain ⟨rfl, rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl, rfl⟩
    | close => exact absurd rfl he
    | newline => exact absurd rfl hn
    | backslashEof => exact absurd rfl hb
    | backslashNewline => exact absurd rfl hb
    | backslashEscape => exact absurd rfl hb

theorem StringTok.deterministic {e : Char} {l : List Char} {t1 t2 : Token} {o1 o2 : List Char}
    (h1 : StringTok e l t1 o1) (h2 : StringTok e l t2 o2) : t1 = t2 ∧ o1 = o2 := by
  obtain ⟨v1, b1, h1, rfl⟩ := h1
  obtain ⟨v2, b2, h2, rfl⟩ := h2
  obtain ⟨rfl, rfl, rfl⟩ := StringRun.deterministic h1 h2
  exact ⟨rfl, rfl⟩

/-! ## comment -/

theorem CommentBody.deterministic {l r1 r2 : List Char}
    (h1 : CommentBody l r1) (h2 : CommentBody l r2) : r1 = r2 := by
  have key : ∀ {p1 p2 s1 s2 : List Char}, p1 ++ '*' :: '/' :: s1 = p2 ++ '*' :: '/' :: s2 →
      NoCommentEnd p2 → ∀ a, p2 = p1 ++ a → s1 = s2 := by
    intro p1 p2 s1 s2 h hno2 a ha
    subst ha
    rw [List.append_assoc] at h
    have h' := List.append_cancel_left h
    match a, h' with
    | [], h' => simp at h'; exact h'
    | [x], h' => simp at h'
    | x :: y :: a', h' =>
      simp only [List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, rfl, _⟩ := h'
      exact absurd (by simp) (hno2 p1 a')
  rcases h1 with ⟨p1, hp1, hno1⟩ | ⟨hno1, rfl⟩ <;> rcases h2 with ⟨p2, hp2, hno2⟩ | ⟨hno2, rfl⟩
  · have h := hp1.symm.trans hp2
    rcases List.append_eq_append_iff.mp h with ⟨a, ha, _⟩ | ⟨c, hc, _⟩
    · exact key h hno2 a ha
    · exact (key h.symm hno1 c hc).symm
  · exact absurd hp1 (hno2 p1 r1)
  · exact absurd hp2 (hno1 p2 r2)
  · rfl

theorem Comments.deterministic {l o1 o2 : List Char}
    (h1 : Comments l o1) (h2 : Comments l o2) : o1 = o2 := by
  induction h1 generalizing o2 with
  | done h =>
    cases h2 with
    | done _ => rfl
    | comment => exact absurd rfl (h _)
  | comment hb ih1 ih =>
    cases h2 with
    | done h => exact absurd rfl (h _)
    | comment hb' h2 =>
      have := CommentBody.deterministic hb hb'
      subst this
      exact ih h2

/-! ## number -/


theorem DecimalNumber.deterministic_aux {a b : List Char} {v1 v2 : Nat}
    (h1 : DecimalNumber a v1) (h2 : DecimalNumber b v2) (hab : a = b) : v1 = v2 := by
  induction h1 generalizing b v2 with
  | nil =>
    cases h2 with
    | nil => rfl
    | snoc d h => simp at hab
  | snoc d h ih =>
    cases h2 with
    | nil => simp at hab
    | snoc d' h' =>
      obtain ⟨hds, hd⟩ := List.append_inj' hab rfl
      simp at hd
      subst hd
      rw [ih h' hds]

theorem DecimalNumber.deterministic {ds : List Char} {v1 v2 : Nat}
    (h1 : DecimalNumber ds v1) (h2 : DecimalNumber ds v2) : v1 = v2 :=
  DecimalNumber.deterministic_aux h1 h2 rfl

theorem DigitRun.deterministic {l ds1 ds2 r1 r2 : List Char}
    (h1 : DigitRun l ds1 r1) (h2 : DigitRun l ds2 r2) : ds1 = ds2 ∧ r1 = r2 := by
  obtain ⟨hs1, ha1, hm1⟩ := h1
  obtain ⟨hs2, ha2, hm2⟩ := h2
  have h := hs1.symm.trans hs2
  have hds : ds1 = ds2 := by
    rcases List.append_eq_append_iff.mp h with ⟨a', h2', h1'⟩ | ⟨c', h1'', h2'⟩
    · match a', h2', h1' with
      | [], h2', _ => simp [h2']
      | x :: _, h2', h1' =>
        exact absurd ⟨x, by simp [h1'], ha2 x (by simp [h2'])⟩ hm1
    · match c', h1'', h2' with
      | [], h1'', _ => simp [h1'']
      | x :: _, h1'', h2' =>
        exact absurd ⟨x, by simp [h2'], ha1 x (by simp [h1''])⟩ hm2
  subst hds
  exact ⟨rfl, List.append_cancel_left h⟩

theorem SignPart.deterministic {l r1 r2 : List Char} {s1 s2 : Option Char}
    (h1 : SignPart l s1 r1) (h2 : SignPart l s2 r2) : s1 = s2 ∧ r1 = r2 := by
  rcases h1 with ⟨c, rfl, hc, rfl⟩ | ⟨hp, hm, rfl, rfl⟩ <;>
    rcases h2 with ⟨c', h', hc', rfl⟩ | ⟨hp', hm', rfl, rfl⟩
  · simp at h'; obtain ⟨rfl, rfl⟩ := h'; exact ⟨rfl, rfl⟩
  · rcases hc with rfl | rfl <;> simp_all
  · subst h'; rcases hc' with rfl | rfl <;> simp_all
  · exact ⟨rfl, rfl⟩

theorem FractionPart.deterministic {l r1 r2 : List Char} {f1 f2 : Bool}
    (h1 : FractionPart l f1 r1) (h2 : FractionPart l f2 r2) : f1 = f2 ∧ r1 = r2 := by
  rcases h1 with ⟨r, ds, hs, hl, hd, rfl⟩ | ⟨hs, rfl, rfl⟩ <;>
    rcases h2 with ⟨r', ds', hs', hl', hd', rfl⟩ | ⟨hs', rfl, rfl⟩
  · rw [hl] at hl'; simp at hl'; subst hl'
    exact ⟨rfl, (DigitRun.deterministic hd hd').2⟩
  · exact absurd hs hs'
  · exact absurd hs' hs
  · exact ⟨rfl, rfl⟩

theorem ExponentPart.deterministic {l r1 r2 : List Char} {e1 e2 : Bool}
    (h1 : ExponentPart l e1 r1) (h2 : ExponentPart l e2 r2) : e1 = e2 ∧ r1 = r2 := by
  rcases h1 with ⟨e, r, r', ds, hs, hl, hsg, hd, rfl⟩ | ⟨hs, rfl, rfl⟩ <;>
    rcases h2 with ⟨e', q, q', ds', hs', hl', hsg', hd', rfl⟩ | ⟨hs', rfl, rfl⟩
  · rw [hl] at hl'; simp at hl'; obtain ⟨rfl, rfl⟩ := hl'
    have hr : r' = q' := by
      rcases hsg with ⟨h, rfl⟩ | ⟨hp, hm, rfl⟩ <;> rcases hsg' with ⟨h', rfl⟩ | ⟨hp', hm', rfl⟩
      · rfl
      · rcases h with h | h <;> simp_all
      · rcases h' with h | h <;> simp_all
      · rfl
    subst hr
    exact ⟨rfl, (DigitRun.deterministic hd hd').2⟩
  · exact absurd hs hs'
  · exact absurd hs' hs
  · exact ⟨rfl, rfl⟩

theorem Number.deterministic {l r1 r2 : List Char} {n1 n2 : Num}
    (h1 : Number l n1 r1) (h2 : Number l n2 r2) : n1 = n2 ∧ r1 = r2 := by
  obtain ⟨s, a1, ds, a2, f, a3, e, v, hs, hd, hf, he, hv, rfl⟩ := h1
  obtain ⟨s', b1, ds', b2, f', b3, e', v', hs', hd', hf', he', hv', rfl⟩ := h2
  obtain ⟨rfl, rfl⟩ := SignPart.deterministic hs hs'
  obtain ⟨rfl, rfl⟩ := DigitRun.deterministic hd hd'
  obtain ⟨rfl, rfl⟩ := FractionPart.deterministic hf hf'
  obtain ⟨rfl, rfl⟩ := ExponentPart.deterministic he he'
  obtain rfl := DecimalNumber.deterministic hv hv'
  exact ⟨rfl, rfl⟩

/-! ## numeric token・ident-like token -/

theorem NumericTok.deterministic {l r1 r2 : List Char} {t1 t2 : Token}
    (h1 : NumericTok l t1 r1) (h2 : NumericTok l t2 r2) : t1 = t2 ∧ r1 = r2 := by
  obtain ⟨n, r, hn, h1⟩ := h1
  obtain ⟨n', r', hn', h2⟩ := h2
  obtain ⟨rfl, rfl⟩ := Number.deterministic hn hn'
  rcases h1 with ⟨hi, u, hu, rfl⟩ | ⟨hi, hr, rfl⟩ | ⟨hi, hp, rfl, rfl⟩ <;>
    rcases h2 with ⟨hi', u', hu', rfl⟩ | ⟨hi', hr', rfl⟩ | ⟨hi', hp', rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := IdentSeq.deterministic hu hu'; exact ⟨rfl, rfl⟩
  all_goals first
    | exact absurd hi hi'
    | exact absurd hi' hi
    | (rw [hr] at hr'; simp at hr'; exact ⟨rfl, hr'⟩)
    | (rw [hr] at hp'; simp at hp')
    | (rw [hr'] at hp; simp at hp)
    | exact ⟨rfl, rfl⟩

theorem IdentLikeTok.deterministic {l r1 r2 : List Char} {t1 t2 : Token}
    (h1 : IdentLikeTok l t1 r1) (h2 : IdentLikeTok l t2 r2) : t1 = t2 ∧ r1 = r2 := by
  obtain ⟨s, r, hs, h1⟩ := h1
  obtain ⟨s', r', hs', h2⟩ := h2
  obtain ⟨rfl, rfl⟩ := IdentSeq.deterministic hs hs'
  rcases h1 with ⟨hr, rfl⟩ | ⟨hp, rfl, rfl⟩ <;> rcases h2 with ⟨hr', rfl⟩ | ⟨hp', rfl, rfl⟩
  · rw [hr] at hr'; simp at hr'; exact ⟨rfl, hr'⟩
  · rw [hr] at hp'; simp at hp'
  · rw [hr'] at hp; simp at hp
  · exact ⟨rfl, rfl⟩

/-- **number の関係と `consumeNumber` は一致する。** -/
theorem Number.iff_consumeNumber {l : List Char} {n : Num} {r : List Char} :
    Number l n r ↔ (n, r) = consumeNumber l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := Number.deterministic h (consumeNumber_spec l)
    rfl
  · intro h
    have := consumeNumber_spec l
    rw [← h] at this
    exact this

/-- **numeric token の関係と `consumeNumericToken` は一致する。** -/
theorem NumericTok.iff_consumeNumericToken {l : List Char} {t : Token} {r : List Char} :
    NumericTok l t r ↔ (t, r) = consumeNumericToken l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := NumericTok.deterministic h (consumeNumericToken_spec l)
    rfl
  · intro h
    have := consumeNumericToken_spec l
    rw [← h] at this
    exact this

/-- **ident-like token の関係と `consumeIdentLike` は一致する。** -/
theorem IdentLikeTok.iff_consumeIdentLike {l : List Char} {t : Token} {r : List Char} :
    IdentLikeTok l t r ↔ (t, r) = consumeIdentLike l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := IdentLikeTok.deterministic h (consumeIdentLike_spec l)
    rfl
  · intro h
    have := consumeIdentLike_spec l
    rw [← h] at this
    exact this

/-! ## 実行関数との一致 -/

/-- **escape の関係と `consumeEscape` は一致する。** -/
theorem Escape.iff_consumeEscape {l : List Char} {c : Char} {r : List Char} :
    Escape l c r ↔ (c, r) = consumeEscape l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := Escape.deterministic h (consumeEscape_spec l)
    rfl
  · intro h
    have := consumeEscape_spec l
    rw [← h] at this
    exact this

/-- **ident sequence の関係と `consumeIdentSeq` は一致する。** -/
theorem IdentSeq.iff_consumeIdentSeq {l r o : List Char} :
    IdentSeq l r o ↔ (r, o) = consumeIdentSeq l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := IdentSeq.deterministic h (consumeIdentSeq_spec l)
    rfl
  · intro h
    have := consumeIdentSeq_spec l
    rw [← h] at this
    exact this

/-- **string token の関係と `stringAux` は一致する。** -/
theorem StringTok.iff_stringAux {e : Char} {l : List Char} {t : Token} {r : List Char} :
    StringTok e l t r ↔ (t, r) = stringAux e [] l := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := StringTok.deterministic h (stringAux_tok_spec e l)
    rfl
  · intro h
    have := stringAux_tok_spec e l
    rw [← h] at this
    exact this

/-- **comment の関係と `skipComments` は一致する。** -/
theorem Comments.iff_skipComments {l o : List Char} : Comments l o ↔ o = skipComments l :=
  ⟨fun h => Comments.deterministic h (skipComments_spec l),
   fun h => h ▸ skipComments_spec l⟩

/-! ## token を一つ読む

`TokenAt` は規則が多いので、組ごとの排他ではなく、各規則から `tokenAt` の値を直接計算する
（`TokenAt.complete`）。一意性はそこから従う。
-/

theorem WhitespaceRun.deterministic {l o1 o2 : List Char}
    (h1 : WhitespaceRun l o1) (h2 : WhitespaceRun l o2) : o1 = o2 := by
  obtain ⟨ws1, hs1, ha1, hm1⟩ := h1
  obtain ⟨ws2, hs2, ha2, hm2⟩ := h2
  have h := hs1.symm.trans hs2
  rcases List.append_eq_append_iff.mp h with ⟨a', h2', h1'⟩ | ⟨c', h1'', h2'⟩
  · match a', h2', h1' with
    | [], _, h1' => simpa using h1'
    | x :: _, h2', h1' => exact absurd (ha2 x (by simp [h2'])) (hm1 x (by simp [h1']))
  · match c', h1'', h2' with
    | [], _, h2' => simpa using h2'.symm
    | x :: _, h1'', h2' => exact absurd (ha1 x (by simp [h1''])) (hm2 x (by simp [h2']))

set_option linter.unusedSimpArgs false in
theorem tokenAt_of_digit {c : Char} {rest : List Char} (hc : Digit c) :
    tokenAt c rest = consumeNumericToken (c :: rest) := by
  unfold Digit at hc
  have n0 : c ≠ '\t' := by intro h; subst h; simp at hc
  have n1 : c ≠ '\n' := by intro h; subst h; simp at hc
  have n2 : c ≠ ' ' := by intro h; subst h; simp at hc
  have n3 : c ≠ '"' := by intro h; subst h; simp at hc
  have n4 : c ≠ '\'' := by intro h; subst h; simp at hc
  have n5 : c ≠ ',' := by intro h; subst h; simp at hc
  have n6 : c ≠ ':' := by intro h; subst h; simp at hc
  have n7 : c ≠ ';' := by intro h; subst h; simp at hc
  have n8 : c ≠ '(' := by intro h; subst h; simp at hc
  have n9 : c ≠ ')' := by intro h; subst h; simp at hc
  have n10 : c ≠ '[' := by intro h; subst h; simp at hc
  have n11 : c ≠ ']' := by intro h; subst h; simp at hc
  have n12 : c ≠ '{' := by intro h; subst h; simp at hc
  have n13 : c ≠ '}' := by intro h; subst h; simp at hc
  have n14 : c ≠ '#' := by intro h; subst h; simp at hc
  have n15 : c ≠ '+' := by intro h; subst h; simp at hc
  have n16 : c ≠ '.' := by intro h; subst h; simp at hc
  have n17 : c ≠ '-' := by intro h; subst h; simp at hc
  have n18 : c ≠ '<' := by intro h; subst h; simp at hc
  have n19 : c ≠ '@' := by intro h; subst h; simp at hc
  have n20 : c ≠ '\\' := by intro h; subst h; simp at hc
  have hd : isAsciiDigit c = true := (isAsciiDigit_iff c).mpr hc
  simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, hd]

set_option linter.unusedSimpArgs false in
theorem tokenAt_of_identStart {c : Char} {rest : List Char} (hc : IdentStartCp c) :
    tokenAt c rest = consumeIdentLike (c :: rest) := by
  unfold IdentStartCp Letter NonAsciiIdentCp at hc
  dsimp only at hc
  have n0 : c ≠ '\t' := by intro h; subst h; simp at hc
  have n1 : c ≠ '\n' := by intro h; subst h; simp at hc
  have n2 : c ≠ ' ' := by intro h; subst h; simp at hc
  have n3 : c ≠ '"' := by intro h; subst h; simp at hc
  have n4 : c ≠ '\'' := by intro h; subst h; simp at hc
  have n5 : c ≠ ',' := by intro h; subst h; simp at hc
  have n6 : c ≠ ':' := by intro h; subst h; simp at hc
  have n7 : c ≠ ';' := by intro h; subst h; simp at hc
  have n8 : c ≠ '(' := by intro h; subst h; simp at hc
  have n9 : c ≠ ')' := by intro h; subst h; simp at hc
  have n10 : c ≠ '[' := by intro h; subst h; simp at hc
  have n11 : c ≠ ']' := by intro h; subst h; simp at hc
  have n12 : c ≠ '{' := by intro h; subst h; simp at hc
  have n13 : c ≠ '}' := by intro h; subst h; simp at hc
  have n14 : c ≠ '#' := by intro h; subst h; simp at hc
  have n15 : c ≠ '+' := by intro h; subst h; simp at hc
  have n16 : c ≠ '.' := by intro h; subst h; simp at hc
  have n17 : c ≠ '-' := by intro h; subst h; simp at hc
  have n18 : c ≠ '<' := by intro h; subst h; simp at hc
  have n19 : c ≠ '@' := by intro h; subst h; simp at hc
  have n20 : c ≠ '\\' := by intro h; subst h; simp at hc
  have hd : isAsciiDigit c = false := by
    rw [Bool.eq_false_iff]; intro h
    have := (isAsciiDigit_iff c).mp h; unfold Digit at this
    rcases hc with hc | hc | rfl
    · omega
    · omega
    · simp at this
  have hi : isIdentStart c = true := (isIdentStart_iff c).mpr hc
  simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, hd, hi]

set_option linter.unusedSimpArgs false in
theorem tokenAt_of_other {c : Char} {rest : List Char} (hc : OtherCp c) :
    tokenAt c rest = (Token.delim c, rest) := by
  obtain ⟨hw, hd, hi, hl⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
  unfold Whitespace Newline at hw
  simp only [not_or] at hw
  have hd' : isAsciiDigit c = false := by
    rw [Bool.eq_false_iff]; exact fun h => hd ((isAsciiDigit_iff c).mp h)
  have hi' : isIdentStart c = false := by
    rw [Bool.eq_false_iff]; exact fun h => hi ((isIdentStart_iff c).mp h)
  simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hd', hi', hw, hl]

set_option linter.unusedSimpArgs false in
/-- **`TokenAt` が成り立つなら、`tokenAt` はその token と残りを返す。** -/
theorem TokenAt.complete {c : Char} {rest out : List Char} {t : Token}
    (h : TokenAt c rest t out) : (t, out) = tokenAt c rest := by
  cases h with
  | whitespace hc hw =>
    rw [tokenAt, if_pos ((isWhitespace_iff c).mpr hc)]
    rw [WhitespaceRun.deterministic hw (skipWhitespace_spec rest)]
  | string hc hs =>
    have := StringTok.iff_stringAux.mp hs
    rcases hc with rfl | rfl <;> simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash] <;> exact this
  | hash hcond hid hs =>
    have hseq := IdentSeq.iff_consumeIdentSeq.mp hs
    obtain rfl : _ = (consumeIdentSeq rest).1 := congrArg Prod.fst hseq
    obtain rfl : _ = (consumeIdentSeq rest).2 := congrArg Prod.snd hseq
    have hb : ((rest.head?.map isIdentChar).getD false || startsValidEscape rest) = true :=
      (hashCond_iff rest).mpr hcond
    have hid' : startsIdentSeq rest = _ := Bool.eq_iff_iff.mpr ((startsIdentSeq_iff rest).trans hid.symm)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hb, hid']
  | hashDelim hcond =>
    have hb : ((rest.head?.map isIdentChar).getD false || startsValidEscape rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hcond ((hashCond_iff rest).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hb]
  | punct hp =>
    cases hp <;> simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash]
  | numericSign hc hn ht =>
    have hn' := (startsNumber_iff _).mpr hn
    have := NumericTok.iff_consumeNumericToken.mp ht
    rcases hc with rfl | rfl | rfl <;> simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hn'] <;> exact this
  | signDelim hc hn =>
    have hn' : startsNumber (c :: rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hn ((startsNumber_iff _).mp h)
    rcases hc with rfl | rfl <;> simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hn']
  | cdc hn =>
    have hn' : startsNumber ('-' :: '-' :: '>' :: out) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hn ((startsNumber_iff _).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hn', startsCdc, ch_gt]
  | hyphenIdent hn hc hi ht =>
    have hn' : startsNumber ('-' :: rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hn ((startsNumber_iff _).mp h)
    have hc' : startsCdc rest = false := by
      rw [Bool.eq_false_iff]; exact fun h => hc ((startsCdc_iff rest).mp h)
    have hi' := (startsIdentSeq_iff _).mpr hi
    have := IdentLikeTok.iff_consumeIdentLike.mp ht
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hn', hc', hi']; exact this
  | hyphenDelim hn hc hi =>
    have hn' : startsNumber ('-' :: rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hn ((startsNumber_iff _).mp h)
    have hc' : startsCdc rest = false := by
      rw [Bool.eq_false_iff]; exact fun h => hc ((startsCdc_iff rest).mp h)
    have hi' : startsIdentSeq ('-' :: rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hi ((startsIdentSeq_iff _).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hn', hc', hi']
  | cdo => simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, startsCdo, ch_bang]
  | ltDelim hc =>
    have hc' : startsCdo rest = false := by
      rw [Bool.eq_false_iff]; exact fun h => hc ((startsCdo_iff rest).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hc']
  | atKeyword hi hs =>
    have hseq := IdentSeq.iff_consumeIdentSeq.mp hs
    obtain rfl : _ = (consumeIdentSeq rest).1 := congrArg Prod.fst hseq
    obtain rfl : _ = (consumeIdentSeq rest).2 := congrArg Prod.snd hseq
    have hi' := (startsIdentSeq_iff _).mpr hi
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hi']
  | atDelim hi =>
    have hi' : startsIdentSeq rest = false := by
      rw [Bool.eq_false_iff]; exact fun h => hi ((startsIdentSeq_iff _).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hi']
  | backslashIdent hv ht =>
    have hv' := (startsValidEscape_iff _).mpr hv
    have := IdentLikeTok.iff_consumeIdentLike.mp ht
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hv']; exact this
  | backslashDelim hv =>
    have hv' : startsValidEscape ('\\' :: rest) = false := by
      rw [Bool.eq_false_iff]; exact fun h => hv ((startsValidEscape_iff _).mp h)
    simp [tokenAt, isWhitespace, simpleToken, ch_lf, ch_tab, ch_space, ch_quote, ch_apos, ch_comma, ch_colon, ch_semicolon, ch_lparen, ch_rparen, ch_lbracket, ch_rbracket, ch_lbrace, ch_rbrace, ch_hash, ch_plus, ch_dot, ch_hyphen, ch_lt, ch_at, ch_backslash, hv']
  | digit hc ht =>
    rw [tokenAt_of_digit hc]; exact NumericTok.iff_consumeNumericToken.mp ht
  | identStart hc ht =>
    rw [tokenAt_of_identStart hc]; exact IdentLikeTok.iff_consumeIdentLike.mp ht
  | other hc => rw [tokenAt_of_other hc]

/-- `TokenAt` は結果を一意に決める。 -/
theorem TokenAt.deterministic {c : Char} {rest o1 o2 : List Char} {t1 t2 : Token}
    (h1 : TokenAt c rest t1 o1) (h2 : TokenAt c rest t2 o2) : t1 = t2 ∧ o1 = o2 := by
  have := h1.complete.trans h2.complete.symm
  simp only [Prod.mk.injEq] at this
  exact this

/-- **token を一つ読む関係と `tokenAt` は一致する。** -/
theorem TokenAt.iff_tokenAt {c : Char} {rest out : List Char} {t : Token} :
    TokenAt c rest t out ↔ (t, out) = tokenAt c rest := by
  constructor
  · exact TokenAt.complete
  · intro h
    have := tokenAt_spec c rest
    rw [← h] at this
    exact this

/-! ## token 列 -/

theorem Tokenizes.tokenizeAux_eq {l : List Char} {ts : List Token} (h : Tokenizes l ts) :
    ∀ acc, tokenizeAux acc l = acc.reverse ++ ts := by
  induction h with
  | eof hc =>
    intro acc
    have hs := Comments.iff_skipComments.mp hc
    rw [tokenizeAux]; split
    · simp
    · next heq => unfold nextToken at heq; rw [← hs] at heq; cases heq
  | step hc ht ih1 ih =>
    intro acc
    rename_i l rest out c t ts
    have hs := Comments.iff_skipComments.mp hc
    have hn : nextToken l = some (t, out) := by
      unfold nextToken; rw [← hs]; exact congrArg some ht.complete.symm
    rw [tokenizeAux]; split
    · next heq => rw [hn] at heq; cases heq
    · next t' r' heq =>
      rw [hn] at heq; cases heq
      rw [ih]; simp

/-- `Tokenizes` は結果を一意に決める。 -/
theorem Tokenizes.deterministic {l : List Char} {ts1 ts2 : List Token}
    (h1 : Tokenizes l ts1) (h2 : Tokenizes l ts2) : ts1 = ts2 := by
  have e1 := h1.tokenizeAux_eq []
  have e2 := h2.tokenizeAux_eq []
  simpa using e1.symm.trans e2

/-- **tokenizer の関係と `tokenize` は一致する。** -/
theorem TokenizesInput.iff_tokenize {input : String} {ts : List Token} :
    TokenizesInput input ts ↔ ts = tokenize input := by
  constructor
  · rintro ⟨l, hp, ht⟩
    have hl := Preprocessed.eq_filterCodePoints_iff.mp hp
    subst hl
    have := ht.tokenizeAux_eq []
    simp only [List.reverse_nil, List.nil_append] at this
    unfold tokenize; rw [this]
  · rintro rfl; exact tokenize_spec input

end Selectors.Spec
