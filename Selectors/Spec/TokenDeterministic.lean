import Selectors.Spec.Token
import Selectors.Spec.TokenSound

/-!
# tokenizer の関係仕様は決定的である

`Selectors/Spec/Token.lean` の各関係は入力の形で規則が排他なので、結果を一意に決める。
`Selectors/Spec/TokenSound.lean` と合わせると、関係が実行関数を特徴づける。
-/

namespace Selectors.Spec

open Selectors

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

end Selectors.Spec
