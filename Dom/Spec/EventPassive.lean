import Dom.Spec.Event

/-!
# default passive value は関係と一致する

実行側の `defaultPassiveValue`（`Dom/Event/Dispatch.lean`）は `List.find?` で document element と body element を
探す。関係 `DefaultPassive`（`Dom/Spec/Event.lean`）は「children のうち最初に条件を満たすもの」として書いてある。
二つが一致することと、関係が値を一つに決めることを示す。
-/

namespace Dom.Spec

open Dom

theorem find?_firstElement_iff (t : Tree) (p c : NodeId) :
    (childrenOf t p).find? (fun x => kindOf t x == some .element) = some c ↔ FirstElementChild t p c := by
  rw [List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨hc, pre, post, hl, hpre⟩
    refine ⟨pre, post, hl, by simpa using hc, fun x hx => ?_⟩
    have := hpre x hx
    simpa using this
  · rintro ⟨pre, post, hl, hc, hpre⟩
    refine ⟨by simpa using hc, pre, post, hl, fun x hx => ?_⟩
    simpa using hpre x hx

theorem isHtmlElementNamed_iff (t : Tree) (n : NodeId) (name : String) :
    isHtmlElementNamed t n name = true ↔ IsHtmlNamed t n name := by
  unfold isHtmlElementNamed IsHtmlNamed
  cases h : t.get? n with
  | none => simp
  | some d =>
    simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨⟨hk, hns⟩, hln⟩; exact ⟨hk, hns, hln⟩
    · rintro ⟨hk, hns, hln⟩; exact ⟨⟨hk, hns⟩, hln⟩

theorem bodyElementOf_iff (t : Tree) (doc b : NodeId) :
    bodyElementOf t doc = some b ↔ BodyElement t doc b := by
  unfold bodyElementOf BodyElement
  have hbf : ∀ x, (isHtmlElementNamed t x "body" || isHtmlElementNamed t x "frameset") = true ↔
      IsBodyOrFrameset t x := by
    intro x
    simp only [Bool.or_eq_true, isHtmlElementNamed_iff, IsBodyOrFrameset]
  cases hf : (childrenOf t doc).find? (fun c => kindOf t c == some .element) with
  | none =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨html, hfirst, -⟩
    rw [← find?_firstElement_iff] at hfirst
    rw [hf] at hfirst
    cases hfirst
  | some html =>
    have hfirst := (find?_firstElement_iff t doc html).mp hf
    simp only
    constructor
    · intro h
      split at h
      · rename_i hhtml
        rw [List.find?_eq_some_iff_append] at h
        obtain ⟨hb, pre, post, hl, hpre⟩ := h
        refine ⟨html, hfirst, (isHtmlElementNamed_iff t html "html").mp hhtml, pre, post, hl,
          (hbf b).mp hb, fun x hx => ?_⟩
        intro hx'
        have := hpre x hx
        rw [(hbf x).mpr hx'] at this
        cases this
      · cases h
    · rintro ⟨html', hfirst', hhtml, pre, post, hl, hb, hpre⟩
      have he : html' = html := by
        rw [← find?_firstElement_iff] at hfirst'
        rw [hf] at hfirst'
        exact (Option.some.inj hfirst').symm
      subst he
      rw [if_pos ((isHtmlElementNamed_iff t html' "html").mpr hhtml), List.find?_eq_some_iff_append]
      refine ⟨(hbf b).mpr hb, pre, post, hl, fun x hx => ?_⟩
      cases hx' : (isHtmlElementNamed t x "body" || isHtmlElementNamed t x "frameset")
      · rfl
      · exact absurd ((hbf x).mp hx') (hpre x hx)

/-- **実行側の default passive value は関係を満たす。** -/
theorem defaultPassiveValue_spec (t : Tree) («type» : String) (target : NodeId) :
    DefaultPassive t «type» target (defaultPassiveValue t «type» target) := by
  unfold DefaultPassive defaultPassiveValue
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine and_congr (by simp only [or_assoc]) ?_
  cases ho : ownerDocumentOf t target with
  | none => simp
  | some doc =>
    simp only [Option.some.injEq, exists_eq_left', Bool.or_eq_true, beq_iff_eq,
      find?_firstElement_iff, bodyElementOf_iff]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

/-- **関係は値を一つに決める。** -/
theorem defaultPassive_eq {t : Tree} {«type» : String} {target : NodeId} {b : Bool}
    (h : DefaultPassive t «type» target b) : b = defaultPassiveValue t «type» target := by
  have h' := defaultPassiveValue_spec t «type» target
  unfold DefaultPassive at h h'
  have key : b = true ↔ defaultPassiveValue t «type» target = true := h.trans h'.symm
  revert key
  cases b <;> cases defaultPassiveValue t «type» target <;> simp

end Dom.Spec
