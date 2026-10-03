import Dom.Spec.Observe

/-!
# `observe` は関係とちょうど一致する

実行関数の結果は `ObserveResult` を満たし（sound）、関係を満たす結果は実行関数の結果と
等しい（complete）。一意性は complete から出る。
-/

namespace Dom.Spec

open Dom MutationObserver

/-! ## step 1-2 -/

theorem resolve_fields (o : MutationObserverInit) :
    o.resolve.childList = o.childList ∧ o.resolve.subtree = o.subtree ∧
      o.resolve.attributeOldValue = o.attributeOldValue ∧
      o.resolve.attributeFilter = o.attributeFilter ∧
      o.resolve.characterDataOldValue = o.characterDataOldValue := by
  obtain ⟨cl, st, att, aov, af, cd, cdov⟩ := o
  cases att <;> cases aov <;> cases af <;> cases cd <;> cases cdov <;>
    simp [MutationObserverInit.resolve]

theorem attributesResolved_resolve (o : MutationObserverInit) :
    AttributesResolved o o.resolve.attributes := by
  obtain ⟨cl, st, att, aov, af, cd, cdov⟩ := o
  unfold AttributesResolved
  cases att <;> cases aov <;> cases af <;> cases cd <;> cases cdov <;>
    simp [MutationObserverInit.resolve]

theorem characterDataResolved_resolve (o : MutationObserverInit) :
    CharacterDataResolved o o.resolve.characterData := by
  obtain ⟨cl, st, att, aov, af, cd, cdov⟩ := o
  unfold CharacterDataResolved
  cases att <;> cases aov <;> cases af <;> cases cd <;> cases cdov <;>
    simp [MutationObserverInit.resolve]

theorem attributesResolved_unique {o : MutationObserverInit} {a b : Option Bool}
    (h₁ : AttributesResolved o a) (h₂ : AttributesResolved o b) : a = b := by
  rcases h₁ with ⟨c₁, c₁', rfl⟩ | ⟨c₁, rfl⟩ <;> rcases h₂ with ⟨c₂, c₂', rfl⟩ | ⟨c₂, rfl⟩
  · rfl
  · exact absurd ⟨c₁, c₁'⟩ c₂
  · exact absurd ⟨c₂, c₂'⟩ c₁
  · rfl

theorem characterDataResolved_unique {o : MutationObserverInit} {a b : Option Bool}
    (h₁ : CharacterDataResolved o a) (h₂ : CharacterDataResolved o b) : a = b := by
  rcases h₁ with ⟨c₁, c₁', rfl⟩ | ⟨c₁, rfl⟩ <;> rcases h₂ with ⟨c₂, c₂', rfl⟩ | ⟨c₂, rfl⟩
  · rfl
  · exact absurd ⟨c₁, c₁'⟩ c₂
  · exact absurd ⟨c₂, c₂'⟩ c₁
  · rfl

/-! ## step 3-6 -/

theorem rejected_iff (o : MutationObserverInit) :
    ObserveOptionsRejected o ↔
      ((o.childList = false ∧ o.resolve.attributes ≠ some true ∧ o.resolve.characterData ≠ some true) ∨
        (o.attributeOldValue = true ∧ o.resolve.attributes = some false) ∨
        (o.attributeFilter ≠ none ∧ o.resolve.attributes = some false) ∨
        (o.characterDataOldValue = true ∧ o.resolve.characterData = some false)) := by
  constructor
  · rintro ⟨a, c, ha, hc, h⟩
    rw [attributesResolved_unique ha (attributesResolved_resolve o),
      characterDataResolved_unique hc (characterDataResolved_resolve o)] at h
    exact h
  · intro h
    exact ⟨_, _, attributesResolved_resolve o, characterDataResolved_resolve o, h⟩

theorem observeOptionsError_spec (o : MutationObserverInit) :
    (ObserveOptionsRejected o ∧ observeOptionsError o = some .typeError) ∨
      (¬ ObserveOptionsRejected o ∧ observeOptionsError o = none) := by
  rw [rejected_iff]
  unfold observeOptionsError
  obtain ⟨cl, st, att, aov, af, cd, cdov⟩ := o
  cases cl <;> cases att <;> cases aov <;> cases af <;> cases cd <;> cases cdov <;>
    simp [MutationObserverInit.resolve] <;>
    (try (rename_i x; cases x)) <;> (try (rename_i x; cases x)) <;> simp_all

/-! ## 全体 -/

theorem registrationFor_resolve (mo : Nat) (target : NodeId) (o : MutationObserverInit) :
    registrationFor mo target o o.resolve.attributes o.resolve.characterData =
      { node := target, observer := mo, subtree := o.resolve.subtree,
        childList := o.resolve.childList, attributes := o.resolve.attributes == some true,
        attributeOldValue := o.resolve.attributeOldValue,
        attributeFilter := o.resolve.attributeFilter,
        characterData := o.resolve.characterData == some true,
        characterDataOldValue := o.resolve.characterDataOldValue } := by
  obtain ⟨hcl, hst, haov, hfil, hcov⟩ := resolve_fields o
  have hb : ∀ x : Option Bool, decide (x = some true) = (x == some true) := by
    intro x; cases x with
    | none => rfl
    | some b => cases b <;> rfl
  unfold registrationFor
  rw [hcl, hst, haov, hfil, hcov, hb, hb]

/-- **`observe` の結果は関係を満たす。** -/
theorem observe_result_sound (s : DOMState) (mo : Nat) (target : NodeId) (o : MutationObserverInit) :
    ObserveResult s mo target o (observe s mo target o) := by
  unfold observe
  dsimp only
  cases hd : s.tree.get? target with
  | none => exact Or.inl ⟨Or.inl hd, rfl⟩
  | some d =>
    simp only [Option.isNone_some, Bool.false_eq_true, if_false]
    by_cases hmo : mo ≥ s.observers.length
    · rw [if_pos hmo]; exact Or.inl ⟨Or.inr hmo, rfl⟩
    rw [if_neg hmo]
    have hmo' : mo < s.observers.length := by omega
    rcases observeOptionsError_spec o with ⟨hrej, he⟩ | ⟨hrej, he⟩
    · rw [he]; exact Or.inr ⟨⟨d, hd⟩, hmo', hrej, rfl⟩
    rw [he]
    dsimp only
    have hreg := registrationFor_resolve mo target o
    by_cases hex : (s.registrations.any fun r =>
        r.observer == mo && r.node == target && !r.transient) = true
    · rw [if_pos hex]
      refine ⟨⟨d, hd⟩, hmo', hrej, _, _, attributesResolved_resolve o,
        characterDataResolved_resolve o, Or.inl ⟨?_, ?_⟩⟩
      · obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp hex
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        exact ⟨r, hr, hc.1.1, hc.1.2, hc.2⟩
      · rw [hreg]
        congr 2
        funext r
        unfold reregistered
        by_cases h1 : r.transient = true ∧ r.observer = mo ∧ r.source = some target
        · rw [if_pos h1]; simp [h1.1, h1.2.1, h1.2.2]
        · rw [if_neg h1]
          by_cases h2 : r.observer = mo ∧ r.node = target ∧ r.transient = false
          · rw [if_pos h2]; simp [h2.1, h2.2.1, h2.2.2]
          · rw [if_neg h2]
            have e1 : ¬ ((r.transient && r.observer == mo && r.source == some target) = true) := by
              simp only [Bool.and_eq_true, beq_iff_eq]
              intro ⟨⟨a, b⟩, c⟩; exact h1 ⟨a, b, c⟩
            have e2 : ¬ ((r.observer == mo && r.node == target && !r.transient) = true) := by
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
              intro ⟨⟨a, b⟩, c⟩; exact h2 ⟨a, b, c⟩
            rw [if_neg e1, if_neg e2]
    · rw [if_neg hex]
      obtain ⟨ob, hob⟩ : ∃ ob, s.observers[mo]? = some ob :=
        ⟨s.observers[mo], List.getElem?_eq_getElem hmo'⟩
      refine ⟨⟨d, hd⟩, hmo', hrej, _, _, attributesResolved_resolve o,
        characterDataResolved_resolve o, Or.inr ⟨fun ⟨r, hr, h1, h2, h3⟩ => hex (List.any_eq_true.mpr
          ⟨r, hr, by simp [h1, h2, h3]⟩), ob, hob, ?_⟩⟩
      rw [hreg, hob]

/-- **関係を満たす結果は、`observe` の結果と等しい。** -/
theorem observe_result_complete {s : DOMState} {mo : Nat} {target : NodeId}
    {o : MutationObserverInit} {r : Except DOMException DOMState} (h : ObserveResult s mo target o r) :
    r = observe s mo target o := by
  have hs := observe_result_sound s mo target o
  rcases r with e | s'
  · cases hr : observe s mo target o with
    | error e' =>
      rw [hr] at hs
      congr 1
      rcases h with ⟨hn, rfl⟩ | ⟨⟨d, hd⟩, hmo, hrej, rfl⟩ <;>
        rcases hs with ⟨hn', rfl⟩ | ⟨⟨d', hd'⟩, hmo', hrej', rfl⟩
      · rfl
      · rcases hn with hn | hn
        · rw [hn] at hd'; cases hd'
        · omega
      · rcases hn' with hn' | hn'
        · rw [hn'] at hd; cases hd
        · omega
      · rfl
    | ok s₂ =>
      rw [hr] at hs
      exfalso
      obtain ⟨⟨d, hd⟩, hmo, hrej, -⟩ := hs
      rcases h with ⟨hn | hn, -⟩ | ⟨-, -, hrej', -⟩
      · rw [hn] at hd; cases hd
      · omega
      · exact hrej hrej'
  · cases hr : observe s mo target o with
    | error e' =>
      rw [hr] at hs
      exfalso
      obtain ⟨⟨d, hd⟩, hmo, hrej, -⟩ := h
      rcases hs with ⟨hn | hn, -⟩ | ⟨-, -, hrej', -⟩
      · rw [hn] at hd; cases hd
      · omega
      · exact hrej hrej'
    | ok s₂ =>
      rw [hr] at hs
      congr 1
      obtain ⟨-, -, -, a, c, ha, hc, h₁⟩ := h
      obtain ⟨-, -, -, a', c', ha', hc', h₂⟩ := hs
      rw [attributesResolved_unique ha ha', characterDataResolved_unique hc hc'] at h₁
      rcases h₁ with ⟨hx, rfl⟩ | ⟨hx, ob, hob, rfl⟩ <;> rcases h₂ with ⟨hx', rfl⟩ | ⟨hx', ob', hob', rfl⟩
      · rfl
      · exact absurd hx hx'
      · exact absurd hx' hx
      · rw [hob] at hob'; cases hob'; rfl

end Dom.Spec
