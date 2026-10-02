import Dom.Spec.Normalize
import Dom.Spec.ReplaceDataCongr
import Dom.Spec.RemoveCongr
import Dom.Properties.CharacterData
import Dom.Validity.PreserveInsertAt

/-!
# `normalize` の congruence と一意性

`Dom/Spec/InsertCongr.lean` と同じ形で、`NormalizeSpec` について
「入力の観測が等しければ出力の観測も等しい」を段ごとに示す。
-/

namespace Dom.Spec

open Dom

/-! ## 補題 -/

/-- replace data は木の形を変えないので、well-formedness を保つ。 -/
theorem replaceDataSpec_wellFormed {s s' : DOMState} {node : NodeId} {offset count : Nat}
    {data : String} (hwf : WellFormed s.tree) (h : ReplaceDataSpec s node offset count data s') :
    WellFormed s'.tree := by
  obtain ⟨d, c, new, s₀, hd, -, -, -, -, -, hdr, -⟩ := h
  refine TreeObsEq.wellFormed (t := withData s.tree node d new) ?_ (wellFormed_withData hwf hd new)
  intro m
  rw [get?_withData hd]
  by_cases hm : m = node
  · subst hm; rw [if_pos rfl, hdr.changed d hd]
  · rw [if_neg hm, hdr.others m hm]

/-- 前提を満たす分け方は一つしかない（`sibs` は最長の exclusive Text の並び）。 -/
private theorem prefix_unique {α : Type _} {P : α → Prop} :
    ∀ (a₁ b₁ a₂ b₂ : List α), a₁ ++ b₁ = a₂ ++ b₂ →
      (∀ x ∈ a₁, P x) → (∀ x, b₁.head? = some x → ¬ P x) →
      (∀ x ∈ a₂, P x) → (∀ x, b₂.head? = some x → ¬ P x) → a₁ = a₂
  | [], b₁, [], b₂, _, _, _, _, _ => rfl
  | [], b₁, y :: a₂, b₂, he, _, hb₁, ha₂, _ => by
    simp only [List.nil_append, List.cons_append] at he
    exact absurd (ha₂ y (by simp)) (hb₁ y (by rw [he]; rfl))
  | x :: a₁, b₁, [], b₂, he, ha₁, _, _, hb₂ => by
    simp only [List.nil_append, List.cons_append] at he
    exact absurd (ha₁ x (by simp)) (hb₂ x (by rw [← he]; rfl))
  | x :: a₁, b₁, y :: a₂, b₂, he, ha₁, hb₁, ha₂, hb₂ => by
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rw [prefix_unique a₁ b₁ a₂ b₂ he (fun z hz => ha₁ z (by simp [hz])) hb₁
      (fun z hz => ha₂ z (by simp [hz])) hb₂]

theorem exclusiveText_congr {t tb : Tree} (h : TreeObsEq t tb) (n : NodeId) :
    ExclusiveText tb n ↔ ExclusiveText t n := by
  unfold ExclusiveText
  rw [h n]

/-- **後ろの contiguous exclusive Text nodes は木の観測から一つに決まる。** -/
theorem followingContiguousTexts_unique {t tb : Tree} (hwf : WellFormed t) (h : TreeObsEq t tb)
    {n : NodeId} {sibs₁ sibs₂ : List NodeId}
    (h₁ : FollowingContiguousTexts t n sibs₁) (h₂ : FollowingContiguousTexts tb n sibs₂) :
    sibs₁ = sibs₂ := by
  obtain ⟨p₁, pre₁, post₁, hp₁, hc₁, ha₁, hb₁⟩ := h₁
  obtain ⟨p₂, pre₂, post₂, hp₂, hc₂, ha₂, hb₂⟩ := h₂
  rw [h.parentOf, hp₁] at hp₂
  cases hp₂
  rw [h.childrenOf] at hc₂
  have e := (splitAt?_childrenOf_of_split hwf hc₁).symm.trans (splitAt?_childrenOf_of_split hwf hc₂)
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  refine prefix_unique (P := ExclusiveText t) _ _ _ _ e.2 ha₁ hb₁
    (fun x hx => (exclusiveText_congr h x).mp (ha₂ x hx))
    (fun x hx hex => hb₂ x hx ((exclusiveText_congr h x).mpr hex))

/-- step 6.1-6.4 の三つの枝は（`sib` が `parent` でなければ）排他なので、行き先は一つに決まる。 -/
theorem bpHandedOff_unique {survivor sib parent : NodeId} {idx len : Nat}
    {bp b₁ b₂ : BoundaryPoint} (hne : sib ≠ parent)
    (h₁ : BPHandedOff survivor sib parent idx len bp b₁)
    (h₂ : BPHandedOff survivor sib parent idx len bp b₂) : b₁ = b₂ := by
  rcases h₁ with ⟨hn₁, rfl⟩ | ⟨hn₁, ho₁, rfl⟩ | ⟨hn₁, hx₁, rfl⟩ <;>
    rcases h₂ with ⟨hn₂, rfl⟩ | ⟨hn₂, ho₂, rfl⟩ | ⟨hn₂, hx₂, rfl⟩
  all_goals first
    | rfl
    | (exfalso; exact hne (hn₁.symm.trans hn₂))
    | (exfalso; exact hne (hn₂.symm.trans hn₁))
    | (exfalso; exact hn₂ hn₁)
    | (exfalso; exact hn₁ hn₂)
    | (exfalso; exact hx₂ ⟨hn₁, ho₁⟩)
    | (exfalso; exact hx₁ ⟨hn₂, ho₂⟩)

/-- **step 6 の congruence。** -/
theorem rangesHandedOff_congr {s₁ sb₁ s₂ sb₂ : DOMState} {survivor sib parent : NodeId}
    {idx len : Nat} (hne : sib ≠ parent) (h : ObsEq s₁ sb₁)
    (h₁ : RangesHandedOff s₁ s₂ survivor sib parent idx len)
    (h₂ : RangesHandedOff sb₁ sb₂ survivor sib parent idx len) : ObsEq s₂ sb₂ := by
  obtain ⟨rs₁, rfl, hl₁, hh₁⟩ := h₁
  obtain ⟨rs₂, rfl, hl₂, hh₂⟩ := h₂
  have hr : sb₁.ranges = s₁.ranges := h.ranges
  rw [hr] at hl₂ hh₂
  have hrs : rs₂ = rs₁ := by
    refine List.ext_getElem (by rw [hl₂, hl₁]) (fun i hi₂ hi₁ => ?_)
    have hs : i < s₁.ranges.length := by omega
    obtain ⟨r, hrr⟩ : ∃ r, s₁.ranges[i]? = some r := ⟨s₁.ranges[i], by simp [hs]⟩
    have e₁ := hh₁ i r rs₁[i] hrr (by simp [hi₁])
    have e₂ := hh₂ i r rs₂[i] hrr (by simp [hi₂])
    rw [show rs₂[i] = ⟨(rs₂[i]).start, (rs₂[i]).«end»⟩ from rfl,
      show rs₁[i] = ⟨(rs₁[i]).start, (rs₁[i]).«end»⟩ from rfl,
      bpHandedOff_unique hne e₂.1 e₁.1, bpHandedOff_unique hne e₂.2 e₁.2]
  exact { h with ranges := hrs }

/-! ## 兄弟を一つ畳む -/

/-- **`SiblingMerged` の congruence。** well-formedness も運ぶ。 -/
theorem siblingMerged_congr {s sb o₁ o₂ : DOMState} {survivor sib : NodeId}
    (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (h₁ : SiblingMerged s survivor sib o₁) (h₂ : SiblingMerged sb survivor sib o₂) :
    ObsEq o₁ o₂ ∧ WellFormed o₁.tree := by
  obtain ⟨dsurv, dsib, parent, pre, post, s₁, s₂, hsurv, hsib, hp, hc, hst, hro, hrm⟩ := h₁
  obtain ⟨dsurv', dsib', parent', pre', post', sb₁, sb₂, hsurv', hsib', hp', hc', hst', hro',
    hrm'⟩ := h₂
  rw [h.tree survivor, hsurv] at hsurv'
  cases hsurv'
  rw [h.tree sib, hsib] at hsib'
  cases hsib'
  rw [h.tree.parentOf, hp] at hp'
  cases hp'
  rw [h.tree.childrenOf] at hc'
  have e := (splitAt?_childrenOf_of_split hwf hc).symm.trans (splitAt?_childrenOf_of_split hwf hc')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hne : sib ≠ parent := by
    intro he
    rw [he] at hp
    exact hwf.acyclic parent (Ancestor.step hp)
  -- step 3-4
  have hobs₁ : ObsEq s₁ sb₁ ∧ WellFormed s₁.tree := by
    rcases hst with ⟨he, rfl⟩ | ⟨he, hr⟩ <;> rcases hst' with ⟨he', rfl⟩ | ⟨he', hr'⟩
    · exact ⟨h, hwf⟩
    · exact absurd he he'
    · exact absurd he' he
    · exact ⟨replaceDataSpec_congr h hr hr', replaceDataSpec_wellFormed hwf hr⟩
  obtain ⟨hobs₁, hwf₁⟩ := hobs₁
  -- step 6
  have hobs₂ := rangesHandedOff_congr hne hobs₁ hro hro'
  have hwf₂ : WellFormed s₂.tree := by
    obtain ⟨rs, rfl, -⟩ := hro
    exact hwf₁
  -- step 7
  exact ⟨removeSpec_congr hwf₂ hobs₂ hrm hrm', removeSpec_wellFormed hwf₂ hrm⟩

/-- **`RunMerged` の congruence。** -/
theorem runMerged_congr {s o₁ : DOMState} {survivor : NodeId} {sibs : List NodeId}
    (h₁ : RunMerged s survivor sibs o₁) :
    ∀ {sb o₂ : DOMState}, WellFormed s.tree → ObsEq s sb → RunMerged sb survivor sibs o₂ →
      ObsEq o₁ o₂ ∧ WellFormed o₁.tree := by
  induction h₁ with
  | nil =>
    intro sb o₂ hwf h h₂
    cases h₂
    exact ⟨h, hwf⟩
  | cons hm _ ih =>
    intro sb o₂ hwf h h₂
    cases h₂ with
    | cons hm' hr' =>
      obtain ⟨hobs, hwf₁⟩ := siblingMerged_congr hwf h hm hm'
      exact ih hwf₁ hobs hr'

/-! ## 候補列 -/

/-- **`NormalizedEach` の congruence。** -/
theorem normalizedEach_congr {this : NodeId} {s o₁ : DOMState} {cands : List NodeId}
    (h₁ : NormalizedEach this s cands o₁) :
    ∀ {sb o₂ : DOMState}, WellFormed s.tree → ObsEq s sb → NormalizedEach this sb cands o₂ →
      ObsEq o₁ o₂ := by
  induction h₁ with
  | nil =>
    intro sb o₂ _ h h₂
    cases h₂
    exact h
  | skip hna _ ih =>
    intro sb o₂ hwf h h₂
    cases h₂ with
    | skip _ hr' => exact ih hwf h hr'
    | empty ha' => exact absurd (h.tree.ancestor_iff.mp ha') hna
    | run ha' => exact absurd (h.tree.ancestor_iff.mp ha') hna
  | empty ha hd hlen hrm _ ih =>
    intro sb o₂ hwf h h₂
    cases h₂ with
    | skip hna' => exact absurd (h.tree.ancestor_iff.mpr ha) hna'
    | empty _ hd' _ hrm' hr' =>
      exact ih (removeSpec_wellFormed hwf hrm) (removeSpec_congr hwf h hrm hrm') hr'
    | run _ hd' hlen' =>
      rw [h.tree, hd] at hd'
      cases hd'
      exact absurd hlen hlen'
  | run ha hd hlen hft hrun _ ih =>
    intro sb o₂ hwf h h₂
    cases h₂ with
    | skip hna' => exact absurd (h.tree.ancestor_iff.mpr ha) hna'
    | empty _ hd' hlen' =>
      rw [h.tree, hd] at hd'
      cases hd'
      exact absurd hlen' hlen
    | run _ _ _ hft' hrun' hr' =>
      have he := followingContiguousTexts_unique hwf h.tree hft hft'
      subst he
      obtain ⟨hobs, hwf₁⟩ := runMerged_congr hrun hwf h hrun'
      exact ih hwf₁ hobs hr'

/-- **`NormalizeSpec` は出力を観測として一つに決める。** -/
theorem normalizeSpec_deterministic {s o₁ o₂ : DOMState} {this : NodeId}
    (hwf : WellFormed s.tree) (h₁ : NormalizeSpec s this o₁) (h₂ : NormalizeSpec s this o₂) :
    ObsEq o₁ o₂ :=
  normalizedEach_congr h₁.2 hwf (ObsEq.refl s) h₂.2

end Dom.Spec
