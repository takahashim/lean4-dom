import Dom.Spec.RangeInsertSound
import Dom.Spec.RangeDeleteCongr

/-!
# `insertNode` の関係の一意性と完全性

step 12 の pre-insert は step 9 の removal の後の状態で走るので、その状態は観測としてしか
決まらない。そこで pre-insertion validity と pre-insert の関係の congruence を置く。
-/

namespace Dom.Spec

open Dom

/-! ## pre-insertion validity は木の観測だけで決まる -/

theorem preInsertValidity_congr {t t' : Tree} (h : TreeObsEq t t') {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {r : Except DOMException Unit} :
    PreInsertValidity t' node parent child excl r ↔ PreInsertValidity t node parent child excl r := by
  have e₁ : ∀ n, InTree t' n = InTree t n := fun n => by unfold InTree; rw [h n]
  have e₂ : ∀ n k, KindIs t' n k = KindIs t n k := fun n k => by unfold KindIs; rw [h n]
  have e₃ : ∀ n, IsText t' n = IsText t n := fun n => by unfold IsText; rw [h n]
  have e₄ : ∀ n, IsCharacterData t' n = IsCharacterData t n := fun n => by
    unfold IsCharacterData; rw [h n]
  have e₅ : ∀ n, childrenOf t' n = childrenOf t n := h.childrenOf
  have e₆ : ∀ n, parentOf t' n = parentOf t n := h.parentOf
  have e₇ : ∀ a n, InclusiveAncestor t' a n = InclusiveAncestor t a n :=
    fun a n => propext h.inclusiveAncestor_iff
  unfold PreInsertValidity ParentIsContainer ChildIsChildOf NodeIsInsertable
    ElementInsertionBlocked DoctypeInsertionBlocked HasChildOfKindOutside HasTextChild
    HasTwoElementChildren DoctypeFollowing ElementPreceding HasChildOfKind
  simp only [e₁, e₂, e₃, e₄, e₅, e₆, e₇]

/-- **pre-insert の結果の関係の congruence。** -/
theorem preInsertResult_congr {s sb : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb)
    {node parent : NodeId} {child : Option NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : PreInsertResult s node parent child r₁) (h₂ : PreInsertResult sb node parent child r₂) :
    ResultObsEq r₁ r₂ := by
  have hv : ∀ {r}, PreInsertValidity sb.tree node parent child [] r ↔
      PreInsertValidity s.tree node parent child [] r := preInsertValidity_congr h.tree
  cases r₁ with
  | ok o₁ =>
    cases r₂ with
    | ok o₂ =>
      obtain ⟨hv₁, ref₁, ha₁, hb₁, hi₁⟩ := h₁
      obtain ⟨-, ref₂, ha₂, hb₂, hi₂⟩ := h₂
      have hre : ref₂ = ref₁ := by
        by_cases hc : child = some node
        · rw [ha₁ hc, ha₂ hc, h.tree.nextSibling]
        · rw [hb₁ hc, hb₂ hc]
      rw [hre] at hi₂
      refine insertSpec_congr hwf h ?_ hi₁ hi₂
      have hve : ensurePreInsertionValidity s.tree node parent child [] = .ok () :=
        (preInsertValidity_iff hwf).mp hv₁
      have hshift := ensurePreInsertionValidity_shift hwf hve
      have hv' : ensurePreInsertionValidity s.tree node parent ref₁ [] = .ok () := by
        by_cases hc : child = some node
        · rw [ha₁ hc]; rw [if_pos hc] at hshift; exact hshift
        · rw [hb₁ hc]; rw [if_neg hc] at hshift; exact hshift
      exact nodesToInsert_not_ancestor_of_validity hwf hv'
    | error e₂ =>
      have := preInsertValidity_deterministic _ _ _ _ _ _ _ h₁.1
        (hv.mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂)))
      cases this
  | error e₁ =>
    cases r₂ with
    | ok o₂ =>
      have := preInsertValidity_deterministic _ _ _ _ _ _ _
        (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁)) (hv.mp h₂.1)
      cases this
    | error e₂ =>
      have := preInsertValidity_deterministic _ _ _ _ _ _ _
        (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁))
        (hv.mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂)))
      exact Except.error.inj this

/-! ## step 4 と step 10-11 -/

theorem childAtOffset_unique {t : Tree} {n : NodeId} {offset : Nat} {a b : Option NodeId}
    (h₁ : ChildAtOffset t n offset a) (h₂ : ChildAtOffset t n offset b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some c => exact absurd h₂.2 (h₁ c h₂.1)
  | some c =>
    cases b with
    | none => exact absurd h₁.2 (h₂ c h₁.1)
    | some c' =>
      by_cases hcc : c = c'
      · rw [hcc]
      · exact absurd rfl (index_ne_of_ne h₁.1 h₂.1 h₁.2 h₂.2 hcc)

theorem newOffset_congr {t t' : Tree} (h : TreeObsEq t t') {parent node : NodeId}
    {ref : Option NodeId} {n₁ n₂ : Nat}
    (h₁ : NewOffset t parent ref node n₁) (h₂ : NewOffset t' parent ref node n₂) : n₁ = n₂ := by
  obtain ⟨b₁, hb₁, hc₁⟩ := h₁
  obtain ⟨b₂, hb₂, hc₂⟩ := h₂
  have hbe : b₁ = b₂ := by
    rcases hb₁ with ⟨hr, rfl⟩ | ⟨c, hr, hi⟩ <;> rcases hb₂ with ⟨hr', rfl⟩ | ⟨c', hr', hi'⟩
    · rw [h.lengthOf]
    · rw [hr] at hr'; cases hr'
    · rw [hr] at hr'; cases hr'
    · rw [hr] at hr'
      cases hr'
      rw [h.index] at hi'
      rw [hi] at hi'
      exact Option.some.inj hi'
  subst hbe
  have hk : KindIs t' node .documentFragment ↔ KindIs t node .documentFragment := by
    unfold KindIs; rw [h node]
  rcases hc₁ with ⟨hk₁, rfl⟩ | ⟨hk₁, rfl⟩ <;> rcases hc₂ with ⟨hk₂, rfl⟩ | ⟨hk₂, rfl⟩
  · rw [h.lengthOf]
  · exact absurd (hk.mpr hk₁) hk₂
  · exact absurd (hk.mp hk₂) hk₁
  · rfl

/-! ## 全体 -/

/-- **`insertNode` の関係は結果を一つに決める。** -/
theorem insertNode_result_deterministic {s : DOMState} {i : Nat} {r : RangeState} {node : NodeId}
    (hwf : WellFormed s.tree) {res₁ res₂ : Except DOMException DOMState}
    (h₁ : InsertNodeResult s i r node res₁) (h₂ : InsertNodeResult s i r node res₂) :
    ResultObsEq res₁ res₂ := by
  have vdet := preInsertValidity_deterministic s.tree
  rcases h₁ with ⟨he₁, rfl⟩ | ⟨hn₁, hrest₁⟩ <;> rcases h₂ with ⟨he₂, rfl⟩ | ⟨hn₂, hrest₂⟩
  · rfl
  · exact absurd he₁ hn₂
  · exact absurd he₂ hn₁
  rcases hrest₁ with ⟨ht₁, p₁, hp₁, hres₁⟩ | ⟨ht₁, ref₁, hc₁, hres₁⟩ <;>
    rcases hrest₂ with ⟨ht₂, p₂, hp₂, hres₂⟩ | ⟨ht₂, ref₂, hc₂, hres₂⟩
  · -- Text
    rw [hp₁] at hp₂
    cases hp₂
    rcases hres₁ with ⟨e₁, hv₁, rfl⟩ | ⟨hv₁, rfl⟩ <;> rcases hres₂ with ⟨e₂, hv₂, rfl⟩ | ⟨hv₂, rfl⟩
    · exact Except.error.inj (vdet _ _ _ _ _ _ hv₁ hv₂)
    · cases vdet _ _ _ _ _ _ hv₁ hv₂
    · cases vdet _ _ _ _ _ _ hv₁ hv₂
    · rfl
  · exact absurd ht₁ ht₂
  · exact absurd ht₂ ht₁
  · have hre := childAtOffset_unique hc₁ hc₂
    subst hre
    rcases hres₁ with ⟨e₁, hv₁, rfl⟩ | ⟨hv₁, ht₁'⟩ <;> rcases hres₂ with ⟨e₂, hv₂, rfl⟩ | ⟨hv₂, ht₂'⟩
    · exact Except.error.inj (vdet _ _ _ _ _ _ hv₁ hv₂)
    · cases vdet _ _ _ _ _ _ hv₁ hv₂
    · cases vdet _ _ _ _ _ _ hv₁ hv₂
    obtain ⟨ref'₁, h8₁, s₁, h9₁, no₁, hno₁, hpi₁⟩ := ht₁'
    obtain ⟨ref'₂, h8₂, s₁', h9₂, no₂, hno₂, hpi₂⟩ := ht₂'
    have hre' : ref'₁ = ref'₂ := by
      rcases h8₁ with ⟨ha, rfl⟩ | ⟨ha, rfl⟩ <;> rcases h8₂ with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
      · rfl
      · exact absurd ha hb
      · exact absurd hb ha
      · rfl
    subst hre'
    -- step 9
    have hobs₁ : ObsEq s₁ s₁' ∧ WellFormed s₁.tree := by
      rcases h9₁ with ⟨hp, rfl⟩ | ⟨⟨p, hp⟩, hrm⟩ <;> rcases h9₂ with ⟨hp', rfl⟩ | ⟨⟨p', hp'⟩, hrm'⟩
      · exact ⟨ObsEq.refl _, hwf⟩
      · rw [hp] at hp'; cases hp'
      · rw [hp] at hp'; cases hp'
      · exact ⟨removeSpec_congr hwf (ObsEq.refl s) hrm hrm', removeSpec_wellFormed hwf hrm⟩
    obtain ⟨hobs₁, hwf₁⟩ := hobs₁
    have hoe : no₁ = no₂ := newOffset_congr hobs₁.tree hno₁ hno₂
    subst hoe
    refine andThen_congr (fun _ _ ha hb => preInsertResult_congr hwf₁ hobs₁ ha hb) ?_ hpi₁ hpi₂
    intro s₂ s₂' _ hobs₂ q₁ q₂ ⟨r₂, hr₂, hq₁⟩ ⟨r₂', hr₂', hq₂⟩
    have hre : r₂' = r₂ := by
      rw [hobs₂.ranges] at hr₂'
      rw [hr₂] at hr₂'
      exact (Option.some.inj hr₂').symm
    subst hre
    rcases hq₁ with ⟨hcol, rfl⟩ | ⟨hcol, rfl⟩ <;> rcases hq₂ with ⟨hcol', rfl⟩ | ⟨hcol', rfl⟩
    · exact { hobs₂ with ranges := (by simp only [hobs₂.ranges]) }
    · exact absurd hcol hcol'
    · exact absurd hcol' hcol
    · exact hobs₂

/-- **`insertNode` の完全性。** -/
theorem rangeInsertNode_result_complete {s : DOMState} {i : Nat} {r : RangeState} {node : NodeId}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r)
    {res : Except DOMException DOMState} (hres : InsertNodeResult s i r node res) :
    ResultObsEq res (rangeInsertNode s i node) :=
  insertNode_result_deterministic h.wellFormed hres (rangeInsertNode_result_sound node h hr hrv)

end Dom.Spec
