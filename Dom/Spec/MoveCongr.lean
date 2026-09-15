import Dom.Spec.Move
import Dom.Spec.InsertCongr

/-!
# `move` の congruence

`move` は `remove` も `insert` も呼ばないので、congruence も component を直接繋ぐ。
道具はすべて `remove` と `insert` のために作ったものである。

* 木から外す段は `remove` の三つの一意性（`treeRemoved_unique` /
  `rangeAdjusted_unique` / `iteratorAdjusted_unique`）
* 入れる段は `rangeInsertAdjusted_congr` と `treeInserted_congr`
* record の段は `treeRecordQueued_congr`

step 1-6（`moveValidity`）は関係に含めていないので、それが保証する事実は要らない。
木に入れるところは `TreeInserted` を直接使っていて、`insert` のように
`adopt` を挟まないからである。
-/

namespace Dom.Spec

open Dom

variable {s sb : DOMState} {node newParent : NodeId} {child : Option NodeId}

/-- **step 10-11, 14 の congruence。** -/
theorem moveDetached_congr {s₁ s₁' : DOMState} {p : NodeId} {i : Nat} {nd : NodeData}
    (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (hnd : s.tree.get? node = some nd) (hp : parentOf s.tree node = some p)
    (h₁ : MoveDetached s s₁ node p i) (h₂ : MoveDetached sb s₁' node p i) : ObsEq s₁ s₁' := by
  obtain ⟨hr₁, hit₁, ht₁, hu₁⟩ := h₁
  obtain ⟨hr₂, hit₂, ht₂, hu₂⟩ := h₂
  have hr₂' := rangeAdjusted_transport h hr₂
  have hit₂' := iteratorAdjusted_transport hwf h hit₂
  have ht₂' := treeRemoved_transport h.tree ht₂
  exact
    { tree := fun m => (treeRemoved_unique ht₁ ht₂' m).symm
      ranges := (rangeAdjusted_unique hr₁ hr₂').symm
      iterators := (iteratorAdjusted_unique hwf hnd hp hit₁ hit₂').symm
      registrations := fun r => by
        rw [hu₂.registrations, hu₁.registrations]; exact h.registrations r
      records := fun mo => by rw [hu₂.observers, hu₁.observers]; exact h.records mo
      pendingObservers := fun mo => by
        rw [hu₂.pendingObservers, hu₁.pendingObservers]; exact h.pendingObservers mo
      microtaskQueued := by
        rw [hu₂.microtaskQueued, h.microtaskQueued, hu₁.microtaskQueued] }

/-! ## 全体 -/

/-- **`MoveSpec` の congruence。** -/
theorem moveSpec_congr {o₁ o₂ : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (h₁ : MoveSpec s node newParent child o₁) (h₂ : MoveSpec sb node newParent child o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨oldParent, index, idx, newPrev, s₁, sa, s₂, s₃,
    hp₁, hix₁, hdet₁, hprev₁, hidx₁, hri₁, hti₁, hl₁, hq₁, hf₁, hq₁', hf₁'⟩ := h₁
  obtain ⟨oldParent', index', idx', newPrev', s₁', sa', s₂', s₃',
    hp₂, hix₂, hdet₂, hprev₂, hidx₂, hri₂, hti₂, hl₂, hq₂, hf₂, hq₂', hf₂'⟩ := h₂
  -- step 7-9。旧 parent と index は入力の観測から決まる。
  have hoe : oldParent' = oldParent := by
    rw [h.tree.parentOf, hp₁] at hp₂
    exact (Option.some.inj hp₂).symm
  subst hoe
  have hie : index' = index := by rw [hix₁, hix₂, h.tree.index]
  subst hie
  obtain ⟨nd, hnd, -⟩ := parentOf_eq_some hp₁
  -- step 10-11, 14
  have hobs₁ : ObsEq s₁ s₁' := moveDetached_congr hwf h hnd hp₁ hdet₁ hdet₂
  -- step 16-17
  have hpe : newPrev' = newPrev :=
    (previousSiblingOf_unique hobs₁.tree hprev₁ hprev₂).symm
  subst hpe
  have hde : idx' = idx := (childIndex_unique hobs₁.tree hidx₁ hidx₂).symm
  subst hde
  have hobsa : ObsEq sa sa' := rangeInsertAdjusted_congr hobs₁ hri₁ hri₂
  -- step 18
  have hobs₂ : ObsEq s₂ s₂' :=
    { tree := treeInserted_congr hobsa.tree hti₁ hti₂
      ranges := by rw [hl₂.ranges, hobsa.ranges, hl₁.ranges]
      iterators := by rw [hl₂.iterators, hobsa.iterators, hl₁.iterators]
      registrations := fun r => by
        rw [hl₂.registrations, hl₁.registrations]; exact hobsa.registrations r
      records := fun mo => by rw [hl₂.observers, hl₁.observers]; exact hobsa.records mo
      pendingObservers := fun mo => by
        rw [hl₂.pendingObservers, hl₁.pendingObservers]; exact hobsa.pendingObservers mo
      microtaskQueued := by
        rw [hl₂.microtaskQueued, hobsa.microtaskQueued, hl₁.microtaskQueued] }
  -- step 23-24
  have hobs₃ : ObsEq s₃ s₃' := by
    refine treeRecordQueued_congr hobs₂ hq₁ ?_ hf₁ hf₂
    rwa [h.tree.previousSibling, h.tree.nextSibling] at hq₂
  exact treeRecordQueued_congr hobs₃ hq₁' hq₂' hf₁' hf₂'

/-- **`MoveSpec` は観測を一つに決める。** -/
theorem moveSpec_deterministic {o₁ o₂ : DOMState} (hwf : WellFormed s.tree)
    (h₁ : MoveSpec s node newParent child o₁) (h₂ : MoveSpec s node newParent child o₂) :
    ObsEq o₁ o₂ :=
  moveSpec_congr hwf (ObsEq.refl s) h₁ h₂

end Dom.Spec
