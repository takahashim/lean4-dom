import Dom.Spec.Move
import Dom.Spec.InsertCongr

/-!
# `move` の congruence

`move` は `remove` も `insert` も呼ばないので、congruence も component を直接繋ぐ。
道具はすべて `remove` と `insert` のために作ったものである。

* 木から外す段は `remove` と同じ `detached_congr`
* transient registered observer の段は `remove` と同じ `transientAdded_congr`
* 入れる段は `rangeInsertAdjusted_congr` と `treeInserted_congr`
* record の段は `treeRecordQueued_congr`

step 1-6（`moveValidity`）は関係に含めていないので、それが保証する事実は要らない。
木に入れるところは `TreeInserted` を直接使っていて、`insert` のように
`adopt` を挟まないからである。
-/

namespace Dom.Spec

open Dom

variable {s sb : DOMState} {node newParent : NodeId} {child : Option NodeId}

/-! ## 全体 -/

/-- **`MoveSpec` の congruence。** -/
theorem moveSpec_congr {o₁ o₂ : DOMState} (hwf : WellFormed s.tree) (h : ObsEq s sb)
    (h₁ : MoveSpec s node newParent child o₁) (h₂ : MoveSpec sb node newParent child o₂) :
    ObsEq o₁ o₂ := by
  obtain ⟨oldParent, index, idx, newPrev, s₁, sₜ, sa, s₂, s₃,
    hp₁, hix₁, hdet₁, hta₁, hprev₁, hidx₁, hri₁, hti₁, hl₁, hq₁, hf₁, hq₁', hf₁'⟩ := h₁
  obtain ⟨oldParent', index', idx', newPrev', s₁', sₜ', sa', s₂', s₃',
    hp₂, hix₂, hdet₂, hta₂, hprev₂, hidx₂, hri₂, hti₂, hl₂, hq₂, hf₂, hq₂', hf₂'⟩ := h₂
  -- step 7-9。旧 parent と index は入力の観測から決まる。
  have hoe : oldParent' = oldParent := by
    rw [h.tree.parentOf, hp₁] at hp₂
    exact (Option.some.inj hp₂).symm
  subst hoe
  have hie : index' = index := by rw [hix₁, hix₂, h.tree.index]
  subst hie
  obtain ⟨nd, hnd, -⟩ := parentOf_eq_some hp₁
  -- step 9-10, 13
  have hobs₀ : ObsEq s₁ s₁' := detached_congr hwf h hnd hp₁ hdet₁ hdet₂
  -- step 17
  have hobs₁ : ObsEq sₜ sₜ' := transientAdded_congr hobs₀ hta₁ hta₂
  -- step 18-19
  have hpe : newPrev' = newPrev :=
    (previousSiblingOf_unique hobs₁.tree hprev₁ hprev₂).symm
  subst hpe
  have hde : idx' = idx := (childIndex_unique hobs₁.tree hidx₁ hidx₂).symm
  subst hde
  have hobsa : ObsEq sa sa' := rangeInsertAdjusted_congr hobs₁ hri₁ hri₂
  -- step 20-21
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
        rw [hl₂.microtaskQueued, hobsa.microtaskQueued, hl₁.microtaskQueued]
      walkers := by rw [hl₂.untouched.walkers, hobsa.walkers, hl₁.untouched.walkers]
      listeners := by rw [hl₂.untouched.listeners, hobsa.listeners, hl₁.untouched.listeners]
      detachedAttrs := by
        rw [hl₂.untouched.detachedAttrs, hobsa.detachedAttrs, hl₁.untouched.detachedAttrs]
      registrationOrder := fun m => by
        rw [hl₂.registrations, hl₁.registrations]; exact hobsa.registrationOrder m
      pendingOrder := by rw [hl₂.pendingObservers, hobsa.pendingOrder, hl₁.pendingObservers] }
  -- step 26-27
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
