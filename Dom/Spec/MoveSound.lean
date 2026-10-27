import Dom.Spec.Move
import Dom.Spec.RemoveSound
import Dom.Spec.InsertSound

/-!
# `move` は `MoveSpec` を満たす

step 9-10, 13 は `remove` と同じ三つの調整なので、`remove` の soundness（`detached_of_detach`）を借りる。
step 17 も `remove` と同じ `addTransientObservers` なので、`transientAdded_of_add` がそのまま効く。
-/

namespace Dom.Spec

open Dom

/-! ## 全体 -/

/-- **`move` は `MoveSpec` を満たす。** -/
theorem move_sound {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (hwf : WellFormed s.tree) (h : move s node newParent child = .ok s') :
    MoveSpec s node newParent child s' := by
  unfold move at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next oldParent hp =>
      split at h
      · simp at h
      · next s₁ hd =>
        have hdet := detached_of_detach hwf hp hd
        have hwf₁ : WellFormed s₁.tree :=
          detach_preserves_wellformed hwf (detachWithLiveAdjust_tree hd)
        -- step 17
        have hta := transientAdded_of_add hwf₁ node oldParent
        have hwfₜ : WellFormed (addTransientObservers s₁ node oldParent).tree := by simpa using hwf₁
        simp only at h
        generalize hi : (liveRangeInsertAdjust (addTransientObservers s₁ node oldParent) newParent
          child 1).mapTree (fun t => insertAt t newParent node child) = r at h
        cases r with
        | error e => cases h
        | ok s₂ =>
          obtain ⟨hi', hs₂⟩ := DOMState.mapTree_eq_ok hi
          -- step 18。`child` は step 20-21 の `insertAt` が「parent の子」を検査する。
          obtain ⟨idx, hidx⟩ : ∃ idx, ChildIndex (addTransientObservers s₁ node oldParent).tree child idx := by
            cases child with
            | none => exact ⟨0, rfl⟩
            | some c =>
              obtain ⟨pd, nd, hpd, -, -, -, hchild, -⟩ := insertAt_ok_cases hi'
              have hmem : c ∈ childrenOf (addTransientObservers s₁ node oldParent).tree newParent := by
                rw [liveRangeInsertAdjust_tree] at hpd
                rw [childrenOf_eq hpd]
                exact hchild c rfl
              exact index_isSome hwfₜ (parentOf_of_mem_childrenOf hwfₜ hmem)
          have hwf₂ : WellFormed s₂.tree := by
            rw [hs₂]
            exact insertAt_preserves_wellformed (by rw [liveRangeInsertAdjust_tree]; exact hwfₜ) hi'
          -- step 19 の兄弟。`child` で場合分けして `match` を潰しておく。
          -- 潰さないと、同じ式が証明の中と `move` の定義とで別の補助関数になる。
          obtain ⟨newPrev, hprev, hh⟩ :
              ∃ np, PreviousSiblingOf (addTransientObservers s₁ node oldParent).tree newParent child np ∧
                (Except.ok (queueTreeMutationRecord
                  (queueTreeMutationRecord s₂ oldParent [] [node]
                    (previousSibling s.tree node) (nextSibling s.tree node))
                  newParent [node] [] np child) : Except DOMException DOMState) = .ok s' := by
            cases child with
            | none => exact ⟨_, rfl, h⟩
            | some c => exact ⟨_, rfl, h⟩
          have hwf₃ : WellFormed
              (queueTreeMutationRecord s₂ oldParent [] [node]
                (previousSibling s.tree node) (nextSibling s.tree node)).tree := by
            simpa using hwf₂
          rw [← Except.ok.inj hh]
          exact ⟨oldParent, (index s.tree node).getD 0, idx, newPrev,
            s₁, addTransientObservers s₁ node oldParent,
            liveRangeInsertAdjust (addTransientObservers s₁ node oldParent) newParent child 1, s₂,
            queueTreeMutationRecord s₂ oldParent [] [node]
              (previousSibling s.tree node) (nextSibling s.tree node),
            hp, rfl, hdet, hta, hprev, hidx,
            rangeInsertAdjusted_of_adjust _ newParent child 1 idx hidx,
            treeInserted_insertAt hi',
            ⟨by rw [hs₂]; rfl, by rw [hs₂]; rfl, by rw [hs₂]; rfl, by rw [hs₂]; rfl,
              by rw [hs₂]; rfl, by rw [hs₂]; rfl,
              ⟨by rw [hs₂]; rfl, by rw [hs₂]; rfl, by rw [hs₂]; rfl⟩⟩,
            treeRecordQueued_of_queue s₂ hwf₂ oldParent [] [node] _ _ (by simp),
            ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩,
            treeRecordQueued_of_queue _ hwf₃ newParent [node] [] _ _ (by simp),
            ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩⟩

end Dom.Spec
