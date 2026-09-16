import Dom.Spec.Move
import Dom.Spec.RemoveSound
import Dom.Spec.InsertSound

/-!
# `move` は `MoveSpec` を満たす

step 10-11, 14 は `remove` と同じ三つの調整なので、`remove` の soundness を借りる。
`move` が呼ぶのは `detachWithLiveAdjust` で、`remove` はその後ろに
transient registered observer と record を足しただけである。足す側は木も
live range も NodeIterator も触らないので、`suppressObservers` を立てた `remove` に
読み替えれば `remove_sound_range` / `_iterator` / `_tree` がそのまま効く。
-/

namespace Dom.Spec

open Dom

/--
`detachWithLiveAdjust` は「observer を抑えた `remove`」の前半である。

後半（step 20 の transient registered observer）は木・live range・NodeIterator を
触らないので、この読み替えで前半についての定理が使える。
-/
theorem remove_suppress_of_detach {s s₁ : DOMState} {node p : NodeId}
    (hp : parentOf s.tree node = some p) (h : detachWithLiveAdjust s node = .ok s₁) :
    remove s node true = .ok (addTransientObservers s₁ node p) := by
  rw [remove_of_detach hp h]
  simp

/-- **`detachWithLiveAdjust` は `MoveDetached` を満たす。** -/
theorem moveDetached_of_detach {s s₁ : DOMState} {node p : NodeId} (hwf : WellFormed s.tree)
    (hp : parentOf s.tree node = some p) (h : detachWithLiveAdjust s node = .ok s₁) :
    MoveDetached s s₁ node p ((index s.tree node).getD 0) := by
  have hr := remove_suppress_of_detach hp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hq := remove_sound_range hwf hp hr
    simpa [RangeAdjusted] using hq
  · have hq := remove_sound_iterator hwf hp hr
    simpa [IteratorAdjusted] using hq
  · have hq := remove_sound_tree hwf hp hr
    simpa using hq
  · obtain ⟨-, hs⟩ := DOMState.mapTree_eq_ok h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hs] <;> simp

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
      -- step 23 が読む `oldParent` は step 7-9 で見たものと同じである。
      simp only [hp] at h
      split at h
      · simp at h
      · next s₁ hd =>
        have hdet := moveDetached_of_detach hwf hp hd
        have hwf₁ : WellFormed s₁.tree := by
          have := remove_preserves_wellformed hwf (remove_suppress_of_detach hp hd)
          simpa using this
        split at h
        · simp at h
        · next s₂ hi =>
          obtain ⟨hi', hs₂⟩ := DOMState.mapTree_eq_ok hi
          -- step 16。`child` は step 18 の `insertAt` が「parent の子」を検査する。
          obtain ⟨idx, hidx⟩ : ∃ idx, ChildIndex s₁.tree child idx := by
            cases child with
            | none => exact ⟨0, rfl⟩
            | some c =>
              obtain ⟨pd, nd, hpd, -, -, -, hchild, -⟩ := insertAt_ok_cases hi'
              have hmem : c ∈ childrenOf s₁.tree newParent := by
                rw [liveRangeInsertAdjust_tree] at hpd
                rw [childrenOf_eq hpd]
                exact hchild c rfl
              exact index_isSome hwf₁ (parentOf_of_mem_childrenOf hwf₁ hmem)
          have hwf₂ : WellFormed s₂.tree := by
            rw [hs₂]
            exact insertAt_preserves_wellformed (by rw [liveRangeInsertAdjust_tree]; exact hwf₁) hi'
          -- step 17 の兄弟。`child` で場合分けして `match` を潰しておく。
          -- 潰さないと、同じ式が証明の中と `move` の定義とで別の補助関数になる。
          obtain ⟨newPrev, hprev, hh⟩ :
              ∃ np, PreviousSiblingOf s₁.tree newParent child np ∧
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
            s₁, liveRangeInsertAdjust s₁ newParent child 1, s₂,
            queueTreeMutationRecord s₂ oldParent [] [node]
              (previousSibling s.tree node) (nextSibling s.tree node),
            hp, rfl, hdet, hprev, hidx,
            rangeInsertAdjusted_of_adjust s₁ newParent child 1 idx hidx,
            treeInserted_insertAt hi',
            ⟨by rw [hs₂]; rfl, by rw [hs₂]; rfl, by rw [hs₂]; rfl, by rw [hs₂]; rfl,
              by rw [hs₂]; rfl, by rw [hs₂]; rfl⟩,
            treeRecordQueued_of_queue s₂ hwf₂ oldParent [] [node] _ _ (by simp),
            ⟨by simp, by simp, by simp, by simp⟩,
            treeRecordQueued_of_queue _ hwf₃ newParent [node] [] _ _ (by simp),
            ⟨by simp, by simp, by simp, by simp⟩⟩

end Dom.Spec
