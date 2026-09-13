import Dom.Spec.Adopt
import Dom.Spec.RemoveSound

/-!
# `adopt` は関係意味論を満たす

`Dom/Spec/Adopt.lean` の `AdoptSpec` を、実行関数 `adopt` が満たすことを示す。
step 2 は `remove_sound` に、step 3 は `get?_setOwnerDocument` に帰着する。
-/

namespace Dom.Spec

open Dom

/-- step 3。`setOwnerDocument` は部分木だけの node document を付け替える。 -/
theorem documentAssigned_setOwnerDocument {t : Tree} (hwf : WellFormed t) {node doc : NodeId}
    {nd : NodeData} (hn : t.get? node = some nd) :
    DocumentAssigned t (setOwnerDocument t node doc) node doc := by
  constructor
  · intro m d hm hdesc
    rw [get?_setOwnerDocument, hm]
    simp only [Option.map_some, Option.some.injEq]
    rw [if_pos ((mem_preorder_iff hwf hn m).mpr hdesc)]
  · intro m hdesc
    rw [get?_setOwnerDocument]
    cases hq : t.get? m with
    | none => rfl
    | some d =>
      simp only [Option.map_some]
      rw [if_neg (fun hmem => hdesc ((mem_preorder_iff hwf hn m).mp hmem))]

/-- **`adopt` は `AdoptSpec` を満たす。** -/
theorem adopt_sound {s s' : DOMState} {node doc : NodeId} (hwf : WellFormed s.tree)
    (h : adopt s node doc = .ok s') : AdoptSpec s node doc s' := by
  unfold adopt at h
  split at h
  · simp at h
  · next oldDoc hold =>
    refine ⟨oldDoc, hold, ?_⟩
    -- step 2
    split at h
    · simp at h
    · next s₁ hstep =>
      refine ⟨s₁, ?_, ?_⟩
      · -- parent の有無で分ける
        revert hstep
        split
        · next hp => intro hstep; exact Or.inl ⟨hp, (Except.ok.inj hstep).symm⟩
        · next p hp => intro hstep; exact Or.inr ⟨⟨p, hp⟩, remove_sound hwf hstep⟩
      · -- step 3
        have hwf₁ : WellFormed s₁.tree := by
          revert hstep
          split
          · intro hstep; rw [← Except.ok.inj hstep]; exact hwf
          · intro hstep; exact remove_preserves_wellformed hwf hstep
        have hnode : ∃ nd, s₁.tree.get? node = some nd := by
          obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? node = some nd := by
            unfold ownerDocumentOf at hold
            cases hq : s.tree.get? node with
            | none => rw [hq] at hold; simp at hold
            | some nd => exact ⟨nd, rfl⟩
          revert hstep
          split
          · intro hstep; rw [← Except.ok.inj hstep]; exact ⟨nd, hnd⟩
          · intro hstep
            exact exists_get?_of_kindPreserving (shapePreserving_remove hstep) hnd
        obtain ⟨nd₁, hnd₁⟩ := hnode
        split at h
        · next he => rw [if_pos he, ← Except.ok.inj h]
        · next he =>
          rw [if_neg he, ← Except.ok.inj h]
          exact ⟨documentAssigned_setOwnerDocument hwf₁ hnd₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Dom.Spec
