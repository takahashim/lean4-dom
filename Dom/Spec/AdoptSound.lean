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
  obtain ⟨oldDoc, s₁, hold, hstep, hfinal⟩ := adopt_cases h
  refine ⟨oldDoc, hold, s₁, ?_, ?_⟩
  · -- step 2。parent の有無で分ける
    rcases hstep with ⟨hp, hs⟩ | ⟨hp, hr⟩
    · exact Or.inl ⟨hp, hs⟩
    · exact Or.inr ⟨hp, remove_sound hwf hr⟩
  · -- step 3
    have hwf₁ : WellFormed s₁.tree := by
      rcases hstep with ⟨_, rfl⟩ | ⟨_, hr⟩
      · exact hwf
      · exact remove_preserves_wellformed hwf hr
    obtain ⟨nd₁, hnd₁⟩ : ∃ nd₁, s₁.tree.get? node = some nd₁ := by
      obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? node = some nd := by
        unfold ownerDocumentOf at hold
        cases hq : s.tree.get? node with
        | none => rw [hq] at hold; simp at hold
        | some nd => exact ⟨nd, rfl⟩
      rcases hstep with ⟨_, rfl⟩ | ⟨_, hr⟩
      · exact ⟨nd, hnd⟩
      · exact exists_get?_of_kindPreserving (shapePreserving_remove hr) hnd
    rcases hfinal with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · rw [if_pos he]
    · rw [if_neg he]
      exact ⟨documentAssigned_setOwnerDocument hwf₁ hnd₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Dom.Spec
