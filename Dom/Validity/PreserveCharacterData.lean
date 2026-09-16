import Dom.Validity.PreserveReplaceAll

/-!
# `replaceData` による保存

`data` しか変えないので、木の形に関する妥当性は三層とも保たれる。
-/

namespace Dom

/-! ## replaceData -/

/--
`replaceData` は `data` しか変えないので、木の形に関する妥当性は三層とも保たれる。

`withData` の補題（`Dom/Properties/CharacterData.lean`）がそのまま使える。
-/
theorem structurallyValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : StructurallyValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨d, spliced, hd, _, _, _, htree, _, _⟩ := replaceData_ok hr
  -- 新しい木の `get?` は、`n` のところだけ `data` が変わった値を返す。
  obtain ⟨nw, hget⟩ : ∃ nw, ∀ m, s'.tree.get? m =
      if m = n then some { d with data := nw } else s.tree.get? m :=
    ⟨spliced, fun m => by rw [htree]; exact get?_withData hd _ m⟩
  -- `n` の kind / parent / children は変わらない。
  have hsame : ∀ m dm, s'.tree.get? m = some dm →
      ∃ d₀, s.tree.get? m = some d₀ ∧ dm.kind = d₀.kind ∧ dm.parent = d₀.parent ∧
        dm.children = d₀.children := by
    intro m dm hm
    rw [hget] at hm
    split at hm
    · next he => subst he; cases hm; exact ⟨d, hd, rfl, rfl, rfl⟩
    · exact ⟨dm, hm, rfl, rfl, rfl⟩
  refine ⟨replaceData_preserves_wellformed h.wellFormed hr, ?_, ?_, ?_, ?_⟩
  · intro m dm hm hk
    obtain ⟨d₀, hd₀, hkk, hpp, _⟩ := hsame m dm hm
    rw [hpp]; exact h.documentHasNoParent m d₀ hd₀ (by rw [← hkk]; exact hk)
  · intro m dm hm hk
    obtain ⟨d₀, hd₀, hkk, hpp, _⟩ := hsame m dm hm
    rw [hpp]; exact h.fragmentHasNoParent m d₀ hd₀ (by rw [← hkk]; exact hk)
  · intro m dm hm hc
    obtain ⟨d₀, hd₀, hkk, _, hcc⟩ := hsame m dm hm
    rw [hkk]; exact h.childrenOnlyUnderContainers m d₀ hd₀ (by rw [← hcc]; exact hc)
  · intro m dm hm hk p hp pd hpd
    obtain ⟨d₀, hd₀, hkk, hpp, _⟩ := hsame m dm hm
    obtain ⟨pd₀, hpd₀, hkkp, _, _⟩ := hsame p pd hpd
    rw [hkkp]
    exact h.doctypeParentIsDocument m d₀ hd₀ (by rw [← hkk]; exact hk) p
      (by rw [← hpp]; exact hp) pd₀ hpd₀

theorem nodeDocumentsValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : NodeDocumentsValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨d, spliced, hd, _, _, _, htree, _, _⟩ := replaceData_ok hr
  have hget := get?_withData (t := s.tree) (n := n) (d := d) hd spliced
  have hown : ∀ m, ownerDocumentOf s'.tree m = ownerDocumentOf s.tree m := by
    intro m
    rw [htree]
    simp only [ownerDocumentOf_eq, hget]
    split
    · next he => rw [he, hd]; rfl
    · rfl
  refine ⟨?_, ?_⟩
  · intro m dm hm hk
    rw [htree, hget] at hm
    split at hm
    · next he => subst he; cases hm; exact h.documentIsOwnNodeDocument m d hd hk
    · exact h.documentIsOwnNodeDocument m dm hm hk
  · intro c p hp
    rw [hown, hown]
    refine h.treeEdgePreservesNodeDocument c p ?_
    rw [htree, parentOf_withData hd] at hp
    exact hp

theorem documentTreesValid_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : DocumentTreesValid s.tree)
    (hr : replaceData s n offset count data = .ok s') : DocumentTreesValid s'.tree := by
  obtain ⟨d, spliced, hd, _, _, _, htree, _, _⟩ := replaceData_ok hr
  refine documentTreesValid_of_sameShape ?_ ?_ h
  · intro m; rw [htree]; exact (shapePreserving_withData hd _).kind m
  · intro m; rw [htree]; exact childrenOf_withData hd _ m

end Dom
