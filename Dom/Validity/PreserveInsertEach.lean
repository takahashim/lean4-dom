import Dom.Validity.PreserveAdopt

/-!
# `insertEach` による保存
-/

namespace Dom

/-! ## insertEach -/

/--
`insertEach` は node ごとに adopt してから `insertAt` する。

必要な前提は次の三つで、いずれも §4.2.3 の validity 検査か invariant から出る。

* parent は children を持てる kind である（step 1）。
* 入れる node はどれも Document でない（step 4、fragment の場合は
  「Document は parent を持たない」という invariant から）。
* `doc` は Document である（parent の node document なので `WellFormed` から）。
-/
theorem structurallyValid_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      StructurallyValid s.tree → InsertFacts s.tree parent ns → IsDocument s.tree doc →
      insertEach s parent child doc ns = .ok s' → StructurallyValid s'.tree
  | [], s, s', parent, child, doc, h, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, h, hf, hdoc, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h hdoc ha
        have hf₁ : InsertFacts s₁.tree parent (n :: ns) := hf.congr hkp₁
        have hi' := (DOMState.mapTree_eq_ok hins).1
        have h₂ : StructurallyValid s₂.tree :=
          structurallyValid_insertAt h₁ hf₁.parentCanHaveChildren
            (hf₁.notDocument n (List.mem_cons_self ..))
            (hf₁.notFragment n (List.mem_cons_self ..))
            (hf₁.doctypeParentIsDocument n (List.mem_cons_self ..)) hi'
        have hkp : ShapePreserving s.tree s₂.tree :=
          hkp₁.trans (shapePreserving_insertAt hi')
        exact structurallyValid_insertEach ns h₂ (hf.congr hkp).tail (hdoc.map hkp) hi

/--
`insertEach` の node document 保存。

ループ不変条件は「parent の node document が `doc` である」ことだけでよい。
adopt はこれを壊さない（parent が部分木の外なら不変、中なら `doc` に揃う）。
各 node は adopt の後 node document が `doc` になるので、
`insertAt` が要求する「辺の両端が同じ node document」が満たされる。
-/
theorem nodeDocumentsValid_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      StructurallyValid s.tree → NodeDocumentsValid s.tree → IsDocument s.tree doc →
      InsertFacts s.tree parent ns → ownerDocumentOf s.tree parent = some doc →
      insertEach s parent child doc ns = .ok s' → NodeDocumentsValid s'.tree
  | [], s, s', parent, child, doc, _, h, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, hs, h, hdoc, hf, hpar, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have hnkn := hf.notDocument n (List.mem_cons_self ..)
        have hs₁ : StructurallyValid s₁.tree := structurallyValid_adopt hs hdoc ha
        have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_adopt hs h hdoc hnkn ha
        have hpar₁ : ownerDocumentOf s₁.tree parent = some doc :=
          adopt_ownerDocument_other ha hpar
        -- node が木の中にあることは adopt の成功から出る。
        obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? n = some nd := by
          obtain ⟨_, _, hold, -, -⟩ := adopt_cases ha
          cases h1 : s.tree.get? n with
          | some x => exact ⟨x, rfl⟩
          | none => rw [ownerDocumentOf_eq, h1] at hold; simp at hold
        have hself : ownerDocumentOf s₁.tree n = some doc :=
          adopt_ownerDocument_self hs.wellFormed ha
        have hi' := (DOMState.mapTree_eq_ok hins).1
        have h₂ : NodeDocumentsValid s₂.tree :=
          nodeDocumentsValid_insertAt h₁ (by rw [hself, hpar₁]) hi'
        have hf₁ : InsertFacts s₁.tree parent (n :: ns) := hf.congr hkp₁
        have hs₂ : StructurallyValid s₂.tree :=
          structurallyValid_insertAt hs₁ hf₁.parentCanHaveChildren
            (hf₁.notDocument n (List.mem_cons_self ..))
            (hf₁.notFragment n (List.mem_cons_self ..))
            (hf₁.doctypeParentIsDocument n (List.mem_cons_self ..)) hi'
        have hkp : ShapePreserving s.tree s₂.tree :=
          hkp₁.trans (shapePreserving_insertAt hi')
        refine nodeDocumentsValid_insertEach ns hs₂ h₂ (hdoc.map hkp) (hf.congr hkp).tail ?_ hi
        rw [ownerDocumentOf_insertAt hi']; exact hpar₁

end Dom
