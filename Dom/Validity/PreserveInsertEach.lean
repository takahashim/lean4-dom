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
      StructurallyValid s.tree →
      (∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .documentFragment) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
        ∀ pd, s.tree.get? parent = some pd → pd.kind = .document) →
      IsDocument s.tree doc →
      insertEach s parent child doc ns = .ok s' → StructurallyValid s'.tree
  | [], s, s', parent, child, doc, h, _, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, h, hpk, hnk, hnf, hdt, hdoc, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h hdoc ha
        have h₂ : StructurallyValid s₂.tree := by
          refine structurallyValid_insertAt h₁ ?_ ?_ ?_ ?_ (DOMState.mapTree_eq_ok hins).1
          · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
          · exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁
              (hnk n (List.mem_cons_self ..))
          · exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp₁
              (hnf n (List.mem_cons_self ..))
          · exact doctypeFact_of_kindPreserving hkp₁ (hdt n (List.mem_cons_self ..))
        have hkp₂ : ShapePreserving s₁.tree s₂.tree :=
          shapePreserving_insertAt (DOMState.mapTree_eq_ok hins).1
        have hkp : ShapePreserving s.tree s₂.tree := hkp₁.trans hkp₂
        refine structurallyValid_insertEach ns h₂ ?_ ?_ ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
            (hnk m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp
            (hnf m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact doctypeFact_of_kindPreserving hkp (hdt m (List.mem_cons_of_mem _ hm))
        · exact hdoc.map hkp

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
      StructurallyValid s.tree → NodeDocumentsValid s.tree →
      IsDocument s.tree doc →
      (∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true) →
      ownerDocumentOf s.tree parent = some doc →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .documentFragment) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind = .documentType →
        ∀ pd, s.tree.get? parent = some pd → pd.kind = .document) →
      insertEach s parent child doc ns = .ok s' → NodeDocumentsValid s'.tree
  | [], s, s', parent, child, doc, _, h, _, _, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, hs, h, hdoc, hpk, hpar, hnk, hnf, hdt, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have hnkn := hnk n (List.mem_cons_self ..)
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
        have hpk₁ : ∀ pd, s₁.tree.get? parent = some pd → pd.kind.canHaveChildren = true :=
          kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
        have hs₂ : StructurallyValid s₂.tree :=
          structurallyValid_insertAt hs₁ hpk₁
            (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁ hnkn)
            (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp₁
              (hnf n (List.mem_cons_self ..)))
            (doctypeFact_of_kindPreserving hkp₁ (hdt n (List.mem_cons_self ..))) hi'
        have hkp₂ : ShapePreserving s₁.tree s₂.tree := shapePreserving_insertAt hi'
        refine nodeDocumentsValid_insertEach ns hs₂ h₂ (hdoc.map (hkp₁.trans hkp₂)) ?_ ?_ ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₂ hpk₁
        · rw [ownerDocumentOf_insertAt hi']; exact hpar₁
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document)
            (hkp₁.trans hkp₂) (hnk m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment)
            (hkp₁.trans hkp₂) (hnf m (List.mem_cons_of_mem _ hm))
        · intro m hm
          exact doctypeFact_of_kindPreserving (hkp₁.trans hkp₂)
            (hdt m (List.mem_cons_of_mem _ hm))

end Dom
