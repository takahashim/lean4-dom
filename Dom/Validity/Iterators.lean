import Dom.Validity.AlgorithmPreservation

/-!
# iterator の妥当性の保存

`notes/research-foundation-roadmap.md` Phase A のうち、
`AdmissibleDOMState.iterators` の成分を algorithm ごとに保存する部分。

`remove` の pre-remove steps が iterator の reference を動かすので、
そこだけが本質的である。`insertAt` と `setOwnerDocument` は
parent の辺を増やす／何も変えないだけなので、既存の関係はそのまま残る。

`OtherDocumentIteratorsOutside`（別の node document の iterator は外す部分木の外にいる）
は `StructurallyValid` と `NodeDocumentsValid` と `IteratorsValid` から出るので、
三つを束ねた `IterCtx` を運ぶ。
-/

namespace Dom

/-- iterator の妥当性を運ぶのに必要な部分だけの束。 -/
structure IterCtx (s : DOMState) : Prop where
  structural : StructurallyValid s.tree
  nodeDocuments : NodeDocumentsValid s.tree
  iterators : IteratorsValid s

theorem IterCtx.wellFormed {s : DOMState} (h : IterCtx s) : WellFormed s.tree :=
  h.structural.wellFormed

theorem IterCtx.otherOutside {s : DOMState} (h : IterCtx s) (n : NodeId) :
    OtherDocumentIteratorsOutside s n :=
  otherDocumentIteratorsOutside_of h.wellFormed h.nodeDocuments h.iterators n

/-! ## parent の辺を変えない・増やすだけの操作 -/

/-- parent が同じなら ancestor 関係も同じである。 -/
theorem ancestor_congr {t t' : Tree} (hpar : ∀ m, parentOf t' m = parentOf t m)
    {a n : NodeId} (h : Ancestor t a n) : Ancestor t' a n := by
  induction h with
  | @step m hp => exact Ancestor.step (by rw [hpar]; exact hp)
  | @trans m b hp _ ih => exact Ancestor.trans (by rw [hpar]; exact hp) ih

/-- `insertAt` は `node` の parent を付けるだけなので、既存の ancestor 関係は残る。 -/
theorem ancestor_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hi : insertAt t parent node child = .ok t') {a n : NodeId}
    (h : Ancestor t a n) : Ancestor t' a n := by
  obtain ⟨pd, nd, hpd, hnd, hnone, hanc, hchild, rfl⟩ := insertAt_ok_cases hi
  have hnp : parentOf t node = none := by simp [parentOf, hnd, hnone]
  have key : ∀ x y, parentOf t y = some x →
      parentOf (insertAtIn t parent node child pd nd) y = some x := by
    intro x y hp
    have hne : y ≠ node := by
      intro he
      rw [he, hnp] at hp
      simp at hp
    rw [parentOf_insertAtIn hpd, if_neg hne]
    exact hp
  induction h with
  | step hp => exact Ancestor.step (key _ _ hp)
  | trans hp _ ih => exact Ancestor.trans (key _ _ hp) ih

/-- `insertAt` は iterator の妥当性を保つ。 -/
theorem validIterator_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hi : insertAt t parent node child = .ok t') {it : IteratorState}
    (h : ValidIterator t it) : ValidIterator t' it := by
  refine ⟨exists_get?_of_kindPreserving (shapePreserving_insertAt hi) h.1.choose_spec, ?_⟩
  rcases h.2 with he | ha
  · exact Or.inl he
  · exact Or.inr (ancestor_insertAt hi ha)

/-- `setOwnerDocument` は木の形を変えないので iterator の妥当性を保つ。 -/
theorem validIterator_setOwnerDocument {t : Tree} (n doc : NodeId) {it : IteratorState}
    (h : ValidIterator t it) : ValidIterator (setOwnerDocument t n doc) it := by
  refine ⟨exists_get?_of_kindPreserving (shapePreserving_setOwnerDocument t n doc)
    h.1.choose_spec, ?_⟩
  rcases h.2 with he | ha
  · exact Or.inl he
  · exact Or.inr (ancestor_congr (fun m => parentOf_setOwnerDocument t n doc m) ha)

/-! ## algorithm ごと -/

theorem iterCtx_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : IterCtx s) (hr : remove s n b = .ok s') : IterCtx s' := by
  obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
  exact ⟨structurallyValid_remove h.structural hr,
    nodeDocumentsValid_remove h.wellFormed h.nodeDocuments hr,
    remove_preserves_iterators_valid h.wellFormed hp h.iterators (h.otherOutside n) hr⟩

theorem iterCtx_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      IterCtx s → removeEach s ns b = .ok s' → IterCtx s'
  | [], _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ => exact iterCtx_removeEach ns (iterCtx_remove h h₁) hr

theorem iterCtx_adopt {s s' : DOMState} {node doc : NodeId}
    (h : IterCtx s) (hdoc : IsDocument s.tree doc)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (ha : adopt s node doc = .ok s') : IterCtx s' := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have h₁ : IterCtx s₁ := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact h
    · exact iterCtx_remove h hr
  rcases hfinal with rfl | rfl
  · exact h₁
  · refine ⟨structurallyValid_adopt h.structural hdoc ha,
      nodeDocumentsValid_adopt h.structural h.nodeDocuments hdoc hnk ha, ?_⟩
    intro it hit
    exact validIterator_setOwnerDocument _ _ (h₁.iterators it (by simpa using hit))

theorem iterCtx_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      IterCtx s → IsDocument s.tree doc →
      (∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true) →
      ownerDocumentOf s.tree parent = some doc →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.documentFragment) →
      (∀ n ∈ ns, ∀ nd, s.tree.get? n = some nd → nd.kind = NodeKind.documentType →
        ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document) →
      insertEach s parent child doc ns = .ok s' → IterCtx s'
  | [], s, s', parent, child, doc, h, _, _, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, h, hdoc, hpk, hpar, hnk, hnf, hdt, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have hnkn := hnk n (List.mem_cons_self ..)
        have h₁ : IterCtx s₁ := iterCtx_adopt h hdoc hnkn ha
        have hpar₁ : ownerDocumentOf s₁.tree parent = some doc :=
          adopt_ownerDocument_other ha hpar
        have hself : ownerDocumentOf s₁.tree n = some doc :=
          adopt_ownerDocument_self h.wellFormed ha
        have hi' := (DOMState.mapTree_eq_ok hins).1
        have hpk₁ : ∀ pd, s₁.tree.get? parent = some pd → pd.kind.canHaveChildren = true :=
          kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
        have hkp₂ : ShapePreserving s₁.tree s₂.tree := shapePreserving_insertAt hi'
        have h₂ : IterCtx s₂ := by
          refine ⟨structurallyValid_insertAt h₁.structural hpk₁
              (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁ hnkn)
              (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp₁
                (hnf n (List.mem_cons_self ..)))
              (doctypeFact_of_kindPreserving hkp₁ (hdt n (List.mem_cons_self ..))) hi',
            nodeDocumentsValid_insertAt h₁.nodeDocuments (by rw [hself, hpar₁]) hi', ?_⟩
          have hs₂ := (DOMState.mapTree_eq_ok hins).2
          intro it hit
          rw [hs₂] at hit ⊢
          simp only [DOMState.withTree_iterators] at hit
          exact validIterator_insertAt hi' (h₁.iterators it hit)
        refine iterCtx_insertEach ns h₂ (hdoc.map (hkp₁.trans hkp₂)) ?_ ?_ ?_ ?_ ?_ hi
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

/-- 木と iterator が同じなら `IterCtx` も同じである。 -/
theorem IterCtx.congr {s₁ s₂ : DOMState} (ht : s₂.tree = s₁.tree)
    (hit : s₂.iterators = s₁.iterators) (h : IterCtx s₁) : IterCtx s₂ := by
  refine ⟨by rw [ht]; exact h.structural, by rw [ht]; exact h.nodeDocuments, ?_⟩
  intro it hmem
  rw [ht]
  exact h.iterators it (by rw [← hit]; exact hmem)

theorem iterCtx_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool} (h : IterCtx s)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hnf : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.documentFragment)
    (hdt : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : IterCtx s' := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s' = sx ∨ s'.tree = sx.tree ∧ s'.iterators = sx.iterators := by
      split at hi
      · exact Or.inl (Except.ok.inj hi).symm
      · exact Or.inr ⟨by rw [← Except.ok.inj hi]; simp, by rw [← Except.ok.inj hi]; simp⟩
    have hx' : IterCtx sx := by
      unfold insertEachAt at hx
      split at hx
      · simp at hx
      · next pd hpd =>
        have hpd' : s.tree.get? parent = some pd := by simpa using hpd
        refine iterCtx_insertEach nodes
          (IterCtx.congr (by simp) (by simp) h) ?_ (by simpa using hpk) ?_
          (by simpa using hnk) (by simpa using hnf) (by simpa using hdt) hx
        · exact ⟨_, by simpa using
            (isDocument_ownerDocument h.wellFormed hpd').choose_spec.1,
            (isDocument_ownerDocument h.wellFormed hpd').choose_spec.2⟩
        · simp only [liveRangeInsertAdjust_tree]
          simp [ownerDocumentOf, hpd']
    rcases htree with rfl | ⟨ht, hit⟩
    · exact hx'
    · exact IterCtx.congr ht hit hx'

/-- `insert` は iterator の妥当性を保つ。 -/
theorem iterCtx_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : IterCtx s)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ nd, s.tree.get? node = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hi : insert s node parent child b = .ok s') : IterCtx s' := by
  unfold insert at hi
  split at hi
  · simp at hi
  · next nd hnd =>
    split at hi
    · split at hi
      · rw [← Except.ok.inj hi]; exact h
      · split at hi
        · simp at hi
        · next s₁ hre =>
          have h₁ : IterCtx s₁ := iterCtx_removeEach _ h hre
          have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
          have hfragkind : nd.kind ≠ NodeKind.document := by
            rename_i hfrag _ _
            intro hc; rw [hc] at hfrag; simp at hfrag
          refine iterCtx_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (IterCtx.congr (by simp) (by simp) h₁) ?_ ?_ ?_ ?_ hi
          · simpa using
              kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
          · intro m hm
            simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
              (child_not_document h.structural hnd hm)
          · intro m hm
            simpa using
              kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentFragment) hkp
                (child_not_fragment h.structural hnd hm)
          · intro m hm md hmd hkm _ _
            refine absurd hkm ?_
            have hx := kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.documentType) hkp
              (child_not_doctype h.structural hnd hfragkind hm)
            exact hx md (by simpa using hmd)
    · rename_i hnotfrag
      refine iterCtx_insertNodesAt h hpk ?_ ?_ ?_ hi
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact hnk
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        intro md hmd
        rw [hnd] at hmd
        cases hmd
        simpa using hnotfrag
      · intro m hm
        rcases List.mem_singleton.mp hm with rfl
        exact hdtf

/-- `move` は remove の pre-remove steps を走らせてから insert するだけである。 -/
theorem iterCtx_move {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : IterCtx s)
    (hpk : ∀ pd, s.tree.get? newParent = some pd → pd.kind.canHaveChildren = true)
    (hm : move s node newParent child = .ok s') : IterCtx s' := by
  obtain ⟨s₁, hr, hins⟩ := move_eq_remove_insertAt hm
  obtain ⟨s₂, hr₂, hit⟩ := move_iterators hm
  have hs : s₂ = s₁ := by
    rw [hr] at hr₂
    exact (Except.ok.inj hr₂).symm
  rw [hs] at hit
  have h₁ : IterCtx s₁ := iterCtx_remove h hr
  refine ⟨structurallyValid_move h.structural hpk hm,
    nodeDocumentsValid_move h.wellFormed h.nodeDocuments hm, ?_⟩
  intro it hmem
  rw [hit] at hmem
  exact validIterator_insertAt hins (h₁.iterators it hmem)

/-- `moveBefore` は receiver の kind を検査してから `move` を呼ぶ。 -/
theorem iterCtx_moveBefore {s s' : DOMState} {parent node : NodeId} {child : Option NodeId}
    (h : IterCtx s) (hm : moveBefore s parent node child = .ok s') : IterCtx s' := by
  obtain ⟨pd, ref, hpd, hk, hmove⟩ := moveBefore_ok hm
  refine iterCtx_move h ?_ hmove
  intro pd' hpd'
  obtain rfl : pd' = pd := by rw [hpd] at hpd'; exact (Option.some.inj hpd').symm
  exact hk

theorem iterCtx_replace {s s' : DOMState} {child node parent : NodeId}
    (h : IterCtx s) (hr : replace s child node parent = .ok s') : IterCtx s' := by
  unfold replace at hr
  split at hr
  · simp at hr
  · next hv =>
    split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        have hkp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_adopt ha
        have h₁ : IterCtx s₁ := iterCtx_adopt h (isDocument_ownerDocument h.wellFormed hpd)
          (ensurePreInsertionValidity_nodeNotDocument hv) ha
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have hstep : IterCtx s₂ ∧ ShapePreserving s₁.tree s₂.tree := by
            revert hrm
            split
            · intro hrm
              rw [← Except.ok.inj hrm]
              exact ⟨h₁, ShapePreserving.refl _⟩
            · intro hrm
              have hrm' : remove s₁ child true = .ok s₂ := by simpa using hrm
              exact ⟨iterCtx_remove h₁ hrm', shapePreserving_remove hrm'⟩
          obtain ⟨h₂, hkp₂⟩ := hstep
          have hkp : ShapePreserving s.tree s₂.tree := hkp₁.trans hkp₂
          split at hr
          · simp at hr
          · next s₃ hi =>
            have h₃ : IterCtx s₃ :=
              iterCtx_insert h₂
                (kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
                  (ensurePreInsertionValidity_parentCanHaveChildren hv))
                (kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
                  (ensurePreInsertionValidity_nodeNotDocument hv))
                (doctypeFact_of_kindPreserving hkp
                  (ensurePreInsertionValidity_doctypeParentIsDocument hv)) hi
            rw [← Except.ok.inj hr]
            exact IterCtx.congr (by simp) (by simp) h₃

theorem iterCtx_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : IterCtx s)
    (hpk : ∀ n, node = some n → ∀ pd, s.tree.get? parent = some pd →
      pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hr : replaceAll s node parent = .ok s') : IterCtx s' := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    have h₁ : IterCtx s₁ := iterCtx_removeEach _ h hre
    have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
    split at hr
    · simp at hr
    · next s₂ hins =>
      have h₂ : IterCtx s₂ := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact h₁
        · next _ _ m =>
          intro hins
          refine iterCtx_insert h₁ ?_ ?_ ?_ (by simpa using hins)
          · exact kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
              (hpk m rfl)
          · exact kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document)
              (hnk m rfl)
          · exact doctypeFact_of_kindPreserving hkp (hdtf m rfl)
      rw [← Except.ok.inj hr]
      exact IterCtx.congr (by simp) (by simp) h₂

/-! ## NodeIterator の走査 -/

/--
`nextNode()` / `previousNode()` が返す iterator は valid のままである。

collection は root の preorder なので、返る reference は root の inclusive descendant であり、
木の中にもある。
-/
theorem validIterator_of_mem_collection {t : Tree} (hwf : WellFormed t) {it : IteratorState}
    (h : ValidIterator t it) {n : NodeId} (hn : n ∈ iteratorCollection t it.root) :
    ∃ d, t.get? n = some d ∧ InclusiveDescendant t n it.root := by
  obtain ⟨rd, hrd⟩ := exists_root_of_validIterator hwf h
  have hdesc : InclusiveDescendant t n it.root :=
    (mem_preorder_iff hwf hrd n).mp hn
  obtain ⟨d, hd⟩ : ∃ d, t.get? n = some d := by
    rcases hdesc with rfl | hanc
    · exact ⟨rd, hrd⟩
    · obtain ⟨p, hp⟩ := hanc.parent_isSome
      obtain ⟨d, hd, _⟩ := parentOf_eq_some hp
      exact ⟨d, hd⟩
  exact ⟨d, hd, hdesc⟩

theorem validIterator_nextNode {t : Tree} (hwf : WellFormed t) {it it' : IteratorState}
    {n : NodeId} (h : ValidIterator t it) (hstep : nextNode t it = some (n, it')) :
    ValidIterator t it' := by
  unfold nextNode at hstep
  split at hstep
  · simp at hstep
  · next u v hq =>
    split at hstep
    · simp at hstep
    · next m hm =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hstep
      rw [← hstep.2]
      -- 候補はどれも collection の要素である。
      have hmem : m ∈ iteratorCollection t it.root := by
        have hmc : m ∈ (if it.pointerBeforeReference then it.reference :: v else v) :=
          List.mem_of_find?_eq_some hm
        rw [ListUtil.splitAt?_eq_some hq]
        split at hmc
        · rcases List.mem_cons.mp hmc with rfl | hmv
          · exact List.mem_append_right _ List.mem_cons_self
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hmv)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hmc)
      obtain ⟨d, hd, hdesc⟩ := validIterator_of_mem_collection hwf h hmem
      exact ⟨⟨d, hd⟩, hdesc⟩

theorem validIterator_previousNode {t : Tree} (hwf : WellFormed t) {it it' : IteratorState}
    {n : NodeId} (h : ValidIterator t it) (hstep : previousNode t it = some (n, it')) :
    ValidIterator t it' := by
  unfold previousNode at hstep
  split at hstep
  · simp at hstep
  · next u v hq =>
    split at hstep
    · simp at hstep
    · next m hm =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hstep
      rw [← hstep.2]
      have hmem : m ∈ iteratorCollection t it.root := by
        have hmc : m ∈ (if it.pointerBeforeReference then u.reverse
                        else it.reference :: u.reverse) := List.mem_of_find?_eq_some hm
        rw [ListUtil.splitAt?_eq_some hq]
        split at hmc
        · exact List.mem_append_left _ (List.mem_reverse.mp hmc)
        · rcases List.mem_cons.mp hmc with rfl | hmu
          · exact List.mem_append_right _ List.mem_cons_self
          · exact List.mem_append_left _ (List.mem_reverse.mp hmu)
      obtain ⟨d, hd, hdesc⟩ := validIterator_of_mem_collection hwf h hmem
      exact ⟨⟨d, hd⟩, hdesc⟩

end Dom
