import Dom.Validity.Preservation
import Dom.Properties.Algorithms

/-!
# §4.2.3 の algorithm による admissibility の保存

`notes/research-foundation-roadmap.md` Phase A の完了条件
「全対象 operation の `preserves_admissible`」に向けて、
まず木に関する三つの層（`StructurallyValid` / `NodeDocumentsValid` /
`DocumentTreesValid`）を algorithm ごとに積み上げる。

`remove` は node を外すだけなので、三つとも無条件に保たれる。
`insert` 側は validity 検査が前提を確立するので、そこで primitive の条件を discharge する。
-/

namespace Dom

/-! ## ensure pre-insert validity が確立する kind の事実 -/

/--
step 1。parent は Document / DocumentFragment / Element のいずれかである。
すなわち children を持てる kind である。
-/
theorem ensurePreInsertionValidity_parentCanHaveChildren {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true := by
  intro pd hpd
  unfold ensurePreInsertionValidity at h
  rw [hpd] at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · next hk => simp at h
    · next hk =>
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hk
      cases hkk : pd.kind <;> simp_all [NodeKind.canHaveChildren]

/-- step 4。node は DocumentFragment / DocumentType / Element / CharacterData であり、Document ではない。 -/
theorem ensurePreInsertionValidity_nodeNotDocument {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ nd, t.get? node = some nd → nd.kind ≠ .document := by
  intro nd hnd
  unfold ensurePreInsertionValidity at h
  split at h
  · simp at h
  · next pd hpd =>
    rw [hnd] at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · next hk => simp at h
          · next hk =>
            simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hk
            cases hkk : nd.kind <;> simp_all [NodeKind.isCharacterData]

/-! ## remove -/

theorem structurallyValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : StructurallyValid s.tree) (hr : remove s n b = .ok s') :
    StructurallyValid s'.tree :=
  structurallyValid_detach h (remove_ok hr).2

theorem nodeDocumentsValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : NodeDocumentsValid s.tree) (hr : remove s n b = .ok s') :
    NodeDocumentsValid s'.tree :=
  nodeDocumentsValid_detach hwf h (remove_ok hr).2

/--
`remove` は Document の children から一つ外すだけなので、document tree の制約は保たれる。

element / doctype / Text の個数はどれも増えず、
element より後ろの doctype も増えないためである。
-/
theorem documentChildrenOk_of_detach {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (hd : detach t n = .ok t') {doc : NodeId}
    (h : DocumentChildrenOk t doc) : DocumentChildrenOk t' doc := by
  have hkind : ∀ m, kindOf t' m = kindOf t m := kindPreserving_detach hd
  -- children は、旧 parent なら `removeAll`、それ以外なら不変。
  have hch : ∃ a, childrenOf t' doc = ListUtil.removeAll (childrenOf t doc) a := by
    cases hp : parentOf t n with
    | none =>
      exact ⟨n, by
        rw [detach_of_no_parent hp (by
          rcases detach_ok_cases hd with ⟨d, hdd, _, _⟩ | ⟨d, _, _, hdd, _, _, _⟩ <;>
            simp [hdd])] at hd
        rw [← Except.ok.inj hd, ListUtil.removeAll_eq_self]
        intro hmem
        exact absurd (parentOf_of_mem_childrenOf hwf hmem) (by rw [hp]; simp)⟩
    | some p =>
      by_cases hdp : doc = p
      · subst hdp
        exact ⟨n, detach_childrenOf hwf hp hd⟩
      · exact ⟨n, by
          rw [detach_childrenOf_ne hp hd hdp, ListUtil.removeAll_eq_self]
          intro hmem
          have := parentOf_of_mem_childrenOf hwf hmem
          rw [hp] at this
          exact hdp (Option.some.inj this).symm⟩
  obtain ⟨a, hch⟩ := hch
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold elementChildren at h1 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll a _ _) h1
  · unfold doctypeChildren at h2 ⊢
    simp only [hch, hkind]
    exact Nat.le_trans (ListUtil.length_filter_removeAll a _ _) h2
  · unfold textChildren at h3 ⊢
    simp only [hch, hkind]
    exact ListUtil.filter_removeAll_eq_nil h3
  · intro e he
    have hmemA : e ∈ ListUtil.removeAll (childrenOf t doc) a ∧
        (kindOf t e == some NodeKind.element) = true := by
      unfold elementChildren at he
      simp only [hch, hkind] at he
      exact List.mem_filter.mp he
    have hne : e ≠ a := ((ListUtil.mem_removeAll _ _ _).mp hmemA.1).1
    have hmem : e ∈ childrenOf t doc := ((ListUtil.mem_removeAll _ _ _).mp hmemA.1).2
    have he' : e ∈ elementChildren t doc := by
      unfold elementChildren
      exact List.mem_filter.mpr ⟨hmem, hmemA.2⟩
    have h4e := h4 e he'
    unfold doctypeFollows at h4e ⊢
    simp only [hch, hkind]
    cases hs : ListUtil.splitAt? (childrenOf t doc) e with
    | none =>
      exfalso
      have := ListUtil.splitAt?_isSome_of_mem hmem
      rw [hs] at this
      simp at this
    | some q =>
      obtain ⟨u, v⟩ := q
      rw [hs] at h4e
      rw [ListUtil.splitAt?_removeAll hne hs]
      rw [Bool.eq_false_iff] at h4e ⊢
      intro hcon
      obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hcon
      exact h4e (List.any_eq_true.mpr ⟨x, ((ListUtil.mem_removeAll _ _ _).mp hx).2, hxk⟩)

/--
`remove` は Document の children から一つ外すだけなので、document tree の制約は保たれる。

element / doctype / Text の個数はどれも増えず、
element より後ろの doctype も増えないためである。
-/
theorem documentTreesValid_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : DocumentTreesValid s.tree) (hr : remove s n b = .ok s') :
    DocumentTreesValid s'.tree := by
  have hd := (remove_ok hr).2
  refine ⟨fun doc d hdoc hk => ?_⟩
  refine documentChildrenOk_of_detach hwf hd ?_
  have hkind := kindPreserving_detach hd doc
  cases hdoc' : s.tree.get? doc with
  | none =>
    exfalso
    rw [hdoc, hdoc'] at hkind
    simp at hkind
  | some d' =>
    refine h.documentChildren doc d' hdoc' ?_
    rw [hdoc, hdoc'] at hkind
    simpa [hk] using hkind.symm

/-! ## removeEach -/

theorem structurallyValid_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      StructurallyValid s.tree → removeEach s ns b = .ok s' → StructurallyValid s'.tree
  | [], _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ => exact structurallyValid_removeEach ns (structurallyValid_remove h h₁) hr

theorem nodeDocumentsValid_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      StructurallyValid s.tree → NodeDocumentsValid s.tree → removeEach s ns b = .ok s' →
      NodeDocumentsValid s'.tree
  | [], _, _, _, _, h, hr => by rw [← Except.ok.inj hr]; exact h
  | n :: ns, s, s', b, hs, h, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      exact nodeDocumentsValid_removeEach ns (structurallyValid_remove hs h₁)
        (nodeDocumentsValid_remove hs.wellFormed h h₁) hr

/-! ## kind の事実は kind を変えない操作で移る -/

theorem kindFact_of_kindPreserving {t t' : Tree} (h : KindPreserving t t') {n : NodeId}
    {P : NodeKind → Prop} (hp : ∀ d, t.get? n = some d → P d.kind) :
    ∀ d, t'.get? n = some d → P d.kind := by
  intro d hd
  have hk := h n
  rw [hd] at hk
  cases hd' : t.get? n with
  | none => rw [hd'] at hk; simp at hk
  | some d' =>
    rw [hd'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    rw [hk]
    exact hp d' hd'

/-! ## adopt -/

theorem structurallyValid_adopt {s s' : DOMState} {node doc : NodeId}
    (h : StructurallyValid s.tree) (hdoc : IsDocument s.tree doc)
    (ha : adopt s node doc = .ok s') : StructurallyValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hstep' : StructurallyValid s₁.tree ∧ KindPreserving s.tree s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ⟨h, KindPreserving.refl _⟩
    · exact ⟨structurallyValid_remove h hr, kindPreserving_remove hr⟩
  rcases hfinal with rfl | rfl
  · exact hstep'.1
  · obtain ⟨dd, hdd, hk⟩ := hdoc.map hstep'.2
    exact structurallyValid_setOwnerDocument hstep'.1.wellFormed hstep'.1 hdd hk

/--
adopt は node document を整える step である。

step 2 の remove で node は parent を失うので、step 3 の `setOwnerDocument` は
閉じた部分木を書き換える。node が Document でないことは insert 側の validity 検査から来る。
-/
theorem nodeDocumentsValid_adopt {s s' : DOMState} {node doc : NodeId}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hdoc : IsDocument s.tree doc)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ .document)
    (ha : adopt s node doc = .ok s') : NodeDocumentsValid s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hstep' : NodeDocumentsValid s₁.tree ∧ StructurallyValid s₁.tree ∧
      KindPreserving s.tree s₁.tree ∧ parentOf s₁.tree node = none := by
    rcases hstep with ⟨hnp, rfl⟩ | hr
    · exact ⟨h, hs, KindPreserving.refl _, hnp⟩
    · exact ⟨nodeDocumentsValid_remove hs.wellFormed h hr, structurallyValid_remove hs hr,
        kindPreserving_remove hr, remove_parentOf hr⟩
  rcases hfinal with rfl | rfl
  · exact hstep'.1
  · refine nodeDocumentsValid_setOwnerDocument hstep'.2.1.wellFormed hstep'.2.1 hstep'.1
      hstep'.2.2.2 ?_
    exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hstep'.2.2.1 hnk

/-! ## adopt が node document に与える効果 -/

/-- adopt の後、node の node document は `doc` になっている。 -/
theorem adopt_ownerDocument_self {s s' : DOMState} {node doc : NodeId}
    (hwf : WellFormed s.tree) (ha : adopt s node doc = .ok s')
    {nd : NodeData} (hnd : s.tree.get? node = some nd) :
    ownerDocumentOf s'.tree node = some doc := by
  unfold adopt at ha
  split at ha
  · simp at ha
  · next old hold =>
    split at ha
    · simp at ha
    · next s₁ hr =>
      have hown₁ : ownerDocumentOf s₁.tree node = some old := by
        revert hr
        split
        · intro hr; rw [← Except.ok.inj hr]; exact hold
        · intro hr
          rw [ownerDocumentOf_detach (remove_ok hr).2]; exact hold
      have hwf₁ : WellFormed s₁.tree := by
        revert hr
        split
        · intro hr; rw [← Except.ok.inj hr]; exact hwf
        · intro hr; exact remove_preserves_wellformed hwf hr
      obtain ⟨nd₁, hnd₁⟩ : ∃ nd₁, s₁.tree.get? node = some nd₁ := by
        cases h1 : s₁.tree.get? node with
        | some x => exact ⟨x, rfl⟩
        | none => rw [ownerDocumentOf, h1] at hown₁; simp at hown₁
      split at ha
      · next he => rw [← Except.ok.inj ha, hown₁, he]
      · rw [← Except.ok.inj ha]
        show ownerDocumentOf (setOwnerDocument s₁.tree node doc) node = some doc
        rw [ownerDocumentOf_setOwnerDocument_eq, hnd₁]
        simp [mem_preorder_self hwf₁ hnd₁]

/-- adopt は「parent の node document が `doc` である」という条件を壊さない。 -/
theorem adopt_ownerDocument_other {s s' : DOMState} {node doc parent : NodeId}
    (ha : adopt s node doc = .ok s') (hp : ownerDocumentOf s.tree parent = some doc) :
    ownerDocumentOf s'.tree parent = some doc := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hp₁ : ownerDocumentOf s₁.tree parent = some doc := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact hp
    · rw [ownerDocumentOf_detach (remove_ok hr).2]; exact hp
  rcases hfinal with rfl | rfl
  · exact hp₁
  · show ownerDocumentOf (setOwnerDocument s₁.tree node doc) parent = some doc
    rw [ownerDocumentOf_setOwnerDocument_eq]
    cases h1 : s₁.tree.get? parent with
    | none => rw [ownerDocumentOf, h1] at hp₁; simp at hp₁
    | some pd =>
      simp only [Option.map_some]
      split
      · rfl
      · rw [ownerDocumentOf, h1] at hp₁; simpa using hp₁

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
      IsDocument s.tree doc →
      insertEach s parent child doc ns = .ok s' → StructurallyValid s'.tree
  | [], s, s', parent, child, doc, h, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, h, hpk, hnk, hdoc, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        have h₁ : StructurallyValid s₁.tree := structurallyValid_adopt h hdoc ha
        have h₂ : StructurallyValid s₂.tree := by
          refine structurallyValid_insertAt h₁ ?_ ?_ (DOMState.mapTree_eq_ok hins).1
          · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
          · exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁
              (hnk n (List.mem_cons_self ..))
        have hkp₂ : KindPreserving s₁.tree s₂.tree :=
          kindPreserving_insertAt (DOMState.mapTree_eq_ok hins).1
        have hkp : KindPreserving s.tree s₂.tree := hkp₁.trans hkp₂
        refine structurallyValid_insertEach ns h₂ ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
            (hnk m (List.mem_cons_of_mem _ hm))
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
      insertEach s parent child doc ns = .ok s' → NodeDocumentsValid s'.tree
  | [], s, s', parent, child, doc, _, h, _, _, _, _, hi => by
    rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact h
  | n :: ns, s, s', parent, child, doc, hs, h, hdoc, hpk, hpar, hnk, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        have hkp₁ : KindPreserving s.tree s₁.tree := kindPreserving_adopt ha
        have hnkn := hnk n (List.mem_cons_self ..)
        have hs₁ : StructurallyValid s₁.tree := structurallyValid_adopt hs hdoc ha
        have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_adopt hs h hdoc hnkn ha
        have hpar₁ : ownerDocumentOf s₁.tree parent = some doc :=
          adopt_ownerDocument_other ha hpar
        -- node が木の中にあることは adopt の成功から出る。
        obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? n = some nd := by
          unfold adopt at ha
          split at ha
          · simp at ha
          · next old hold =>
            cases h1 : s.tree.get? n with
            | some x => exact ⟨x, rfl⟩
            | none => rw [ownerDocumentOf, h1] at hold; simp at hold
        have hself : ownerDocumentOf s₁.tree n = some doc :=
          adopt_ownerDocument_self hs.wellFormed ha hnd
        have hi' := (DOMState.mapTree_eq_ok hins).1
        have h₂ : NodeDocumentsValid s₂.tree :=
          nodeDocumentsValid_insertAt h₁ (by rw [hself, hpar₁]) hi'
        have hpk₁ : ∀ pd, s₁.tree.get? parent = some pd → pd.kind.canHaveChildren = true :=
          kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₁ hpk
        have hs₂ : StructurallyValid s₂.tree :=
          structurallyValid_insertAt hs₁ hpk₁
            (kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp₁ hnkn) hi'
        have hkp₂ : KindPreserving s₁.tree s₂.tree := kindPreserving_insertAt hi'
        refine nodeDocumentsValid_insertEach ns hs₂ h₂ (hdoc.map (hkp₁.trans hkp₂)) ?_ ?_ ?_ hi
        · exact kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp₂ hpk₁
        · rw [ownerDocumentOf_insertAt hi']; exact hpar₁
        · intro m hm
          exact kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document)
            (hkp₁.trans hkp₂) (hnk m (List.mem_cons_of_mem _ hm))

/-! ## insert -/

/-- `StructurallyValid` から、木の中の node の children は Document ではない。 -/
theorem child_not_document {t : Tree} (h : StructurallyValid t) {p c : NodeId} {pd : NodeData}
    (hpd : t.get? p = some pd) (hc : c ∈ pd.children) :
    ∀ cd, t.get? c = some cd → cd.kind ≠ .document := by
  intro cd hcd hk
  obtain ⟨cd', hcd', hcdp⟩ := h.wellFormed.parent_child p pd hpd c hc
  rw [hcd] at hcd'
  cases hcd'
  exact absurd hcdp (by rw [h.documentHasNoParent c cd hcd hk]; simp)

theorem structurallyValid_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (h : StructurallyValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : StructurallyValid s'.tree := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s'.tree = sx.tree := by
      split at hi
      · rw [← Except.ok.inj hi]
      · rw [← Except.ok.inj hi]; simp
    rw [htree]
    unfold insertEachAt at hx
    split at hx
    · simp at hx
    · next pd hpd =>
      have hpd' : s.tree.get? parent = some pd := by simpa using hpd
      refine structurallyValid_insertEach nodes (by simpa using h) (by simpa using hpk)
        (by simpa using hnk) ?_ hx
      exact ⟨_, by simpa using (isDocument_ownerDocument h.wellFormed hpd').choose_spec.1,
        (isDocument_ownerDocument h.wellFormed hpd').choose_spec.2⟩

/--
PLAN §6.3 の形。`insert` は構造上の妥当性を保つ。

fragment を展開する側では、入れる node は fragment の children なので
「Document は parent を持たない」という invariant から Document でないことが出る。
単独の node の側では validity 検査の step 4 から出る。
-/
theorem structurallyValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : StructurallyValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : StructurallyValid s'.tree := by
  have hpk := ensurePreInsertionValidity_parentCanHaveChildren hv
  unfold insert at hi
  split at hi
  · simp at hi
  · next nd hnd =>
    split at hi
    · -- fragment を展開する
      split at hi
      · rw [← Except.ok.inj hi]; exact h
      · split at hi
        · simp at hi
        · next s₁ hre =>
          have h₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
          have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
          refine structurallyValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (by simpa using h₁) ?_ ?_ hi
          · simpa using
              kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
          · intro m hm
            simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
              (child_not_document h hnd hm)
    · -- 単独の node
      refine structurallyValid_insertNodesAt h hpk ?_ hi
      intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact ensurePreInsertionValidity_nodeNotDocument hv

theorem nodeDocumentsValid_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hpk : ∀ pd, s.tree.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ n ∈ nodes, ∀ nd, s.tree.get? n = some nd → nd.kind ≠ .document)
    (hi : insertNodesAt s parent child nodes b = .ok s') : NodeDocumentsValid s'.tree := by
  unfold insertNodesAt at hi
  simp only at hi
  split at hi
  · simp at hi
  · next sx hx =>
    have htree : s'.tree = sx.tree := by
      split at hi
      · rw [← Except.ok.inj hi]
      · rw [← Except.ok.inj hi]; simp
    rw [htree]
    unfold insertEachAt at hx
    split at hx
    · simp at hx
    · next pd hpd =>
      have hpd' : s.tree.get? parent = some pd := by simpa using hpd
      refine nodeDocumentsValid_insertEach nodes (by simpa using hs) (by simpa using h)
        ?_ (by simpa using hpk) ?_ (by simpa using hnk) hx
      · exact ⟨_, by simpa using (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.1,
          (isDocument_ownerDocument hs.wellFormed hpd').choose_spec.2⟩
      · simp only [liveRangeInsertAdjust_tree]
        simp [ownerDocumentOf, hpd']

/-- PLAN §6.3 の形。`insert` は node document の整合性を保つ。 -/
theorem nodeDocumentsValid_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool}
    (hs : StructurallyValid s.tree) (h : NodeDocumentsValid s.tree)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : NodeDocumentsValid s'.tree := by
  have hpk := ensurePreInsertionValidity_parentCanHaveChildren hv
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
          have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ hs hre
          have h₁ : NodeDocumentsValid s₁.tree := nodeDocumentsValid_removeEach _ hs h hre
          have hkp : KindPreserving s.tree s₁.tree := kindPreserving_removeEach _ hre
          refine nodeDocumentsValid_insertNodesAt (s := queueTreeMutationRecord s₁ node []
            nd.children none none) (by simpa using hs₁) (by simpa using h₁) ?_ ?_ hi
          · simpa using
              kindFact_of_kindPreserving (P := fun k => k.canHaveChildren = true) hkp hpk
          · intro m hm
            simpa using kindFact_of_kindPreserving (P := fun k => k ≠ NodeKind.document) hkp
              (child_not_document hs hnd hm)
    · refine nodeDocumentsValid_insertNodesAt hs h hpk ?_ hi
      intro m hm
      rcases List.mem_singleton.mp hm with rfl
      exact ensurePreInsertionValidity_nodeNotDocument hv

end Dom
