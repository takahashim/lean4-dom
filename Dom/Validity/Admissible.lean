import Dom.Validity.Attributes
import Dom.Validity.Observers
import Dom.Observer.Deliver

/-!
# `AdmissibleDOMState` の保存

`notes/research-foundation-roadmap.md` Phase A の完了条件
「全対象 operation の `preserves_admissible`」。

七つの成分のうち木に関する三つ（`Dom/Validity/AlgorithmPreservation.lean`）、
iterator（`Dom/Validity/Iterators.lean`）、
observer registration（`Dom/Validity/Observers.lean`）、
attribute（`Dom/Validity/Attributes.lean`）は個別に示してある。
ここでは残る range の端点を埋めてから、七つをまとめる。

`ChildCountKind`（node length が children の個数であること）は
`StructurallyValid` から出る（`Dom/Validity/Derived.lean`）ので、
定理の仮定として外から渡す必要はもう無い。
-/

namespace Dom


/-! ## pre-insert の step 2-3（reference child のずらし） -/

/-- step 4 と step 7-9 の否定から、node は doctype である。 -/
theorem kind_documentType_of {k : NodeKind}
    (h4 : ¬ (!(k == NodeKind.documentFragment || k == NodeKind.documentType ||
      k == NodeKind.element || k.isCharacterData)) = true)
    (h7 : ¬ k.isCharacterData = true) (h8 : ¬ (k == NodeKind.documentFragment) = true)
    (h9 : ¬ (k == NodeKind.element) = true) : k = NodeKind.documentType := by
  cases k <;> simp_all [NodeKind.isCharacterData]

/--
`ensure pre-insertion validity` のうち `child` に依存するのは
step 3 と step 8-11 の検査だけである。
-/
theorem ensurePreInsertionValidity_child_congr {t : Tree} {node parent : NodeId}
    {c₁ c₂ : Option NodeId} {excl : List NodeId}
    (h3 : childHasParent t c₂ parent = true)
    (hel : ∀ nd, t.get? node = some nd →
      checkElementInsertion t parent c₁ excl = .ok () →
      checkElementInsertion t parent c₂ excl = .ok ())
    (hdt : ∀ nd, t.get? node = some nd → nd.kind = NodeKind.documentType →
      checkDoctypeInsertion t parent c₁ excl = .ok () →
      checkDoctypeInsertion t parent c₂ excl = .ok ())
    (hv : ensurePreInsertionValidity t node parent c₁ excl = .ok ()) :
    ensurePreInsertionValidity t node parent c₂ excl = .ok () := by
  unfold ensurePreInsertionValidity at hv ⊢
  split at hv
  · simp at hv
  · next pd hpd =>
    split at hv
    · simp at hv
    · next nd hnd =>
      split at hv
      · simp at hv
      · next h1 =>
        rw [if_neg h1]
        split at hv
        · simp at hv
        · next h2 =>
          rw [if_neg h2]
          rw [if_neg (show ¬(!childHasParent t c₂ parent) = true by simpa using h3)]
          split at hv
          · simp at hv
          · split at hv
            · simp at hv
            · next h4 =>
              rw [if_neg h4]
              split at hv
              · next h5 => rw [if_pos h5]; exact hv
              · next h5 =>
                rw [if_neg h5]
                split at hv
                · simp at hv
                · next h6 =>
                  rw [if_neg h6]
                  split at hv
                  · next h7 => rw [if_pos h7]
                  · next h7 =>
                    rw [if_neg h7]
                    split at hv
                    · next h8 =>
                      rw [if_pos h8]
                      split at hv
                      · simp at hv
                      · next h8a =>
                        rw [if_neg h8a]
                        split at hv
                        · next h8b => rw [if_pos h8b]
                        · next h8b => rw [if_neg h8b]; exact hel nd hnd hv
                    · next h8 =>
                      rw [if_neg h8]
                      split at hv
                      · next h9 => rw [if_pos h9]; exact hel nd hnd hv
                      · next h9 =>
                        rw [if_neg h9]
                        refine hdt nd hnd ?_ hv
                        exact kind_documentType_of h4 h7 h8 h9


/--
`child` が `node` 自身のとき、reference child を次の兄弟にずらしても step 9 の検査は通る。

`node` より後ろに doctype が無いので、次の兄弟も doctype ではなく、
その後ろにも doctype は無い。
-/
theorem checkElementInsertion_shift {t : Tree} {parent node : NodeId} (hwf : WellFormed t)
    (hpar : parentOf t node = some parent)
    (h : checkElementInsertion t parent (some node) [] = .ok ()) :
    checkElementInsertion t parent (nextSibling t node) [] = .ok () := by
  obtain ⟨hall, hafter⟩ := checkElementInsertion_ok h
  have hnil : elementChildren t parent = [] := eq_nil_of_forall_mem_nil hall
  obtain ⟨_, hfol⟩ := hafter node rfl
  have hmem : node ∈ childrenOf t parent := (mem_childrenOf_iff hwf node parent).mp hpar
  obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem hmem
  have hL : childrenOf t parent = A ++ node :: B := ListUtil.splitAt?_eq_some hs
  have hns : nextSibling t node = B.head? := nextSibling_of_split hwf hpar hL
  have hB : (B.any fun x => kindOf t x == some NodeKind.documentType) = false := by
    unfold doctypeFollows at hfol
    rw [hs] at hfol
    exact hfol
  unfold checkElementInsertion
  rw [if_neg (by rw [hnil]; simp)]
  rw [hns]
  cases hBv : B with
  | nil => simp
  | cons y B' =>
    simp only [List.head?_cons]
    rw [hBv] at hB
    simp only [List.any_cons, Bool.or_eq_false_iff] at hB
    have hsy : ListUtil.splitAt? (childrenOf t parent) y = some (A ++ [node], B') := by
      rw [hL, hBv]
      have hrw : A ++ node :: y :: B' = (A ++ [node]) ++ y :: B' := by simp
      rw [hrw]
      refine ListUtil.splitAt?_append_cons_self ?_ B'
      have hnd : (childrenOf t parent).Nodup := childrenOf_nodup hwf parent
      rw [hL, hBv] at hnd
      have hrw' : A ++ node :: y :: B' = (A ++ [node]) ++ y :: B' := by simp
      rw [hrw'] at hnd
      exact (ListUtil.nodup_split hnd).1
    have hfol' : doctypeFollows t parent y = false := by
      unfold doctypeFollows
      rw [hsy]
      exact hB.2
    rw [if_neg (by rw [hfol']; simp)]
    rw [if_neg (by simp [hB.1])]

/--
`child` が `node` 自身で `node` が doctype のとき、
reference child を次の兄弟にずらしても step 10-11 の検査は通る。
-/
theorem checkDoctypeInsertion_shift {t : Tree} {parent node : NodeId} (hwf : WellFormed t)
    (hpar : parentOf t node = some parent)
    (hk : (kindOf t node == some NodeKind.element) = false)
    (h : checkDoctypeInsertion t parent (some node) [] = .ok ()) :
    checkDoctypeInsertion t parent (nextSibling t node) [] = .ok () := by
  obtain ⟨hall, hprec, _⟩ := checkDoctypeInsertion_ok h
  have hnil : doctypeChildren t parent = [] := eq_nil_of_forall_mem_nil hall
  have hp := hprec node rfl
  have hmem : node ∈ childrenOf t parent := (mem_childrenOf_iff hwf node parent).mp hpar
  obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem hmem
  have hL : childrenOf t parent = A ++ node :: B := ListUtil.splitAt?_eq_some hs
  have hns : nextSibling t node = B.head? := nextSibling_of_split hwf hpar hL
  have hA : (A.any fun x => kindOf t x == some NodeKind.element) = false := by
    unfold elementPrecedes at hp
    rw [hs] at hp
    exact hp
  have hnd : (childrenOf t parent).Nodup := childrenOf_nodup hwf parent
  unfold checkDoctypeInsertion
  rw [if_neg (by rw [hnil]; simp)]
  rw [hns]
  cases hBv : B with
  | nil =>
    -- `node` が最後の子なので、element の子は `A` の中にしかない
    refine if_neg ?_
    have hel : elementChildren t parent = [] := by
      unfold elementChildren
      rw [hL, hBv]
      simp only [List.filter_append]
      rw [filter_eq_nil_of_all_false A _ (fun x hx => ?_), filter_eq_nil_of_all_false _ _
        (fun x hx => ?_)]
      · rfl
      · rcases List.mem_singleton.mp hx with rfl
        exact hk
      · cases hxk : (kindOf t x == some NodeKind.element) with
        | false => rfl
        | true =>
          exfalso
          rw [Bool.eq_false_iff] at hA
          exact hA (List.any_eq_true.mpr ⟨x, hx, hxk⟩)
    rw [hel]
    simp
  | cons y B' =>
    simp only [List.head?_cons]
    have hsy : ListUtil.splitAt? (childrenOf t parent) y = some (A ++ [node], B') := by
      rw [hL, hBv]
      have hrw : A ++ node :: y :: B' = (A ++ [node]) ++ y :: B' := by simp
      rw [hrw]
      refine ListUtil.splitAt?_append_cons_self ?_ B'
      rw [hL, hBv] at hnd
      have hrw' : A ++ node :: y :: B' = (A ++ [node]) ++ y :: B' := by simp
      rw [hrw'] at hnd
      exact (ListUtil.nodup_split hnd).1
    refine if_neg ?_
    unfold elementPrecedes
    rw [hsy]
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, hA, hk]
    simp

/-- pre-insert の step 2-3 で reference child をずらしても validity は保たれる。 -/
theorem ensurePreInsertionValidity_shift {t : Tree} {node parent : NodeId}
    {child : Option NodeId} (hwf : WellFormed t)
    (hv : ensurePreInsertionValidity t node parent child [] = .ok ()) :
    ensurePreInsertionValidity t node parent
      (if child = some node then nextSibling t node else child) [] = .ok () := by
  by_cases hc : child = some node
  · rw [if_pos hc]
    subst hc
    have hpar : parentOf t node = some parent :=
      ensurePreInsertionValidity_childParent hv node rfl
    have hmem : node ∈ childrenOf t parent := (mem_childrenOf_iff hwf node parent).mp hpar
    obtain ⟨A, B, hs⟩ := ListUtil.exists_splitAt?_of_mem hmem
    have hL : childrenOf t parent = A ++ node :: B := ListUtil.splitAt?_eq_some hs
    have hns : nextSibling t node = B.head? := nextSibling_of_split hwf hpar hL
    refine ensurePreInsertionValidity_child_congr ?_ ?_ ?_ hv
    · -- step 3：次の兄弟も同じ parent の子である
      unfold childHasParent
      rw [hns]
      cases hBv : B with
      | nil => rfl
      | cons y B' =>
        simp only [List.head?_cons, decide_eq_true_eq]
        refine parentOf_of_mem_childrenOf hwf ?_
        rw [hL, hBv]
        exact List.mem_append_right _ (by simp)
    · exact fun _ _ => checkElementInsertion_shift hwf hpar
    · intro nd hnd hkd
      refine checkDoctypeInsertion_shift hwf hpar ?_
      simp [kindOf, hnd, hkd]
  · rw [if_neg hc]
    exact hv

/-! ## range の端点：adopt / replace / replace all -/

/-- `adopt` は range の両端を木の中に保つ。 -/
theorem adopt_preserves_endpoints {s s' : DOMState} {node doc : NodeId}
    (h : StructurallyValid s.tree) (hv : RangeEndpointsValid s)
    (ha : adopt s node doc = .ok s') : RangeEndpointsValid s' := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have hv₁ : RangeEndpointsValid s₁ := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact hv
    · obtain ⟨⟨q, hq⟩, _⟩ := remove_ok hr
      exact remove_preserves_endpoints h.wellFormed hq
        (childCountKind_of_parentOf h hq) hv hr
  rcases hfinal with rfl | rfl
  · exact hv₁
  · intro r hrmem
    obtain ⟨h1, h2⟩ := hv₁ r (by simpa using hrmem)
    exact ⟨ValidBoundaryPoint.setOwnerDocument h1, ValidBoundaryPoint.setOwnerDocument h2⟩

/-- `replace` は range の両端を木の中に保つ。 -/
theorem replace_preserves_endpoints {s s' : DOMState} {child node parent : NodeId}
    (h : StructurallyValid s.tree) (hv : RangeEndpointsValid s)
    (hr : replace s child node parent = .ok s') : RangeEndpointsValid s' := by
  unfold replace at hr
  split at hr
  · simp at hr
  · next hvv =>
    split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        have hs₁ : StructurallyValid s₁.tree :=
          structurallyValid_adopt h (isDocument_ownerDocument h.wellFormed hpd) ha
        have hv₁ : RangeEndpointsValid s₁ := adopt_preserves_endpoints h hv ha
        -- adopt の後、node は parent を持たない
        have hnp : parentOf s₁.tree node = none := by
          obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases ha
          have hnp₀ : parentOf s₀.tree node = none := by
            rcases hstep with ⟨hn, rfl⟩ | hrm
            · exact hn
            · exact remove_parentOf hrm
          rcases hfinal with rfl | rfl
          · exact hnp₀
          · rw [DOMState.withTree_tree, parentOf_setOwnerDocument]
            exact hnp₀
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have hstep : StructurallyValid s₂.tree ∧ RangeEndpointsValid s₂ ∧
              parentOf s₂.tree node = none ∧ ShapePreserving s₁.tree s₂.tree := by
            revert hrm
            split
            · intro hrm
              rw [← Except.ok.inj hrm]
              exact ⟨hs₁, hv₁, hnp, ShapePreserving.refl _⟩
            · intro hrm
              have hrm' : remove s₁ child true = .ok s₂ := by simpa using hrm
              obtain ⟨⟨q, hq⟩, hd⟩ := remove_ok hrm'
              have hne : node ≠ child := by
                intro he
                rw [he, hq] at hnp
                simp at hnp
              refine ⟨structurallyValid_remove hs₁ hrm',
                remove_preserves_endpoints hs₁.wellFormed hq
                  (childCountKind_of_parentOf hs₁ hq) hv₁ hrm', ?_,
                shapePreserving_remove hrm'⟩
              rw [parentOf_detach hd, if_neg hne]
              exact hnp
          obtain ⟨hs₂, hv₂, hnp₂, hkp₂⟩ := hstep
          split at hr
          · simp at hr
          · next s₃ hi =>
            have hpk : ∀ pd', s₂.tree.get? parent = some pd' →
                pd'.kind.canHaveChildren = true :=
              kindFact_of_kindPreserving ((shapePreserving_adopt ha).trans hkp₂)
                (P := fun k => k.canHaveChildren = true)
                (ensurePreInsertionValidity_parentCanHaveChildren hvv)
            have hv₃ : RangeEndpointsValid s₃ :=
              insert_preserves_endpoints hs₂.wellFormed
                (childCountKind_of_canHaveChildren hpk)
                (fun q hq => by rw [hnp₂] at hq; simp at hq) hv₂ hi
            rw [← Except.ok.inj hr]
            exact rangeEndpointsValid_congr (by simp) (by simp) hv₃

/-- `removeEach` は range の両端を木の中に保つ。 -/
theorem removeEach_preserves_endpoints :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      StructurallyValid s.tree → RangeEndpointsValid s → removeEach s ns b = .ok s' →
      RangeEndpointsValid s'
  | [], _, _, _, _, hv, hr => by rw [← Except.ok.inj hr]; exact hv
  | n :: ns, s, s', b, h, hv, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      obtain ⟨⟨q, hq⟩, _⟩ := remove_ok h₁
      exact removeEach_preserves_endpoints ns (structurallyValid_remove h h₁)
        (remove_preserves_endpoints h.wellFormed hq (childCountKind_of_parentOf h hq) hv h₁) hr

/-- `replace all` は range の両端を木の中に保つ。 -/
theorem replaceAll_preserves_endpoints {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : StructurallyValid s.tree)
    (hpk : ∀ n, node = some n → ∀ pd, s.tree.get? parent = some pd →
      pd.kind.canHaveChildren = true)
    (hv : RangeEndpointsValid s) (hr : replaceAll s node parent = .ok s') :
    RangeEndpointsValid s' := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    have hs₁ : StructurallyValid s₁.tree := structurallyValid_removeEach _ h hre
    have hv₁ : RangeEndpointsValid s₁ := removeEach_preserves_endpoints _ h hv hre
    have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_removeEach _ hre
    split at hr
    · simp at hr
    · next s₂ hins =>
      have hv₂ : RangeEndpointsValid s₂ := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact hv₁
        · next _ _ m =>
          intro hins
          refine insert_preserves_endpoints hs₁.wellFormed ?_ ?_ hv₁ (by simpa using hins)
          · exact childCountKind_of_canHaveChildren
              (kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
                (hpk m rfl))
          · exact fun q hq => childCountKind_of_parentOf hs₁ hq
      rw [← Except.ok.inj hr]
      exact rangeEndpointsValid_congr (by simp) (by simp) hv₂

/-! ## replaceData -/

theorem iterCtx_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : IterCtx s) (hr : replaceData s n offset count data = .ok s') :
    IterCtx s' := by
  obtain ⟨d, _, hd, _, _, _, htree, _, hit⟩ := replaceData_ok hr
  refine ⟨structurallyValid_replaceData h.structural hr,
    nodeDocumentsValid_replaceData h.nodeDocuments hr, ?_⟩
  intro it hmem
  rw [hit] at hmem
  obtain ⟨hex, hanc⟩ := h.iterators it hmem
  rw [htree]
  refine ⟨exists_get?_of_kindPreserving (shapePreserving_withData hd _) hex.choose_spec, ?_⟩
  rcases hanc with he | ha
  · exact Or.inl he
  · exact Or.inr (ancestor_congr (fun m => parentOf_withData hd _ m) ha)

theorem preservesRegs_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hr : replaceData s n offset count data = .ok s') :
    PreservesRegs s s' := by
  obtain ⟨d, _, hd, _, _, _, htree, _, _⟩ := replaceData_ok hr
  refine preservesRegs_congr ?_ ?_ ?_
  · rw [htree]; exact shapePreserving_withData hd _
  all_goals
    unfold replaceData at hr
    repeat' split at hr
    all_goals first
      | (rw [← Except.ok.inj hr]; simp)
      | simp at hr

/-! ## AdmissibleDOMState の保存 -/

namespace AdmissibleDOMState

theorem iterCtx {s : DOMState} (h : AdmissibleDOMState s) : IterCtx s :=
  ⟨h.structural, h.nodeDocuments, h.iterators⟩

end AdmissibleDOMState

/-- `remove` は admissibility を保つ。 -/
theorem admissible_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : AdmissibleDOMState s) (hr : remove s n b = .ok s') : AdmissibleDOMState s' := by
  obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
  have hit := iterCtx_remove h.iterCtx hr
  exact ⟨hit.structural, hit.nodeDocuments, documentTreesValid_remove h.wellFormed
      h.documentTrees hr,
    remove_preserves_endpoints h.wellFormed hp (h.childCountKind hp) h.rangeEndpoints hr,
    hit.iterators, preservesRegs_remove hr h.observerRegistrations,
    AttributesValid.map (shapePreserving_remove hr) h.attributes⟩

/-- `insert` は、validity 検査を通っていれば admissibility を保つ。 -/
theorem admissible_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (h : AdmissibleDOMState s)
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ())
    (hi : insert s node parent child b = .ok s') : AdmissibleDOMState s' := by
  have hpk := ensurePreInsertionValidity_parentCanHaveChildren hv
  have hit := iterCtx_insert h.iterCtx hpk
    (ensurePreInsertionValidity_nodeNotDocument hv)
    (ensurePreInsertionValidity_doctypeParentIsDocument hv) hi
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_insert h.wellFormed h.structural h.documentTrees hv hi,
    insert_preserves_endpoints h.wellFormed (childCountKind_of_canHaveChildren hpk)
      (fun q hq => h.childCountKind hq) h.rangeEndpoints hi,
    hit.iterators, preservesRegs_insert hi h.observerRegistrations,
    AttributesValid.map (shapePreserving_insert hi) h.attributes⟩

/--
`adopt` は admissibility を保つ。

`insert` の中からだけでなく `adoptNode` からも呼ばれるので、単独の形にしておく。
Document を adopt すると node document の不変条件が壊れるので、呼び出し側が除く。
-/
theorem admissible_adopt {s s' : DOMState} {node doc : NodeId}
    (h : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (hnk : ∀ nd, s.tree.get? node = some nd → nd.kind ≠ NodeKind.document)
    (ha : adopt s node doc = .ok s') : AdmissibleDOMState s' := by
  have hit := iterCtx_adopt h.iterCtx hdoc hnk ha
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_adopt h.wellFormed h.documentTrees ha,
    adopt_preserves_endpoints h.structural h.rangeEndpoints ha,
    hit.iterators, preservesRegs_adopt ha h.observerRegistrations,
    AttributesValid.map (shapePreserving_adopt ha) h.attributes⟩

/-- `replace` は admissibility を保つ。 -/
theorem admissible_replace {s s' : DOMState} {child node parent : NodeId}
    (h : AdmissibleDOMState s) (hr : replace s child node parent = .ok s') :
    AdmissibleDOMState s' := by
  have hit := iterCtx_replace h.iterCtx hr
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_replace h.wellFormed h.structural h.documentTrees hr,
    replace_preserves_endpoints h.structural h.rangeEndpoints hr,
    hit.iterators, preservesRegs_replace hr h.observerRegistrations,
    AttributesValid.map (shapePreserving_replace hr) h.attributes⟩

/--
`replace all` は node tree の制約を自分では検査しないので、
呼び出し側が確立する事実を仮定として受け取る。
-/
theorem admissible_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : AdmissibleDOMState s)
    (hpk : ∀ n, node = some n → ∀ pd, s.tree.get? parent = some pd →
      pd.kind.canHaveChildren = true)
    (hnk : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd → nd.kind ≠ NodeKind.document)
    (hdtf : ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      nd.kind = NodeKind.documentType →
      ∀ pd, s.tree.get? parent = some pd → pd.kind = NodeKind.document)
    (hok : kindOf s.tree parent = some NodeKind.document →
      ∀ n, node = some n → ∀ nd, s.tree.get? n = some nd →
      (∀ m ∈ (if nd.kind = NodeKind.documentFragment then nd.children else [n]),
        ∀ k, kindOf s.tree m = some k → k.isText = false) ∧
      (((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.element).length +
        ((if nd.kind = NodeKind.documentFragment then nd.children else [n]).filter fun m =>
          kindOf s.tree m == some NodeKind.documentType).length ≤ 1))
    (hr : replaceAll s node parent = .ok s') : AdmissibleDOMState s' := by
  have hit := iterCtx_replaceAll h.iterCtx hpk hnk hdtf hr
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_replaceAll h.wellFormed h.documentTrees hok hr,
    replaceAll_preserves_endpoints h.structural hpk h.rangeEndpoints hr,
    hit.iterators, preservesRegs_replaceAll hr h.observerRegistrations,
    AttributesValid.map (shapePreserving_replaceAll hr) h.attributes⟩

/--
`move` は step 1-6 で新しい parent の kind を検査しないので、
`moveBefore` が IDL から与える条件を仮定として受け取る。
-/
theorem admissible_move {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : AdmissibleDOMState s)
    (hpk : ∀ pd, s.tree.get? newParent = some pd → pd.kind.canHaveChildren = true)
    (hm : move s node newParent child = .ok s') : AdmissibleDOMState s' := by
  have hit := iterCtx_move h.iterCtx hpk hm
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_move h.wellFormed h.documentTrees hm,
    move_preserves_endpoints h.wellFormed (childCountKind_of_canHaveChildren hpk)
      (fun q hq => h.childCountKind hq) h.rangeEndpoints hm,
    hit.iterators, preservesRegs_move hm h.observerRegistrations,
    AttributesValid.map (shapePreserving_move hm) h.attributes⟩

/-- `moveBefore` は receiver の kind を検査してから `move` を呼ぶ。 -/
theorem admissible_moveBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : AdmissibleDOMState s)
    (hm : moveBefore s parent node child = .ok s') : AdmissibleDOMState s' := by
  obtain ⟨pd, ref, hpd, hk, hmove⟩ := moveBefore_ok hm
  refine admissible_move h ?_ hmove
  intro pd' hpd'
  obtain rfl : pd' = pd := by rw [hpd] at hpd'; exact (Option.some.inj hpd').symm
  exact hk

/-- `replace data` は admissibility を保つ。 -/
theorem admissible_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (h : AdmissibleDOMState s)
    (hr : replaceData s n offset count data = .ok s') : AdmissibleDOMState s' := by
  have hit := iterCtx_replaceData h.iterCtx hr
  exact ⟨hit.structural, hit.nodeDocuments,
    documentTreesValid_replaceData h.documentTrees hr,
    replaceData_preserves_endpoints h.rangeEndpoints hr,
    hit.iterators, preservesRegs_replaceData hr h.observerRegistrations,
    AttributesValid.map (shapePreserving_replaceData hr) h.attributes⟩

/-! ## §4.9 の attribute -/

/--
attribute の algorithm は admissibility を保つ。

木は attribute list しか変わらず、live object と registration はそのまま残るので、
七成分すべてが `AttrOpResult` から従う。
-/
theorem admissible_of_attrOp {s s' : DOMState} (h : AdmissibleDOMState s)
    (hr : AttrOpResult s s') : AdmissibleDOMState s' := by
  refine ⟨structurallyValid_of_attributesOnly hr.tree h.structural,
    nodeDocumentsValid_of_attributesOnly hr.tree h.nodeDocuments,
    documentTreesValid_of_attributesOnly hr.tree h.documentTrees, ?_, ?_, ?_,
    hr.attributes h.attributes⟩
  · intro r hrg
    rw [hr.ranges] at hrg
    obtain ⟨h1, h2⟩ := h.rangeEndpoints r hrg
    exact ⟨validBoundaryPoint_of_attributesOnly hr.tree h1,
      validBoundaryPoint_of_attributesOnly hr.tree h2⟩
  · intro it hit
    rw [hr.iterators] at hit
    exact validIterator_of_attributesOnly hr.tree (h.iterators it hit)
  · intro r hrg
    rw [hr.registrations] at hrg
    obtain ⟨g1, g2⟩ := h.observerRegistrations r hrg
    refine ⟨by rw [hr.observersLength]; exact g1, ?_⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp g2
    cases hd' : s'.tree.get? r.node with
    | none => exfalso; rw [hr.tree.get?_eq_none hd'] at hd; simp at hd
    | some _ => rfl

theorem admissible_setAttribute {s s' : DOMState} {element : NodeId} {qn value : String}
    (h : AdmissibleDOMState s) (hr : setAttribute s element qn value = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setAttribute hr)

theorem admissible_setAttributeNS {s s' : DOMState} {element : NodeId} {ns : Option String}
    {qn value : String} (h : AdmissibleDOMState s)
    (hr : setAttributeNS s element ns qn value = .ok s') : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setAttributeNS hr)

theorem admissible_removeAttribute {s s' : DOMState} {element : NodeId} {qn : String}
    (h : AdmissibleDOMState s) (hr : removeAttribute s element qn = .ok s') :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_removeAttribute hr)

theorem admissible_removeAttributeNS {s s' : DOMState} {element : NodeId} {ns : Option String}
    {localName : String} (h : AdmissibleDOMState s)
    (hr : removeAttributeNS s element ns localName = .ok s') : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_removeAttributeNS hr)

theorem admissible_toggleAttribute {s s' : DOMState} {element : NodeId} {qn : String}
    {force : Option Bool} {b : Bool} (h : AdmissibleDOMState s)
    (hr : toggleAttribute s element qn force = .ok (s', b)) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_toggleAttribute hr)

/-! ## public API -/

/-- `pre-insert` は step 1 の検査を通してから `insert` する。 -/
theorem admissible_preInsert {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    (h : AdmissibleDOMState s) (hp : preInsert s node parent child = .ok s') :
    AdmissibleDOMState s' := by
  unfold preInsert at hp
  split at hp
  · simp at hp
  · next hv =>
    exact admissible_insert h (ensurePreInsertionValidity_shift h.wellFormed hv) hp

theorem admissible_append {s s' : DOMState} {node parent : NodeId}
    (h : AdmissibleDOMState s) (hp : append s node parent = .ok s') : AdmissibleDOMState s' :=
  admissible_preInsert h hp

theorem admissible_preRemove {s s' : DOMState} {child parent : NodeId}
    (h : AdmissibleDOMState s) (hp : preRemove s child parent = .ok s') :
    AdmissibleDOMState s' := by
  unfold preRemove at hp
  split at hp
  · simp at hp
  · exact admissible_remove h hp

theorem admissible_appendChild {s s' : DOMState} {parent node : NodeId}
    (h : AdmissibleDOMState s) (hp : appendChild s parent node = .ok s') :
    AdmissibleDOMState s' :=
  admissible_append h hp

theorem admissible_insertBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : AdmissibleDOMState s)
    (hp : insertBefore s parent node child = .ok s') : AdmissibleDOMState s' :=
  admissible_preInsert h hp

theorem admissible_replaceChild {s s' : DOMState} {parent node child : NodeId}
    (h : AdmissibleDOMState s) (hp : replaceChild s parent node child = .ok s') :
    AdmissibleDOMState s' :=
  admissible_replace h hp

theorem admissible_removeChild {s s' : DOMState} {parent child : NodeId}
    (h : AdmissibleDOMState s) (hp : removeChild s parent child = .ok s') :
    AdmissibleDOMState s' :=
  admissible_preRemove h hp

theorem admissible_before {s s' : DOMState} {this node : NodeId}
    (h : AdmissibleDOMState s) (hp : before s this node = .ok s') : AdmissibleDOMState s' := by
  unfold before at hp
  split at hp
  · rw [← Except.ok.inj hp]; exact h
  · exact admissible_preInsert h hp

theorem admissible_after {s s' : DOMState} {this node : NodeId}
    (h : AdmissibleDOMState s) (hp : after s this node = .ok s') : AdmissibleDOMState s' := by
  unfold after at hp
  split at hp
  · rw [← Except.ok.inj hp]; exact h
  · exact admissible_preInsert h hp

theorem admissible_replaceWith {s s' : DOMState} {this node : NodeId}
    (h : AdmissibleDOMState s) (hp : replaceWith s this node = .ok s') :
    AdmissibleDOMState s' := by
  unfold replaceWith at hp
  split at hp
  · rw [← Except.ok.inj hp]; exact h
  · next parent hpar =>
    rw [if_pos hpar] at hp
    exact admissible_replace h hp

theorem admissible_nodeRemove {s s' : DOMState} {this : NodeId}
    (h : AdmissibleDOMState s) (hp : nodeRemove s this = .ok s') : AdmissibleDOMState s' := by
  unfold nodeRemove at hp
  split at hp
  · rw [← Except.ok.inj hp]; exact h
  · exact admissible_remove h hp

/--
`replaceChildren` は step 2 の検査（既存の children を除外する）を通してから
replace all を行う。除外した children は直後に外れるので、
`replace all` に渡す条件は「入れる node の側」だけで足りる。
-/
theorem admissible_replaceChildren {s s' : DOMState} {parent : NodeId} {node : Option NodeId}
    (h : AdmissibleDOMState s) (hp : replaceChildren s parent node = .ok s') :
    AdmissibleDOMState s' := by
  unfold replaceChildren at hp
  split at hp
  · -- node が null。children を外すだけ。
    exact admissible_replaceAll h (fun n hn => absurd hn (by simp))
      (fun n hn => absurd hn (by simp)) (fun n hn => absurd hn (by simp))
      (fun _ n hn => absurd hn (by simp)) hp
  · next n =>
    split at hp
    · simp at hp
    · next hv =>
      refine admissible_replaceAll h ?_ ?_ ?_ ?_ hp
      · intro m hm
        rcases Option.some.inj hm with rfl
        exact ensurePreInsertionValidity_parentCanHaveChildren hv
      · intro m hm
        rcases Option.some.inj hm with rfl
        exact ensurePreInsertionValidity_nodeNotDocument hv
      · intro m hm
        rcases Option.some.inj hm with rfl
        exact ensurePreInsertionValidity_doctypeParentIsDocument hv
      · intro hdocparent m hm nd hnd
        rcases Option.some.inj hm with rfl
        obtain ⟨pd, hpd, hpk⟩ : ∃ pd, s.tree.get? parent = some pd ∧
            pd.kind = NodeKind.document := by
          cases hq : s.tree.get? parent with
          | none => rw [kindOf, hq] at hdocparent; simp at hdocparent
          | some q =>
            refine ⟨q, rfl, ?_⟩
            rw [kindOf, hq] at hdocparent
            simpa using hdocparent
        exact insertNodes_textAndCount h.structural hpd hnd hpk hv

/-! ## CharacterData -/

theorem admissible_appendData {s s' : DOMState} {n : NodeId} {data : String}
    (h : AdmissibleDOMState s) (hp : appendData s n data = .ok s') :
    AdmissibleDOMState s' := by
  unfold appendData at hp
  split at hp
  · simp at hp
  · exact admissible_replaceData h hp

theorem admissible_insertData {s s' : DOMState} {n : NodeId} {offset : Nat} {data : String}
    (h : AdmissibleDOMState s) (hp : insertData s n offset data = .ok s') :
    AdmissibleDOMState s' :=
  admissible_replaceData h hp

theorem admissible_deleteData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    (h : AdmissibleDOMState s) (hp : deleteData s n offset count = .ok s') :
    AdmissibleDOMState s' :=
  admissible_replaceData h hp

theorem admissible_setData {s s' : DOMState} {n : NodeId} {data : String}
    (h : AdmissibleDOMState s) (hp : setData s n data = .ok s') :
    AdmissibleDOMState s' := by
  unfold setData at hp
  split at hp
  · simp at hp
  · exact admissible_replaceData h hp

/-! ## live object をまとめた形 -/

/--
`remove` は live Range と NodeIterator の妥当性を保つ。

`notes/research-foundation-roadmap.md` §16 の `remove_preserves_live_objects`。
pre-remove steps が両方を仕様どおり動かすことの帰結である。
-/
theorem remove_preserves_live_objects {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : AdmissibleDOMState s) (hr : remove s n b = .ok s') :
    RangeEndpointsValid s' ∧ IteratorsValid s' :=
  ⟨(admissible_remove h hr).rangeEndpoints, (admissible_remove h hr).iterators⟩

/--
`replace data` は live Range と NodeIterator の妥当性を保つ。

§16 の `replaceData_preserves_live_object_validity`。
-/
theorem replaceData_preserves_live_object_validity {s s' : DOMState} {n : NodeId}
    {offset count : Nat} {data : String} (h : AdmissibleDOMState s)
    (hr : replaceData s n offset count data = .ok s') :
    RangeEndpointsValid s' ∧ IteratorsValid s' :=
  ⟨(admissible_replaceData h hr).rangeEndpoints, (admissible_replaceData h hr).iterators⟩

/--
`move` を木・Range・Iterator に射影した結果は、`remove` してから `insertAt` したものと一致する。

§16 の `move_matches_remove_insert_observation`。
`move` は node document を付け替えないので、`insert`（adopt を含む）ではなく
primitive の `insertAt` との一致になる。
Range は挿入側の調整を、Iterator は `remove` の pre-remove steps だけを受ける。
-/
theorem move_matches_remove_insert_observation {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hm : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      insertAt s₁.tree newParent node child = .ok s'.tree ∧
      s'.ranges = (liveRangeInsertAdjust s₁ newParent child 1).ranges ∧
      s'.iterators = s₁.iterators := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  obtain ⟨s₂, hr₂, hrng⟩ := move_ranges hm
  obtain ⟨s₃, hr₃, hit⟩ := move_iterators hm
  have h₂ : s₂ = s₁ := by rw [hr] at hr₂; exact (Except.ok.inj hr₂).symm
  have h₃ : s₃ = s₁ := by rw [hr] at hr₃; exact (Except.ok.inj hr₃).symm
  rw [h₂] at hrng
  rw [h₃] at hit
  exact ⟨s₁, hr, hi, hrng, hit⟩

/-! ## MutationObserver の配送 -/

/--
`observe` は木も live object も変えず、registration を一つ足すか差し替えるだけである。

足す registration は「木の中にある target」と「範囲内の observer index」を指す。
どちらも `observe` が step 前に検査している。
-/
theorem admissible_observe {s s' : DOMState} {mo : Nat} {target : NodeId}
    {opts : MutationObserverInit} (h : AdmissibleDOMState s)
    (ho : MutationObserver.observe s mo target opts = .ok s') : AdmissibleDOMState s' := by
  have htree : s'.tree = s.tree := MutationObserver.observe_tree ho
  have hranges : s'.ranges = s.ranges := MutationObserver.observe_ranges ho
  have hiters : s'.iterators = s.iterators := MutationObserver.observe_iterators ho
  refine ⟨by rw [htree]; exact h.structural, by rw [htree]; exact h.nodeDocuments,
    by rw [htree]; exact h.documentTrees, ?_, ?_, ?_, by rw [htree]; exact h.attributes⟩
  · intro r hr
    rw [htree]
    exact h.rangeEndpoints r (by rw [← hranges]; exact hr)
  · intro it hit
    rw [htree]
    exact h.iterators it (by rw [← hiters]; exact hit)
  · -- registration の妥当性。足す一つだけが新しい。
    unfold MutationObserver.observe at ho
    split at ho
    · simp at ho
    · next hnone =>
      split at ho
      · simp at ho
      · next hmo =>
        split at ho
        · -- step 3-6 の TypeError
          simp at ho
        · have htgt : (s.tree.get? target).isSome := by
            cases hq : s.tree.get? target with
            | none =>
              exfalso
              rw [hq] at hnone
              exact hnone rfl
            | some _ => rfl
          have hmo' : mo < s.observers.length := by omega
          split at ho
          · -- 既存の registration の options を差し替える
            rw [← Except.ok.inj ho]
            intro r hr
            simp only at hr
            obtain ⟨r₀, hr₀, hre⟩ := List.mem_filterMap.mp hr
            split at hre
            · simp at hre
            · split at hre
              · rw [← Option.some.inj hre]
                exact ⟨hmo', htgt⟩
              · rw [← Option.some.inj hre]
                exact h.observerRegistrations r₀ hr₀
          · -- 新しい registration を足す
            rw [← Except.ok.inj ho]
            intro r hr
            simp only [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · obtain ⟨g1, g2⟩ := h.observerRegistrations r hr
              exact ⟨by simpa using g1, g2⟩
            · exact ⟨by simpa using hmo', htgt⟩

/-- `disconnect` は registration を減らすだけである。 -/
theorem admissible_disconnect {s : DOMState} (h : AdmissibleDOMState s) (mo : Nat) :
    AdmissibleDOMState (MutationObserver.disconnect s mo) := by
  refine ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators, ?_,
    h.attributes⟩
  intro r hr
  unfold MutationObserver.disconnect at hr
  simp only at hr
  obtain ⟨g1, g2⟩ := h.observerRegistrations r (List.mem_filter.mp hr).1
  exact ⟨by simpa using g1, g2⟩

/-- `takeRecords` は record queue を空にするだけである。 -/
theorem admissible_takeRecords {s : DOMState} (h : AdmissibleDOMState s) (mo : Nat) :
    AdmissibleDOMState (MutationObserver.takeRecords s mo).1 := by
  unfold MutationObserver.takeRecords
  split
  · exact h
  · refine ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators, ?_,
    h.attributes⟩
    intro r hr
    obtain ⟨g1, g2⟩ := h.observerRegistrations r hr
    exact ⟨by simpa using g1, g2⟩

/-- transient registration を外しても妥当である。 -/
theorem admissible_removeTransients {s : DOMState} (h : AdmissibleDOMState s) (mo : Nat) :
    AdmissibleDOMState (removeTransients s mo) := by
  refine ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators, ?_,
    h.attributes⟩
  intro r hr
  exact h.observerRegistrations r (List.mem_filter.mp hr).1

theorem admissible_notifyEach :
    ∀ (ms : List Nat) {s : DOMState}, AdmissibleDOMState s →
      AdmissibleDOMState (notifyEach s ms).1
  | [], _, h => h
  | mo :: rest, s, h => by
    show AdmissibleDOMState (notifyEach (notifyOne s mo).1 rest).1
    refine admissible_notifyEach rest ?_
    show AdmissibleDOMState (removeTransients (MutationObserver.takeRecords s mo).1 mo)
    exact admissible_removeTransients (admissible_takeRecords h mo) mo

/-- microtask checkpoint は admissibility を保つ。 -/
theorem admissible_notifyMutationObservers {s : DOMState} (h : AdmissibleDOMState s) :
    AdmissibleDOMState (notifyMutationObservers s).1 := by
  unfold notifyMutationObservers
  refine admissible_notifyEach _ ?_
  exact ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators,
    fun r hr => h.observerRegistrations r hr, h.attributes⟩

end Dom
