import Dom.Spec.SplitText
import Dom.Properties.Clone
import Dom.Properties.InsertOk
import Dom.CharacterData.SplitText
import Dom.Validity.Admissible
import Dom.Validity.Variadic
import Dom.Spec.InsertChildren

/-!
# "split a Text node" は `SplitTextResult` を満たす

実行関数との違いは二つある。

* step 7.1 を pre-insert で書いている。新しい Text と、Element か DocumentFragment である parent では
  pre-insert の検査は必ず通り、reference child は新しい Text ではないので、insert と同じになる
  （`validity_freshText`）。
* step 7.2-7.5 は、移した先が妥当でなければ動かさない（`guardBP`）。admissible な状態では
  移した先は必ず妥当なので、検査は効かない（`splitAdjusted_splitTextBP`）。
-/

namespace Dom.Spec

open Dom


/-! ## 作ったばかりの node を入れる -/

/--
作ったばかりの node を、reference child の前に入れたときの効果と frame。

`append_fresh` の reference child を一般にしたもの。
-/
theorem insert_fresh {s s' : DOMState} {node parent : NodeId} {child : Option NodeId} {b : Bool}
    {nd : NodeData} (hwf : WellFormed s.tree)
    (hnd : s.tree.get? node = some nd) (hch : nd.children = []) (hp : nd.parent = none)
    (hk : nd.kind ≠ .documentFragment)
    (h : insert s node parent child b = .ok s') :
    (∀ m md, s.tree.get? m = some md → m ≠ node → m ≠ parent → s'.tree.get? m = some md) ∧
    (∃ nd', s'.tree.get? node = some nd' ∧ nd'.data = nd.data ∧ nd'.kind = nd.kind) ∧
    (∀ pd, s.tree.get? parent = some pd → ∃ pd', s'.tree.get? parent = some pd' ∧
      pd'.kind = pd.kind ∧ pd'.children = Dom.ListUtil.insertBefore pd.children child node) := by
  obtain ⟨pd, s₁, hpd, ha, hi, -⟩ := insert_single hnd (by simpa using hk) h
  have hpn : parentOf (liveRangeInsertAdjust s parent child 1).tree node = none := by
    simp [parentOf_eq, hnd, hp]
  obtain ⟨-, hs₁⟩ := adopt_of_no_parent hpn ha
  have hother : ∀ m, m ≠ node → s₁.tree.get? m = s.tree.get? m := by
    intro m hm
    rcases hs₁ with he | he
    · rw [he]; simp
    · rw [he]
      have : m ∉ preorder (liveRangeInsertAdjust s parent child 1).tree node := by
        rw [liveRangeInsertAdjust_tree]
        rw [mem_preorder_iff hwf hnd]
        rintro (rfl | hanc)
        · exact hm rfl
        · exact not_ancestor_of_children_nil hwf hnd hch m hanc
      rw [get?_setOwnerDocument_of_not_mem this]
      simp
  have hnode₁ : ∃ nd₁, s₁.tree.get? node = some nd₁ ∧ nd₁.data = nd.data ∧ nd₁.kind = nd.kind := by
    rcases hs₁ with he | he
    · exact ⟨nd, by rw [he]; simpa [liveRangeInsertAdjust_tree] using hnd, rfl, rfl⟩
    · refine ⟨nd.withOwnerDocument pd.ownerDocument, ?_, rfl, rfl⟩
      rw [he, get?_setOwnerDocument_of_mem ?_ (by simpa [liveRangeInsertAdjust_tree] using hnd)]
      rw [liveRangeInsertAdjust_tree, mem_preorder_iff hwf hnd]
      exact Or.inl rfl
  obtain ⟨nd₁, hnd₁, hda₁, hki₁⟩ := hnode₁
  obtain ⟨pd₁, nd₁', hpd₁, hnd₁', -, hanc, -, htree⟩ := insertAt_ok_cases hi
  rw [hnd₁] at hnd₁'
  cases hnd₁'
  have hnp : node ≠ parent := by
    intro he
    rw [he] at hanc
    rw [isInclusiveAncestorOf_self] at hanc
    simp at hanc
  refine ⟨?_, ?_, ?_⟩
  · intro m md hm h1 h2
    rw [htree, get?_insertAtIn_other h1 h2, hother m h1]
    exact hm
  · exact ⟨{ nd₁ with parent := some parent }, by rw [htree]; simp, hda₁, hki₁⟩
  · intro pd₀ hpd₀
    have hpe : pd₁ = pd₀ := by
      rw [hother parent (Ne.symm hnp)] at hpd₁
      rw [hpd₀] at hpd₁
      exact (Option.some.inj hpd₁).symm
    subst hpe
    exact ⟨{ pd₁ with children := Dom.ListUtil.insertBefore pd₁.children child node },
      by rw [htree, get?_insertAtIn_parent hnp], rfl, rfl⟩

/-! ## step 7.1 の検査は通る -/

/-- Text の parent は Element か DocumentFragment である（Document は Text を子に持たない）。 -/
theorem textParent_kind {s : DOMState} {node p : NodeId} {d : NodeData} (h : AdmissibleDOMState s)
    (hd : s.tree.get? node = some d) (hk : d.kind.isText = true) (hp : parentOf s.tree node = some p) :
    ∃ pd, s.tree.get? p = some pd ∧ (pd.kind = .element ∨ pd.kind = .documentFragment) := by
  have hwf := h.wellFormed
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
  have hmem : node ∈ childrenOf s.tree p := (mem_childrenOf_iff hwf node p).mp hp
  have hne : pd.children ≠ [] := by
    intro he; rw [childrenOf_eq hpd, he] at hmem; simp at hmem
  have hch := h.structural.childrenOnlyUnderContainers p pd hpd hne
  refine ⟨pd, hpd, ?_⟩
  cases hpk : pd.kind with
  | element => exact Or.inl rfl
  | documentFragment => exact Or.inr rfl
  | document =>
    have hok := h.documentTrees.documentChildren p pd hpd hpk
    have : node ∈ textChildren s.tree p := by
      unfold textChildren
      simp only [List.mem_filter]
      refine ⟨hmem, ?_⟩
      simp [kindOf, hd, hk]
    rw [hok.2.2.1] at this
    simp at this
  | _ => rw [hpk] at hch; simp [NodeKind.canHaveChildren] at hch

/-- 作ったばかりの Text を、Element か DocumentFragment に入れる検査は通る。 -/
theorem validity_freshText {t : Tree} {node parent : NodeId} {child : Option NodeId}
    {pd nd : NodeData} (hpd : t.get? parent = some pd)
    (hpk : pd.kind = .element ∨ pd.kind = .documentFragment) (hnd : t.get? node = some nd)
    (hk : nd.kind = .text) (hanc : isInclusiveAncestorOf t node parent = false)
    (hch : childHasParent t child parent = true) :
    ensurePreInsertionValidity t node parent child [] = .ok () := by
  unfold ensurePreInsertionValidity
  rcases hpk with hpk | hpk <;>
    simp [hpd, hnd, hk, hanc, hch, hpk, NodeKind.isCharacterData]

/-! ## step 7.2-7.5 の検査は効かない -/

/--
移した先は妥当である。node の length は `len`、新しい Text の length は `len - offset`、
parent は node の index + 2 個以上の子を持つ。
-/
theorem splitAdjusted_splitTextBP {t : Tree} {node newNode parent : NodeId} {offset idx len : Nat}
    {bp : BoundaryPoint} (hbp : ValidBoundaryPoint t bp)
    (hnode : ∀ nd, t.get? node = some nd → nd.length = len)
    (hnew : ∃ nn, t.get? newNode = some nn ∧ nn.length = len - offset)
    (hpar : ∃ pd, t.get? parent = some pd ∧ idx + 2 ≤ pd.length) :
    SplitAdjusted node newNode parent offset idx bp (splitTextBP t node newNode parent offset idx bp) := by
  obtain ⟨bd, hbd, hle⟩ := hbp
  unfold splitTextBP guardBP splitTextMoved
  by_cases h1 : bp.node = node ∧ offset < bp.offset
  · rw [if_pos h1]
    obtain ⟨nn, hnn, hnl⟩ := hnew
    have hl := hnode bd (h1.1 ▸ hbd)
    rw [if_pos ((checkValidBoundaryPoint_iff _ _).mpr ⟨nn, hnn, by simp; omega⟩)]
    exact Or.inl ⟨h1.1, h1.2, rfl⟩
  · rw [if_neg h1]
    by_cases h2 : bp.node = parent ∧ bp.offset = idx + 1
    · rw [if_pos h2]
      obtain ⟨pd, hpd, hpl⟩ := hpar
      rw [if_pos ((checkValidBoundaryPoint_iff _ _).mpr ⟨pd, by simp only []; rw [h2.1]; exact hpd,
        by simp only []; omega⟩)]
      refine Or.inr (Or.inl ⟨h2.1, h2.2, ?_⟩)
      cases bp; simp_all
    · rw [if_neg h2]
      split <;> exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)

/-! ## 全体 -/

/--
**"split a Text node" の結果は、成否によらず関係を満たす。**

node は木にある Text である（`splitText()` の受け手）。
-/
theorem splitText_result_sound {s : DOMState} {node : NodeId} {d : NodeData}
    (h : AdmissibleDOMState s) (hd : s.tree.get? node = some d) (hk : d.kind.isText = true)
    (offset : Nat) : SplitTextResult s node offset (splitText s node offset) := by
  have hwf := h.wellFormed
  have hcd : d.kind.isCharacterData = true := by
    cases hdk : d.kind <;> simp_all [NodeKind.isText, NodeKind.isCharacterData]
  refine ⟨d, hd, hk, ?_⟩
  unfold splitText
  rw [hd]
  simp only [hk, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hl : d.length < offset
  · rw [if_pos hl]; exact Or.inl ⟨hl, rfl⟩
  rw [if_neg hl]
  refine Or.inr ⟨by omega, ?_⟩
  have hsub := substringData_result_sound hd hcd offset (d.length - offset)
  cases hs : substringData s.tree node offset (d.length - offset) with
  | error e => rw [hs] at hsub; exact Or.inl ⟨e, hsub, rfl⟩
  | ok newData =>
  rw [hs] at hsub
  refine Or.inr ?_
  simp only []
  -- step 5
  have hdoc : IsDocumentIn s d.ownerDocument := h.wellFormed.ownerDocument_is_document node d hd
  have hct := createTextNode_of_isDocumentIn hdoc newData
  rw [hct]
  simp only []
  cases hw : withFresh s { kind := .text, ownerDocument := d.ownerDocument, data := newData } with
  | mk nn s₁ =>
  rw [hw] at hct
  have hcreate := createTextNode_creates hct
  refine ⟨newData, nn, s₁, hsub, hcreate, ?_⟩
  simp only []
  have hadd := hcreate.1
  have h₁ : AdmissibleDOMState s₁ := admissible_createsNode h hcreate
  have hwf₁ := h₁.wellFormed
  have hget : ∀ m md, s.tree.get? m = some md → s₁.tree.get? m = some md := by
    intro m md hm
    have hne : m ≠ nn := by intro he; rw [he, hadd.fresh] at hm; cases hm
    rw [hadd.others m hne]; exact hm
  have hnn : s₁.tree.get? nn = some { kind := .text, ownerDocument := d.ownerDocument, data := newData } :=
    hadd.created
  have hnode_ne : node ≠ nn := by intro he; rw [he, hadd.fresh] at hd; cases hd
  have hpar_eq : parentOf s₁.tree node = parentOf s.tree node := by
    rw [parentOf_of_get? (hget node d hd), parentOf_of_get? hd]
  -- step 8
  have step8 : ∀ s₃ : DOMState, WellFormed s₃.tree →
      ((∃ e, ReplaceDataResult s₃ node offset (d.length - offset) "" (.error e) ∧
          (match replaceData s₃ node offset (d.length - offset) "" with
            | .error e => Except.error e
            | .ok s₄ => Except.ok (nn, s₄)) = .error e) ∨
        (∃ s', ReplaceDataResult s₃ node offset (d.length - offset) "" (.ok s') ∧
          (match replaceData s₃ node offset (d.length - offset) "" with
            | .error e => Except.error e
            | .ok s₄ => Except.ok (nn, s₄)) = .ok (nn, s'))) := by
    intro s₃ hwf₃
    have := replaceData_result_sound hwf₃ node offset (d.length - offset) ""
    cases hr : replaceData s₃ node offset (d.length - offset) "" with
    | error e => rw [hr] at this; exact Or.inl ⟨e, this, rfl⟩
    | ok s' => rw [hr] at this; exact Or.inr ⟨s', this, rfl⟩
  rw [hpar_eq]
  cases hp : parentOf s.tree node with
  | none => exact ⟨s₁, Or.inl ⟨rfl, rfl⟩, step8 s₁ hwf₁⟩
  | some p =>
  simp only []
  have hp₁ : parentOf s₁.tree node = some p := hpar_eq.trans hp
  obtain ⟨pd, hpd, hpk⟩ := textParent_kind h hd hk hp
  have hpd₁ := hget p pd hpd
  have hpn : p ≠ nn := by intro he; rw [he, hadd.fresh] at hpd; cases hpd
  -- step 7.1：pre-insert の検査は通り、reference child は新しい Text ではない
  have hanc : isInclusiveAncestorOf s₁.tree nn p = false := by
    cases hb : isInclusiveAncestorOf s₁.tree nn p with
    | false => rfl
    | true =>
      exfalso
      rcases (isInclusiveAncestorOf_iff hwf₁ nn p).mp hb with he | ha
      · exact hpn he.symm
      · exact not_ancestor_of_children_nil hwf₁ hnn rfl p ha
  have hnsp : ∀ c, nextSibling s₁.tree node = some c → parentOf s₁.tree c = some p :=
    fun c hc => parentOf_nextSibling hwf₁ hp₁ hc
  have hnnp : parentOf s₁.tree nn = none := by rw [parentOf_of_get? hnn]
  have hcn : ∀ c, nextSibling s₁.tree node = some c → c ≠ nn := by
    intro c hc he
    have := hnsp c hc
    rw [he, hnnp] at this
    cases this
  have hch : childHasParent s₁.tree (nextSibling s₁.tree node) p = true := by
    cases hns : nextSibling s₁.tree node with
    | none => rfl
    | some c => simp [childHasParent, hnsp c hns]
  have hv := validity_freshText hpd₁ hpk hnn rfl hanc hch
  have href : preInsertReferenceChild s₁.tree nn (nextSibling s₁.tree node) =
      nextSibling s₁.tree node := by
    rw [preInsertReferenceChild_eq, if_neg]
    intro he
    exact hcn nn he rfl
  rw [preInsert_of_validity hv, href]
  obtain ⟨s₂, hi⟩ := insert_isOk_of_validity (b := false) hwf₁ hv hcn
  rw [hi]
  simp only []
  have hins := insert_sound hwf₁ hi
  have h₂ : AdmissibleDOMState s₂ := admissible_insert h₁ hv hi
  obtain ⟨hother, ⟨nn', hnn', hnnd, hnnk⟩, hpch⟩ :=
    insert_fresh hwf₁ hnn rfl rfl (by simp) hi
  -- parent の children は「…, node, 新しい Text, …」になる
  obtain ⟨j, hj⟩ := index_isSome hwf₁ hp₁
  obtain ⟨u, v, huv, hul, hnu⟩ := (index_eq_some_iff_split hp₁).mp hj
  have hns : nextSibling s₁.tree node = v.head? := nextSibling_of_split hwf₁ hp₁ huv
  obtain ⟨pd₂, hpd₂, hpk₂, hpc₂⟩ := hpch pd hpd₁
  have hnodup := childrenOf_nodup hwf₁ p
  rw [huv] at hnodup
  have hc₂ : pd₂.children = u ++ node :: nn :: v := by
    rw [hpc₂, ← childrenOf_eq hpd₁, huv, hns]
    cases v with
    | nil => simp [ListUtil.insertBefore_none]
    | cons c v' =>
      simp only [List.head?_cons, ListUtil.insertBefore_some]
      have hcu : c ∉ u ++ [node] := by
        rw [show u ++ node :: c :: v' = (u ++ [node]) ++ c :: v' by simp] at hnodup
        intro hm
        exact (List.nodup_append.mp hnodup).2.2 c hm c (by simp) rfl
      rw [show u ++ node :: c :: v' = (u ++ [node]) ++ c :: v' by simp,
        insertBeforeFirst_split (u ++ [node]) v' hcu]
      simp
  have hnp : node ≠ p := by
    intro he
    rw [← he, hd] at hpd
    cases hpd
    rcases hpk with hpk | hpk <;> simp [hpk, NodeKind.isText] at hk
  have hd₂ : s₂.tree.get? node = some d := hother node d (hget node d hd) hnode_ne hnp
  have hpar₂ : parentOf s₂.tree node = some p := by
    rw [parentOf_of_get? hd₂, ← parentOf_of_get? hd, hp]
  have hidx : index s₂.tree node = some j :=
    (index_eq_some_iff_split hpar₂).mpr ⟨u, nn :: v, by rw [childrenOf_eq hpd₂, hc₂], hul, hnu⟩
  -- 新しい Text の length は length − offset
  have hlen : Utf16.length newData = d.length - offset := by
    obtain ⟨d0, hd0, -, hc⟩ := hsub
    rw [hd] at hd0
    cases hd0
    rcases hc with ⟨hlt, -⟩ | ⟨-, c, hcl, hc2⟩
    · exact absurd hlt hl
    · rcases hc2 with ⟨pre, mid, post, -, -, hmid, heq⟩ | ⟨-, hbad⟩
      · cases heq
        unfold Utf16.length
        rw [String.toList_ofList, hmid]
        rcases hcl with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> omega
      · cases hbad
  have hnnlen : nn'.length = d.length - offset := by
    have : nn'.length = Utf16.length nn'.data := by
      simp [NodeData.length, hnnk, NodeKind.isCharacterData]
    rw [this, hnnd]
    exact hlen
  have hpdlen : j + 2 ≤ pd₂.length := by
    have : pd₂.length = pd₂.children.length := by
      rcases hpk with hpk | hpk <;> simp [NodeData.length, hpk₂, hpk, NodeKind.isCharacterData]
    rw [this, hc₂]
    simp
    omega
  refine ⟨splitTextAdjust s₂ node nn p offset, Or.inr ⟨p, s₂, j, rfl, hins, hidx, ?_⟩,
    step8 _ h₂.wellFormed⟩
  refine ⟨_, rfl, by simp, ?_⟩
  intro i r r' hr hr'
  simp only [hidx, Option.getD_some, List.getElem?_map, hr, Option.map_some, Option.some.injEq] at hr'
  subst hr'
  have hv := h₂.rangeEndpoints r (List.mem_of_getElem? hr)
  have hnode : ∀ nd, s₂.tree.get? node = some nd → nd.length = d.length := by
    intro nd hnd'
    rw [hd₂] at hnd'
    cases hnd'
    rfl
  exact ⟨splitAdjusted_splitTextBP hv.1 hnode ⟨nn', hnn', hnnlen⟩ ⟨pd₂, hpd₂, hpdlen⟩,
    splitAdjusted_splitTextBP hv.2 hnode ⟨nn', hnn', hnnlen⟩ ⟨pd₂, hpd₂, hpdlen⟩⟩

/--
**split が成功したあとの形。** 新しい Text は node と同じ parent の子で、node ではない。
木にあった node は残り、live range の数は変わらない。
-/
theorem splitText_ok_facts {s s₀ : DOMState} {node newText p : NodeId} {d : NodeData} {offset : Nat}
    (h : AdmissibleDOMState s) (hd : s.tree.get? node = some d) (hk : d.kind.isText = true)
    (hp : parentOf s.tree node = some p) (hr : splitText s node offset = .ok (newText, s₀)) :
    parentOf s₀.tree newText = some p ∧ newText ≠ node ∧
      (∀ m, (s.tree.get? m).isSome → (s₀.tree.get? m).isSome) ∧
      s₀.ranges.length = s.ranges.length := by
  have hwf := h.wellFormed
  unfold splitText at hr
  rw [hd] at hr
  simp only [hk, Bool.not_true, Bool.false_eq_true, if_false] at hr
  by_cases hl : d.length < offset
  · rw [if_pos hl] at hr; cases hr
  rw [if_neg hl] at hr
  cases hs : substringData s.tree node offset (d.length - offset) with
  | error e => rw [hs] at hr; cases hr
  | ok newData =>
  rw [hs] at hr
  simp only [] at hr
  have hdoc : IsDocumentIn s d.ownerDocument := h.wellFormed.ownerDocument_is_document node d hd
  have hct := createTextNode_of_isDocumentIn hdoc newData
  rw [hct] at hr
  simp only [] at hr
  cases hw : withFresh s { kind := .text, ownerDocument := d.ownerDocument, data := newData } with
  | mk nn s₁ =>
  rw [hw] at hct hr
  simp only [] at hr
  have hcreate := createTextNode_creates hct
  have hadd := hcreate.1
  have h₁ : AdmissibleDOMState s₁ := admissible_createsNode h hcreate
  have hwf₁ := h₁.wellFormed
  have hget : ∀ m md, s.tree.get? m = some md → s₁.tree.get? m = some md := by
    intro m md hm
    have hne : m ≠ nn := by intro he; rw [he, hadd.fresh] at hm; cases hm
    rw [hadd.others m hne]; exact hm
  have hnn : s₁.tree.get? nn = some { kind := .text, ownerDocument := d.ownerDocument, data := newData } :=
    hadd.created
  have hnode_ne : node ≠ nn := by intro he; rw [he, hadd.fresh] at hd; cases hd
  have hp₁ : parentOf s₁.tree node = some p := by
    rw [parentOf_of_get? (hget node d hd), ← parentOf_of_get? hd, hp]
  rw [hp₁] at hr
  simp only [] at hr
  obtain ⟨pd, hpd, hpk⟩ := textParent_kind h hd hk hp
  have hpd₁ := hget p pd hpd
  have hpn : p ≠ nn := by intro he; rw [he, hadd.fresh] at hpd; cases hpd
  have hanc : isInclusiveAncestorOf s₁.tree nn p = false := by
    cases hb : isInclusiveAncestorOf s₁.tree nn p with
    | false => rfl
    | true =>
      exfalso
      rcases (isInclusiveAncestorOf_iff hwf₁ nn p).mp hb with he | ha
      · exact hpn he.symm
      · exact not_ancestor_of_children_nil hwf₁ hnn rfl p ha
  have hnsp : ∀ c, nextSibling s₁.tree node = some c → parentOf s₁.tree c = some p :=
    fun c hc => parentOf_nextSibling hwf₁ hp₁ hc
  have hnnp : parentOf s₁.tree nn = none := by rw [parentOf_of_get? hnn]
  have hcn : ∀ c, nextSibling s₁.tree node = some c → c ≠ nn := by
    intro c hc he
    have := hnsp c hc
    rw [he, hnnp] at this
    cases this
  have hch : childHasParent s₁.tree (nextSibling s₁.tree node) p = true := by
    cases hns : nextSibling s₁.tree node with
    | none => rfl
    | some c => simp [childHasParent, hnsp c hns]
  have hv := validity_freshText hpd₁ hpk hnn rfl hanc hch
  have href : preInsertReferenceChild s₁.tree nn (nextSibling s₁.tree node) =
      nextSibling s₁.tree node := by
    rw [preInsertReferenceChild_eq, if_neg]
    intro he
    exact hcn nn he rfl
  rw [preInsert_of_validity hv, href] at hr
  obtain ⟨s₂, hi⟩ := insert_isOk_of_validity (b := false) hwf₁ hv hcn
  rw [hi] at hr
  simp only [] at hr
  have h₂ : AdmissibleDOMState s₂ := admissible_insert h₁ hv hi
  obtain ⟨hother, ⟨nn', hnn', -, -⟩, hpch⟩ := insert_fresh hwf₁ hnn rfl rfl (by simp) hi
  obtain ⟨pd₂, hpd₂, -, hpc₂⟩ := hpch pd hpd₁
  have hmem : nn ∈ childrenOf s₂.tree p := by
    rw [childrenOf_eq hpd₂, hpc₂]
    exact (ListUtil.mem_insertBefore _ _ _ _).mpr (Or.inl rfl)
  have hpar₂ : parentOf s₂.tree nn = some p := (mem_childrenOf_iff h₂.wellFormed nn p).mpr hmem
  -- step 8
  cases hrep : replaceData (splitTextAdjust s₂ node nn p offset) node offset (d.length - offset) "" with
  | error e => rw [hrep] at hr; cases hr
  | ok s₄ =>
  rw [hrep] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨h1, h2⟩ := hr
  subst h1
  subst h2
  obtain ⟨d₃, c₃, new₃, s₀', -, -, -, -, -, -, hdr, hlen, -⟩ :=
    replaceData_sound (show WellFormed (splitTextAdjust s₂ node nn p offset).tree from h₂.wellFormed) hrep
  have hkeep : ∀ m, (s₂.tree.get? m).isSome → (s₄.tree.get? m).isSome := by
    intro m hm
    by_cases hmn : m = node
    · subst hmn
      obtain ⟨dd, hdd⟩ := Option.isSome_iff_exists.mp hm
      rw [hdr.changed dd hdd]; rfl
    · rw [hdr.others m hmn]; exact hm
  refine ⟨?_, hnode_ne.symm, ?_, ?_⟩
  · rw [parentOf_eq, hdr.others nn (Ne.symm hnode_ne), ← parentOf_eq]
    exact hpar₂
  · intro m hm
    apply hkeep
    obtain ⟨md, hmd⟩ := Option.isSome_iff_exists.mp hm
    have hm₁ := hget m md hmd
    by_cases h1 : m = nn
    · rw [h1, hnn']; rfl
    · by_cases h2 : m = p
      · rw [h2, hpd₂]; rfl
      · rw [hother m md hm₁ h1 h2]; rfl
  · rw [hlen]
    show (splitTextAdjust s₂ node nn p offset).ranges.length = s.ranges.length
    simp only [splitTextAdjust, List.length_map]
    rw [insertSpec_ranges_length (insert_sound hwf₁ hi)]
    exact congrArg List.length hcreate.2.2.1

end Dom.Spec
