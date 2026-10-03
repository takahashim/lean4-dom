import Dom.Spec.RangeInsert
import Dom.Spec.RangeDeleteSound
import Dom.Spec.InsertChildren
import Dom.Properties.InsertContract

/-!
# `insertNode` は `InsertNodeResult` を満たす

実行関数は step 13 で、newOffset を「最後に入った node の次」（`siblingBP`）として
書いている。それが step 10-11 の newOffset（removal の後、pre-insert の前の木で、
reference node の index か parent の length に入る node の数を足したもの）に等しいことを、
`insert` の後の parent の children（`insertSpec_children`）から示す。
-/

namespace Dom.Spec

open Dom
open Dom.ListUtil (insertAllBefore)

variable {t : Tree}

/-! ## 語彙の対応 -/

theorem hierarchyError_iff {sn node : NodeId} {sd : NodeData} (hs : t.get? sn = some sd) :
    (sd.kind == .processingInstruction || sd.kind == .comment ||
        (sd.kind.isText && (parentOf t sn).isNone) || sn == node) = true ↔
      InsertNodeHierarchyError t sn node := by
  unfold InsertNodeHierarchyError KindIs IsText
  simp only [hs, Option.some.injEq, exists_eq_left', Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, Option.isNone_iff_eq_none, or_assoc]

/-- 実行側の `children[offset]?` は step 4 の関係を満たす。 -/
theorem childAtOffset_spec (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hd : t.get? n = some d) (offset : Nat) : ChildAtOffset t n offset (d.children[offset]?) := by
  have hch : childrenOf t n = d.children := childrenOf_eq hd
  cases h : d.children[offset]? with
  | none =>
    intro c hcp hidx
    have := index_lt_children_length hcp hidx
    rw [hch] at this
    rw [List.getElem?_eq_getElem this] at h
    cases h
  | some c =>
    obtain ⟨hlt, hc⟩ := List.getElem?_eq_some_iff.mp h
    have hmem : c ∈ childrenOf t n := by rw [hch, ← hc]; exact List.getElem_mem hlt
    have hcp := (mem_childrenOf_iff hwf c n).mpr hmem
    refine ⟨hcp, (index_eq_some_iff_split hcp).mpr ⟨(childrenOf t n).take offset,
      (childrenOf t n).drop (offset + 1), ?_, by simp [hch]; omega, ?_⟩⟩
    · rw [hch, ← hc]; simp
    · intro hm
      have hnd := childrenOf_nodup hwf n
      rw [show childrenOf t n = (childrenOf t n).take offset ++ c :: (childrenOf t n).drop (offset + 1)
        from by rw [hch, ← hc]; simp] at hnd
      exact (List.nodup_append.mp hnd).2.2 c hm c (by simp) rfl

/-- step 6 を通れば parent は Document / DocumentFragment / Element である。 -/
theorem parentIsContainer_of_validity {node parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (hv : PreInsertValidity t node parent child excl (.ok ())) :
    ParentIsContainer t parent ∧ InTree t node := by
  unfold PreInsertValidity Step at hv
  rcases hv with ⟨-, h⟩ | ⟨-, hv⟩
  · cases h
  rcases hv with ⟨-, h⟩ | ⟨hn, hv⟩
  · cases h
  rcases hv with ⟨-, h⟩ | ⟨hpc, -⟩
  · cases h
  exact ⟨Classical.not_not.mp hpc, Classical.not_not.mp hn⟩

theorem childCountKind_of_container {parent : NodeId} (h : ParentIsContainer t parent) :
    ChildCountKind t parent := by
  refine childCountKind_of_kind ?_
  intro d hd
  rcases h with ⟨d', hd', hk⟩ | ⟨d', hd', hk⟩ | ⟨d', hd', hk⟩ <;>
    (rw [hd] at hd'; cases hd'; simp [hk])

theorem childCountKind_of_shapePreserving {t' : Tree} (hsp : ShapePreserving t t') {n : NodeId}
    (h : ChildCountKind t n) : ChildCountKind t' n := by
  intro d' hd'
  obtain ⟨d, hd, hk, -⟩ := hsp.exists_get? hd'
  rw [← hk]
  exact h d hd

/-! ## step 12-13 -/

/-- 実行関数の step 12-13。 -/
private def insertTail (s₁ : DOMState) (i : Nat) (node parent : NodeId) (ref : Option NodeId) :
    Except DOMException DOMState :=
  let last :=
    match s₁.tree.get? node with
    | some nd => if nd.kind == NodeKind.documentFragment then nd.children.getLast? else some node
    | none => some node
  match preInsert s₁ node parent ref with
  | .error e => .error e
  | .ok s₂ =>
    match s₂.ranges[i]? with
    | none => .error .notFoundError
    | some r₂ =>
      if r₂.start == r₂.«end» then
        match last.bind (fun n => siblingBP s₂.tree n true) with
        | none => .ok s₂
        | some bp => .ok (withRange s₂ i { r₂ with «end» := bp })
      else .ok s₂

/-- step 10-11 の newOffset（実行側の値で書いたもの）。 -/
private def newOffsetOf (t : Tree) (parent : NodeId) (ref : Option NodeId) (node : NodeId) : Nat :=
  (match ref with
   | none => lengthOf t parent
   | some c => (index t c).getD 0) +
  (match t.get? node with
   | some nd => if nd.kind = NodeKind.documentFragment then lengthOf t node else 1
   | none => 1)

theorem newOffsetOf_spec (hwf : WellFormed t) {parent node : NodeId} {ref : Option NodeId}
    {nd : NodeData} (hnd : t.get? node = some nd)
    (href : ∀ c, ref = some c → parentOf t c = some parent) :
    NewOffset t parent ref node (newOffsetOf t parent ref node) := by
  have hcount : ∀ b : Nat,
      (KindIs t node .documentFragment ∧ b + (match t.get? node with
        | some nd => if nd.kind = NodeKind.documentFragment then lengthOf t node else 1
        | none => 1) = b + lengthOf t node) ∨
      (¬ KindIs t node .documentFragment ∧ b + (match t.get? node with
        | some nd => if nd.kind = NodeKind.documentFragment then lengthOf t node else 1
        | none => 1) = b + 1) := by
    intro b
    simp only [hnd]
    by_cases hk : nd.kind = NodeKind.documentFragment
    · rw [if_pos hk]; exact Or.inl ⟨⟨nd, hnd, hk⟩, rfl⟩
    · rw [if_neg hk]
      refine Or.inr ⟨?_, rfl⟩
      rintro ⟨d, hd, hdk⟩
      rw [hnd] at hd
      cases hd
      exact hk hdk
  unfold newOffsetOf
  cases ref with
  | none => exact ⟨lengthOf t parent, Or.inl ⟨rfl, rfl⟩, hcount _⟩
  | some c =>
    obtain ⟨j, hj⟩ := index_isSome hwf (href c rfl)
    refine ⟨j, Or.inr ⟨c, rfl, hj⟩, ?_⟩
    simp only [hj, Option.getD_some]
    exact hcount j

/-- 入る node の列の最後は、実行側の `last` である。 -/
theorem last_eq_getLast? {node : NodeId} {nd : NodeData} {nodes : List NodeId}
    (hnd : t.get? node = some nd) (h : NodesToInsert t node nodes) :
    (if nd.kind == NodeKind.documentFragment then nd.children.getLast? else some node) =
      nodes.getLast? := by
  obtain ⟨d, hd, hc⟩ := h
  rw [hnd] at hd
  cases hd
  rcases hc with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · rw [if_pos (by simp [hk])]
  · rw [if_neg (by simp [hk])]; rfl

/-- 入る node の数は、node の length（fragment のとき）か 1 である。 -/
theorem nodes_length_eq {node : NodeId} {nd : NodeData} {nodes : List NodeId}
    (hnd : t.get? node = some nd) (h : NodesToInsert t node nodes) :
    nodes.length = (if nd.kind = NodeKind.documentFragment then lengthOf t node else 1) := by
  obtain ⟨d, hd, hc⟩ := h
  rw [hnd] at hd
  cases hd
  rcases hc with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · rw [if_pos hk, lengthOf_of_get? hnd]
    simp [NodeData.length, hk, NodeKind.isCharacterData]
  · rw [if_neg hk]; rfl

/-- 入れる node の列に、parent の子は入っていない。 -/
theorem not_mem_nodes_of_child {node parent c : NodeId} {nd : NodeData} {nodes : List NodeId}
    (hwf : WellFormed t) (hnd : t.get? node = some nd) (h : NodesToInsert t node nodes)
    (hne : node ≠ parent) (hcp : parentOf t c = some parent) (hcn : c ≠ node) : c ∉ nodes := by
  obtain ⟨d, hd, hc⟩ := h
  rw [hnd] at hd
  cases hd
  intro hm
  rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨cd, hcd, hcp'⟩ := hwf.parent_child node nd hnd c hm
    simp only [parentOf_eq, hcd, Option.bind_some] at hcp
    rw [hcp'] at hcp
    exact hne (Option.some.inj hcp)
  · simp at hm
    exact hcn hm

/--
**step 12-13。**

node が parent を持たず、reference node が parent の子で node でなければ、
実行関数の「最後に入った node の次」は step 10-11 の newOffset に等しい。
DocumentFragment が空のとき（何も入らないとき）は、range の end が既にそこにあることを
`hempty` として受け取る。
-/
private theorem insertTail_spec {s₁ : DOMState} {i : Nat} {node parent : NodeId}
    {ref : Option NodeId} {nd : NodeData}
    (hwf₁ : WellFormed s₁.tree) (hnd : s₁.tree.get? node = some nd)
    (hnp : parentOf s₁.tree node = none) (hne : node ≠ parent)
    (hcck : ChildCountKind s₁.tree parent)
    (href : ∀ c, ref = some c → parentOf s₁.tree c = some parent) (hrn : ref ≠ some node)
    (hi : i < s₁.ranges.length)
    (hempty : NodesToInsert s₁.tree node [] → ∀ r₁, s₁.ranges[i]? = some r₁ →
      r₁.start = r₁.«end» → r₁.«end» = ⟨parent, newOffsetOf s₁.tree parent ref node⟩) :
    AndThen (PreInsertResult s₁ node parent ref)
      (fun s₂ res₂ => ∃ r₂, s₂.ranges[i]? = some r₂ ∧
        ((r₂.start = r₂.«end» ∧
            res₂ = .ok { s₂ with
              ranges := s₂.ranges.set i { r₂ with «end» := ⟨parent, newOffsetOf s₁.tree parent ref node⟩ } }) ∨
          (r₂.start ≠ r₂.«end» ∧ res₂ = .ok s₂)))
      (insertTail s₁ i node parent ref) := by
  have hsound := preInsert_result_sound hwf₁ node parent ref
  unfold insertTail
  simp only [hnd]
  cases hpi : preInsert s₁ node parent ref with
  | error e =>
    rw [hpi] at hsound
    exact Or.inl ⟨e, hsound, rfl⟩
  | ok s₂ =>
    rw [hpi] at hsound
    refine Or.inr ⟨s₂, hsound, ?_⟩
    have hwf₂ := preInsert_preserves_wellformed hwf₁ hpi
    obtain ⟨-, ref'', -, hb, hins⟩ := hsound
    rw [hb hrn] at hins
    have hlen := insertSpec_ranges_length hins
    have hi₂ : i < s₂.ranges.length := by omega
    refine ⟨s₂.ranges[i], List.getElem?_eq_getElem hi₂, ?_⟩
    simp only [List.getElem?_eq_getElem hi₂]
    obtain ⟨nodes, hnodes, hch, hpar⟩ := insertSpec_children hwf₁ hins hnp hne href
    rw [last_eq_getLast? hnd hnodes]
    by_cases hcol : s₂.ranges[i].start = s₂.ranges[i].«end»
    · rw [if_pos (by simp [hcol])]
      refine Or.inl ⟨hcol, ?_⟩
      cases hlast : nodes.getLast? with
      | none =>
        have hnil : nodes = [] := List.getLast?_eq_none_iff.mp hlast
        subst hnil
        -- 何も入らないので状態は変わらない
        have hs₂ : s₂ = s₁ := by
          obtain ⟨nodes', hn', hcase⟩ := hins
          have := nodesToInsert_unique (TreeObsEq.refl _) hn' hnodes
          subst this
          rcases hcase with ⟨-, h⟩ | ⟨hne', -⟩
          · exact h
          · exact absurd rfl hne'
        subst hs₂
        have he := hempty hnodes _ (List.getElem?_eq_getElem hi₂) hcol
        simp only [Option.bind_none]
        rw [← he]
        show Except.ok s₂ = Except.ok { s₂ with ranges := s₂.ranges.set i s₂.ranges[i] }
        rw [List.set_getElem_self]
      | some l =>
        obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
        have hlp : parentOf s₂.tree l = some parent := hpar l (by rw [hys]; simp)
        -- parent の children は「reference node より前」++ 入った node ++ 残り
        have hcount := nodes_length_eq hnd hnodes
        obtain ⟨P, Q, hPQ, hPlen⟩ : ∃ P Q, childrenOf s₂.tree parent = P ++ nodes ++ Q ∧
            P.length + nodes.length = newOffsetOf s₁.tree parent ref node := by
          unfold newOffsetOf
          simp only [hnd]
          rw [← hcount]
          cases ref with
          | none =>
            refine ⟨childrenOf s₁.tree parent, [], by rw [hch, insertAllBefore_none]; simp, ?_⟩
            rw [lengthOf_eq_children hcck]
          | some c =>
            have hcp := href c rfl
            obtain ⟨j, hj⟩ := index_isSome hwf₁ hcp
            obtain ⟨u, v, huv, hul, hcu⟩ := (index_eq_some_iff_split hcp).mp hj
            have hcn : c ≠ node := fun he => hrn (by rw [he])
            refine ⟨u, c :: v, ?_, by simp [hj, hul]⟩
            rw [hch, huv, insertAllBefore_some nodes u v hcu
              (not_mem_nodes_of_child hwf₁ hnd hnodes hne hcp hcn)]
        have hidx : index s₂.tree l = some (P.length + ys.length) := by
          refine (index_eq_some_iff_split hlp).mpr ⟨P ++ ys, Q, by rw [hPQ, hys]; simp, by simp, ?_⟩
          intro hm
          have hnd₂ := childrenOf_nodup hwf₂ parent
          rw [hPQ, hys, show P ++ (ys ++ [l]) ++ Q = (P ++ ys) ++ l :: Q by simp] at hnd₂
          exact (List.nodup_append.mp hnd₂).2.2 l hm l (by simp) rfl
        simp only [Option.bind_some, siblingBP, hlp, hidx, if_true]
        rw [← hPlen, hys]
        simp only [List.length_append, List.length_singleton, Nat.add_assoc]
        rfl
    · rw [if_neg (by simpa using hcol)]
      exact Or.inr ⟨hcol, rfl⟩

/-! ## 全体 -/

/--
**`insertNode` の結果は、成否によらず関係を満たす。**

`this` が live range として妥当（`RangeValid`）であることを仮定する。
-/
theorem rangeInsertNode_result_sound {s : DOMState} {i : Nat} {r : RangeState} (node : NodeId)
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r) :
    InsertNodeResult s i r node (rangeInsertNode s i node) := by
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, hso⟩, -⟩ := id hrv
  unfold rangeInsertNode
  rw [hr]
  simp only [hs]
  -- step 1
  by_cases h1 : (sd.kind == .processingInstruction || sd.kind == .comment ||
      (sd.kind.isText && (parentOf s.tree r.start.node).isNone) || r.start.node == node) = true
  · rw [if_pos h1]
    exact Or.inl ⟨(hierarchyError_iff hs).mp h1, rfl⟩
  rw [if_neg h1]
  have hn1 : ¬ InsertNodeHierarchyError s.tree r.start.node node :=
    fun h' => h1 ((hierarchyError_iff hs).mpr h')
  refine Or.inr ⟨hn1, ?_⟩
  by_cases ht : sd.kind.isText = true
  · -- step 3-7：Text
    rw [if_pos ht]
    have hIsText : IsText s.tree r.start.node := ⟨sd, hs, ht⟩
    cases hp : parentOf s.tree r.start.node with
    | none => exact absurd (Or.inr (Or.inr (Or.inl ⟨hIsText, hp⟩))) hn1
    | some p =>
      simp only []
      cases hv : ensurePreInsertionValidity s.tree node p (some r.start.node) [] with
      | error e => exact Or.inl ⟨hIsText, p, rfl, Or.inl ⟨e, (preInsertValidity_iff hwf).mpr hv, rfl⟩⟩
      | ok u => exact Or.inl ⟨hIsText, p, rfl, Or.inr ⟨(preInsertValidity_iff hwf).mpr hv, rfl⟩⟩
  rw [if_neg ht]
  have hnt : ¬ IsText s.tree r.start.node := by
    rintro ⟨d, hd, hdk⟩
    rw [hs] at hd
    cases hd
    exact ht hdk
  have hsn : r.start.node ≠ node := fun he => hn1 (Or.inr (Or.inr (Or.inr he)))
  refine Or.inr ⟨hnt, _, childAtOffset_spec hwf hs r.start.offset, ?_⟩
  -- step 6
  cases hv : ensurePreInsertionValidity s.tree node r.start.node (sd.children[r.start.offset]?) [] with
  | error e => exact Or.inl ⟨e, (preInsertValidity_iff hwf).mpr hv, rfl⟩
  | ok u =>
  cases u
  have hv' := (preInsertValidity_iff hwf).mpr hv
  refine Or.inr ⟨hv', ?_⟩
  simp only []
  obtain ⟨hpc, ⟨nd, hnd⟩⟩ := parentIsContainer_of_validity hv'
  have hcck : ChildCountKind s.tree r.start.node := childCountKind_of_container hpc
  have hchild := childAtOffset_spec hwf hs r.start.offset
  -- step 8
  generalize href_def : sd.children[r.start.offset]? = ref at hchild hv' ⊢
  have hstep8 : (ref = some node ∧
        (if (ref == some node) = true then nextSibling s.tree node else ref) =
          nextSibling s.tree node) ∨
      (ref ≠ some node ∧ (if (ref == some node) = true then nextSibling s.tree node else ref) = ref) := by
    by_cases hrn : ref = some node
    · exact Or.inl ⟨hrn, by rw [if_pos (by simp [hrn])]⟩
    · exact Or.inr ⟨hrn, by rw [if_neg (by simpa using hrn)]⟩
  generalize href'_def : (if (ref == some node) = true then nextSibling s.tree node else ref) = ref'
    at hstep8 ⊢
  have hrn' : ref' ≠ some node := by
    rcases hstep8 with ⟨-, he⟩ | ⟨hne, he⟩
    · rw [he]; exact nextSibling_ne_self hwf node
    · rw [he]; exact hne
  -- reference node（step 8 の後）は start node の子で node ではない
  have hrefc : ∀ c, ref' = some c → parentOf s.tree c = some r.start.node ∧ c ≠ node := by
    intro c hc
    refine ⟨?_, fun he => hrn' (by rw [hc, he])⟩
    rcases hstep8 with ⟨hrn, he⟩ | ⟨-, he⟩
    · rw [hrn] at hchild
      exact parentOf_nextSibling hwf hchild.1 (he ▸ hc)
    · rw [he] at hc
      rw [hc] at hchild
      exact hchild.1
  refine ⟨ref', hstep8, ?_⟩
  -- step 9 の後の状態についての共通部分
  have tail : ∀ s₁ : DOMState, WellFormed s₁.tree → ShapePreserving s.tree s₁.tree →
      parentOf s₁.tree node = none → (∀ x, x ≠ node → parentOf s₁.tree x = parentOf s.tree x) →
      s₁.ranges.length = s.ranges.length →
      (NodesToInsert s₁.tree node [] → ∀ r₁, s₁.ranges[i]? = some r₁ →
        r₁.start = r₁.«end» → r₁.«end» = ⟨r.start.node, newOffsetOf s₁.tree r.start.node ref' node⟩) →
      ∃ newOffset, NewOffset s₁.tree r.start.node ref' node newOffset ∧
        AndThen (PreInsertResult s₁ node r.start.node ref')
          (fun s₂ res₂ => ∃ r₂, s₂.ranges[i]? = some r₂ ∧
            ((r₂.start = r₂.«end» ∧
                res₂ = .ok { s₂ with
                  ranges := s₂.ranges.set i { r₂ with «end» := ⟨r.start.node, newOffset⟩ } }) ∨
              (r₂.start ≠ r₂.«end» ∧ res₂ = .ok s₂)))
          (insertTail s₁ i node r.start.node ref') := by
    intro s₁ hwf₁ hsp₁ hnp₁ hpar₁ hlen₁ hempty
    obtain ⟨nd₁, hnd₁, -⟩ := kind_of_shapePreserving hsp₁ hnd
    have href₁ : ∀ c, ref' = some c → parentOf s₁.tree c = some r.start.node := by
      intro c hc
      obtain ⟨hcp, hcn⟩ := hrefc c hc
      rw [hpar₁ c hcn]
      exact hcp
    exact ⟨_, newOffsetOf_spec hwf₁ hnd₁ href₁,
      insertTail_spec hwf₁ hnd₁ hnp₁ (Ne.symm hsn) (childCountKind_of_shapePreserving hsp₁ hcck)
        href₁ hrn' (by rw [hlen₁]; exact (List.getElem?_eq_some_iff.mp hr).1) hempty⟩
  by_cases hpn : (parentOf s.tree node).isSome = true
  · -- step 9：外す
    rw [if_pos hpn]
    obtain ⟨s₁, hrm⟩ := (remove_succeeds_iff hwf (n := node) (b := false)).mpr hpn
    simp only [hrm]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hpn
    refine ⟨s₁, Or.inr ⟨⟨p, hp⟩, remove_sound hwf hrm⟩, ?_⟩
    refine tail s₁ (remove_preserves_wellformed hwf hrm) (shapePreserving_remove hrm)
      (remove_parentOf hrm)
      (fun x hx => by rw [parentOf_detach (remove_ok hrm).2, if_neg hx])
      (by rw [remove_ranges hp hrm, List.length_map]) ?_
    -- 何も入らないのは空の DocumentFragment だけで、それは parent を持たない
    intro hn
    exfalso
    obtain ⟨d, hd, hc⟩ := hn
    obtain ⟨d₀, hd₀, hk₀, -⟩ := (shapePreserving_remove hrm).exists_get? hd
    rcases hc with ⟨hk, -⟩ | ⟨-, hc⟩
    · have := h.structural.fragmentHasNoParent node d₀ hd₀ (by rw [hk₀, hk])
      simp only [parentOf_eq, hd₀, Option.bind_some, this] at hp
      cases hp
    · cases hc
  · -- step 9：parent が無い
    rw [if_neg hpn]
    simp only []
    have hnp : parentOf s.tree node = none := by simpa using hpn
    refine ⟨s, Or.inl ⟨hnp, rfl⟩, ?_⟩
    refine tail s hwf (ShapePreserving.refl _) hnp (fun _ _ => rfl) rfl ?_
    -- 空の DocumentFragment：range の end は既に (start node, newOffset) にある
    intro hn r₁ hr₁ hcol
    rw [hr] at hr₁
    cases hr₁
    obtain ⟨d, hd, hc⟩ := hn
    rw [hnd] at hd
    cases hd
    rcases hc with ⟨hk, hch⟩ | ⟨-, hc⟩
    · have hrr : ref' = ref := by
        rcases hstep8 with ⟨hrn, -⟩ | ⟨-, he⟩
        · rw [hrn] at hchild
          rw [hchild.1] at hnp
          cases hnp
        · exact he
      have hcnt : lengthOf s.tree node = 0 := by
        rw [lengthOf_of_get? hnd]
        simp [NodeData.length, hk, NodeKind.isCharacterData, ← hch]
      rw [← hcol]
      show r.start = ⟨r.start.node, newOffsetOf s.tree r.start.node ref' node⟩
      unfold newOffsetOf
      simp only [hnd, if_pos hk, hcnt, Nat.add_zero]
      rw [hrr]
      cases hrc : ref with
      | none =>
        have hge : sd.children.length ≤ r.start.offset := by
          exact List.getElem?_eq_none_iff.mp (href_def.trans hrc)
        have hlen : lengthOf s.tree r.start.node = sd.children.length := by
          rw [lengthOf_eq_children hcck, childrenOf_eq hs]
        have hle : r.start.offset ≤ sd.children.length := by
          have := hcck sd hs
          rw [NodeData.length_eq_children this.1 this.2] at hso
          exact hso
        simp only [hlen]
        rw [show sd.children.length = r.start.offset by omega]
      | some c =>
        rw [hrc] at hchild
        simp only [hchild.2, Option.getD_some]
    · cases hc

end Dom.Spec
