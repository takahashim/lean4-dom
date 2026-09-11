import Dom.Validity.Admissible

/-!
# 契約：成功条件と例外の順序

`notes/research-foundation-roadmap.md` §6。

preservation（妥当な入力から妥当な出力）と effect / frame は
`Dom/Validity/` と `Dom/Properties/` に散らばっている。
ここに置くのは残りの二つ、**success** と **exception** のうち、
研究上意味のある部分である。

例外については「どの例外が起こりうるか」だけでなく **検査の順序** を残す。
複数の違反が同時にあるときにどれが先に返るかは観測可能で、
Dommy で実際に不一致が見つかった箇所でもある（`docs/status.md` の finding 7 と 8）。
-/

namespace Dom

/-! ## remove の成功条件 -/

/-- `remove` が成功するのは、node が parent を持つときちょうどである。 -/
theorem remove_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree) {n : NodeId} {b : Bool} :
    (∃ s', remove s n b = .ok s') ↔ (parentOf s.tree n).isSome := by
  constructor
  · rintro ⟨s', h⟩
    obtain ⟨⟨p, hp⟩, _⟩ := remove_ok h
    rw [hp]
    rfl
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨nd, hnd, hnp⟩ := parentOf_eq_some hp
    obtain ⟨pd, hpd⟩ : ∃ pd, s.tree.get? p = some pd := exists_data_of_parentOf hwf hp
    have hde : detach s.tree n = .ok (detachFrom s.tree n p nd pd) := by
      simp [detach, hnd, hnp, hpd]
    unfold remove
    rw [hp]
    simp only
    cases hd : detachWithLiveAdjust s n with
    | error e =>
      exfalso
      unfold detachWithLiveAdjust DOMState.mapTree at hd
      simp only [iteratorPreRemove_tree, liveRangePreRemove_tree, hde] at hd
      simp at hd
    | ok sd =>
      cases b
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

/-- `remove` が失敗するのは、node が parent を持たないときちょうどである。 -/
theorem remove_error_iff {s : DOMState} (hwf : WellFormed s.tree) {n : NodeId} {b : Bool}
    {e : DOMException} :
    remove s n b = .error e ↔ (parentOf s.tree n = none ∧ e = .notFoundError) := by
  constructor
  · intro h
    cases hp : parentOf s.tree n with
    | none =>
      refine ⟨rfl, ?_⟩
      simp only [remove, hp] at h
      simpa using h.symm
    | some p =>
      exfalso
      obtain ⟨s', hok⟩ := (remove_succeeds_iff (b := b) hwf).mpr (by rw [hp]; rfl)
      rw [hok] at h
      simp at h
  · rintro ⟨hp, rfl⟩
    unfold remove
    rw [hp]

/-- `pre-remove` が失敗するのは、child の parent が指定した parent でないときである。 -/
theorem preRemove_error_notFound {s : DOMState} {child parent : NodeId}
    (h : parentOf s.tree child ≠ some parent) :
    preRemove s child parent = .error .notFoundError := by
  unfold preRemove
  rw [if_pos h]

/-! ## ensure pre-insertion validity の検査順序 -/

section PreInsertOrder

variable {t : Tree} {node parent : NodeId} {child : Option NodeId} {excl : List NodeId}
  {pd nd : NodeData}

/-- step 1。parent が children を持てない kind なら、他に何があっても HierarchyRequestError。 -/
theorem ensurePreInsertionValidity_step1
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = false) :
    ensurePreInsertionValidity t node parent child excl = .error .hierarchyRequestError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  refine if_pos ?_
  cases hkk : pd.kind <;> rw [hkk] at hk <;> simp_all [NodeKind.canHaveChildren]

/-- step 2。cycle は step 3 以降の違反より先に返る。 -/
theorem ensurePreInsertionValidity_step2
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = true)
    (hanc : isInclusiveAncestorOf t node parent = true) :
    ensurePreInsertionValidity t node parent child excl = .error .hierarchyRequestError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by cases hkk : pd.kind <;> rw [hkk] at hk <;>
    simp_all [NodeKind.canHaveChildren]), if_pos hanc]

/-- step 3。reference child が parent の子でないなら NotFoundError。 -/
theorem ensurePreInsertionValidity_step3
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = true)
    (hanc : isInclusiveAncestorOf t node parent = false)
    (hch : childHasParent t child parent = false) :
    ensurePreInsertionValidity t node parent child excl = .error .notFoundError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by cases hkk : pd.kind <;> rw [hkk] at hk <;>
    simp_all [NodeKind.canHaveChildren]), if_neg (by rw [hanc]; simp),
    if_pos (by rw [hch]; simp)]

end PreInsertOrder

/--
cycle（step 2）は「reference child が子でない」（step 3）より先に返る。

`parent.replaceChild(parent, parent)` は HierarchyRequestError であって
NotFoundError ではない。前もって親子関係を見てしまう実装はここを取り違える。
-/
theorem replace_cycle_precedes_notFound {s : DOMState} {parent : NodeId} {pd : NodeData}
    (hwf : WellFormed s.tree) (hpd : s.tree.get? parent = some pd)
    (hk : pd.kind.canHaveChildren = true) :
    replace s parent parent parent = .error .hierarchyRequestError := by
  unfold replace
  rw [ensurePreInsertionValidity_step2 hpd hpd hk
    ((isInclusiveAncestorOf_iff hwf parent parent).mpr (Or.inl rfl))]

/-- `insertBefore` でも同じ順序である。 -/
theorem insertBefore_cycle_precedes_notFound {s : DOMState} {parent : NodeId} {pd : NodeData}
    (hwf : WellFormed s.tree) (hpd : s.tree.get? parent = some pd)
    (hk : pd.kind.canHaveChildren = true) :
    insertBefore s parent parent (some parent) = .error .hierarchyRequestError := by
  unfold insertBefore preInsert
  rw [ensurePreInsertionValidity_step2 hpd hpd hk
    ((isInclusiveAncestorOf_iff hwf parent parent).mpr (Or.inl rfl))]

/-! ## move の検査順序 -/

section MoveOrder

variable {t : Tree} {node newParent : NodeId} {child : Option NodeId} {pd nd : NodeData}

/-- move step 1。root が違えば、他に何があっても HierarchyRequestError。 -/
theorem moveValidity_step1
    (hpd : t.get? newParent = some pd) (hnd : t.get? node = some nd)
    (hroot : root t newParent ≠ root t node) :
    moveValidity t node newParent child = .error .hierarchyRequestError := by
  unfold moveValidity
  rw [hpd, hnd]
  simp only
  rw [if_pos hroot]

/-- move step 2。cycle は step 3 の NotFoundError より先に返る。 -/
theorem moveValidity_step2
    (hpd : t.get? newParent = some pd) (hnd : t.get? node = some nd)
    (hroot : root t newParent = root t node)
    (hanc : isInclusiveAncestorOf t node newParent = true) :
    moveValidity t node newParent child = .error .hierarchyRequestError := by
  unfold moveValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by simpa using hroot), if_pos hanc]

/-- move step 3。reference child が新しい parent の子でないなら NotFoundError。 -/
theorem moveValidity_step3
    (hpd : t.get? newParent = some pd) (hnd : t.get? node = some nd)
    (hroot : root t newParent = root t node)
    (hanc : isInclusiveAncestorOf t node newParent = false)
    (hch : childHasParent t child newParent = false) :
    moveValidity t node newParent child = .error .notFoundError := by
  unfold moveValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by simpa using hroot), if_neg (by rw [hanc]; simp), if_pos (by rw [hch]; simp)]

/-- move step 4。動かせるのは Element と CharacterData だけである。 -/
theorem moveValidity_step4
    (hpd : t.get? newParent = some pd) (hnd : t.get? node = some nd)
    (hroot : root t newParent = root t node)
    (hanc : isInclusiveAncestorOf t node newParent = false)
    (hch : childHasParent t child newParent = true)
    (hkind : nd.kind.isElementOrCharacterData = false) :
    moveValidity t node newParent child = .error .hierarchyRequestError := by
  unfold moveValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by simpa using hroot), if_neg (by rw [hanc]; simp), if_neg (by rw [hch]; simp),
    if_pos (by unfold NodeKind.isElementOrCharacterData at hkind; rw [hkind]; simp)]

end MoveOrder

/-! ## public API の委譲 -/

/--
薄い public API は §4.2.3 の algorithm をそのまま呼ぶ。

この一方向の依存が、「どの API から始めても live object の調整が迂回されない」ことの土台である。
委譲が definitional なものは `rfl` で示せる。
-/
theorem appendChild_refines_append (s : DOMState) (parent node : NodeId) :
    appendChild s parent node = append s node parent := rfl

theorem append_refines_preInsert (s : DOMState) (node parent : NodeId) :
    append s node parent = preInsert s node parent none := rfl

theorem insertBefore_refines_preInsert (s : DOMState) (parent node : NodeId)
    (child : Option NodeId) :
    insertBefore s parent node child = preInsert s node parent child := rfl

theorem replaceChild_refines_replace (s : DOMState) (parent node child : NodeId) :
    replaceChild s parent node child = replace s child node parent := rfl

theorem removeChild_refines_preRemove (s : DOMState) (parent child : NodeId) :
    removeChild s parent child = preRemove s child parent := rfl

/-- `remove()` は parent がある場合だけ `remove` に委譲し、無ければ何もしない。 -/
theorem nodeRemove_refines_remove (s : DOMState) (this : NodeId)
    (h : (parentOf s.tree this).isSome) : nodeRemove s this = remove s this := by
  unfold nodeRemove
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  rw [hp]

theorem nodeRemove_noop (s : DOMState) (this : NodeId) (h : parentOf s.tree this = none) :
    nodeRemove s this = .ok s := by
  unfold nodeRemove
  rw [h]

/-- `replaceChildren(null)` は検査なしで `replace all` に委譲する。 -/
theorem replaceChildren_none_refines_replaceAll (s : DOMState) (parent : NodeId) :
    replaceChildren s parent none = replaceAll s none parent := rfl

/-- `moveBefore` は receiver の kind を検査してから `move` に委譲する。 -/
theorem moveBefore_refines_move {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : moveBefore s parent node child = .ok s') :
    ∃ ref, move s node parent ref = .ok s' := by
  obtain ⟨_, ref, _, _, hm⟩ := moveBefore_ok h
  exact ⟨ref, hm⟩

end Dom
