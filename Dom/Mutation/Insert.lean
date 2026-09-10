import Dom.Basic.Exception
import Dom.Basic.WellFormed

/-!
# primitive mutation：insert

PLAN §5.1 の三つの primitive のうち、parent を持たない node を木に入れるもの。

仕様の insert（DOM Standard §4.2.3）は DocumentFragment の展開と
live object の調整を含む。ここでは一つの node を一箇所に入れる部分だけを切り出す。
-/

namespace Dom

/-- `node` を `parent` の children の `child` の直前（`none` なら末尾）に入れた木。 -/
def insertAtIn (t : Tree) (parent node : NodeId) (child : Option NodeId)
    (pd nd : NodeData) : Tree :=
  { nodes :=
      (t.nodes.insert parent
          { pd with children := Dom.ListUtil.insertBefore pd.children child node }).insert node
        { nd with parent := some parent } }

/--
parent を持たない node を、parent の children の child の直前に入れる。

PLAN §5.1 の四つの前提条件を明示的に検査する。

1. parent が存在する（無ければ `notFoundError`）
2. node が parent を持たない（持っていれば `hierarchyRequestError`）
3. node が parent の inclusive ancestor でない（そうなら `hierarchyRequestError`）
4. child が指定されていれば parent の子である（違えば `notFoundError`）

3 は DOM Standard §4.2.3 ensure pre-insertion validity の step 1、
4 は同 step 4 に対応する。
-/
def insertAt (t : Tree) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException Tree :=
  match t.get? parent with
  | none => .error .notFoundError
  | some pd =>
    match t.get? node with
    | none => .error .notFoundError
    | some nd =>
      if nd.parent.isSome then .error .hierarchyRequestError
      else if isInclusiveAncestorOf t node parent then .error .hierarchyRequestError
      else
        match child with
        | none => .ok (insertAtIn t parent node none pd nd)
        | some c =>
          if c ∈ pd.children then .ok (insertAtIn t parent node (some c) pd nd)
          else .error .notFoundError

/-! ## 場合分けのための equation lemma -/

theorem insertAt_eq_ok {t : Tree} {parent node : NodeId} {child : Option NodeId}
    {pd nd : NodeData}
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hnp : nd.parent = none) (hanc : isInclusiveAncestorOf t node parent = false)
    (hchild : ∀ c, child = some c → c ∈ pd.children) :
    insertAt t parent node child = .ok (insertAtIn t parent node child pd nd) := by
  cases child with
  | none => simp [insertAt, hpd, hnd, hnp, hanc]
  | some c => simp [insertAt, hpd, hnd, hnp, hanc, hchild c rfl]

/-- `insertAt` が成功したなら、四つの前提条件がすべて成り立っている。 -/
theorem insertAt_ok_cases {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') :
    ∃ pd nd, t.get? parent = some pd ∧ t.get? node = some nd ∧ nd.parent = none ∧
      isInclusiveAncestorOf t node parent = false ∧
      (∀ c, child = some c → c ∈ pd.children) ∧
      t' = insertAtIn t parent node child pd nd := by
  unfold insertAt at h
  split at h
  · simp at h
  · next pd hpd =>
    split at h
    · simp at h
    · next nd hnd =>
      split at h
      · simp at h
      · next hnp =>
        split at h
        · simp at h
        · next hanc =>
          have hnp' : nd.parent = none := Option.not_isSome_iff_eq_none.mp hnp
          have hanc' : isInclusiveAncestorOf t node parent = false := by simpa using hanc
          split at h
          · exact ⟨pd, nd, hpd, hnd, hnp', hanc', by simp, (Except.ok.inj h).symm⟩
          · next c =>
            split at h
            · next hc =>
              exact ⟨pd, nd, hpd, hnd, hnp', hanc',
                by rintro c' hc'; cases hc'; exact hc, (Except.ok.inj h).symm⟩
            · simp at h

end Dom
