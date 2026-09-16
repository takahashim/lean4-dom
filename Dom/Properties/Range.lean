import Dom.Range.Adjust
import Dom.Properties.Algorithms
import Dom.Properties.Path

/-!
# Phase 5 の theorem

PLAN §8.3 に挙げた性質のうち、boundary point が木の中に留まる部分を証明する。

* `remove_preserves_endpoints` — `remove` の後も range の両端は木の中にある
* `remove_leaves_subtree` — 削除された node の inclusive descendant を
  端点に持つ range は、操作後には存在しない（`memo.md` §7 の形式化）
* `insert_preserves_endpoints` — fragment でない node の `insert` について同様

`RangeValid` のうち順序（`BoundaryLE`）の保存はまだ証明していない。
`docs/status.md` に残りとして記す。
-/

namespace Dom

open Dom.ListUtil

/-! ## length と children の対応 -/

/--
`n` の length が children の個数で決まる kind であること。

CharacterData と DocumentType 以外がこれにあたる。
仕様の pre-insertion validity は parent を Document / DocumentFragment / Element に限るので、
子を持つ node ではつねに成り立つ。`WellFormed` はこれを要求していないので、
range の定理では前提として置く。
-/
def ChildCountKind (t : Tree) (n : NodeId) : Prop :=
  ∀ d, t.get? n = some d → d.kind.isCharacterData = false ∧ d.kind ≠ .documentType

theorem NodeData.length_eq_children {d : NodeData} (h1 : d.kind.isCharacterData = false)
    (h2 : d.kind ≠ .documentType) : d.length = d.children.length := by
  simp [NodeData.length, h1, h2]

theorem childCountKind_of_kind {t : Tree} {n : NodeId}
    (h : ∀ d, t.get? n = some d →
      d.kind = .document ∨ d.kind = .documentFragment ∨ d.kind = .element) :
    ChildCountKind t n := by
  intro d hd
  rcases h d hd with hk | hk | hk <;> simp [hk, NodeKind.isCharacterData]

theorem lengthOf_eq_children {t : Tree} {n : NodeId} (h : ChildCountKind t n) :
    lengthOf t n = (childrenOf t n).length := by
  unfold lengthOf childrenOf
  cases hd : t.get? n with
  | none => rfl
  | some d =>
    obtain ⟨h1, h2⟩ := h d hd
    exact NodeData.length_eq_children h1 h2

/-- kind を変えない変更は `ChildCountKind` を保つ。 -/
theorem ChildCountKind.map {t t' : Tree} {n : NodeId} (hk : ShapePreserving t t')
    (h : ChildCountKind t n) : ChildCountKind t' n := by
  intro d' hd'
  have hm := hk.kind n
  rw [hd'] at hm
  cases hd : t.get? n with
  | none => rw [hd] at hm; simp at hm
  | some d =>
    rw [hd] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    obtain ⟨h1, h2⟩ := h d hd
    exact ⟨by rw [hm]; exact h1, by rw [hm]; exact h2⟩

/-! ## index の上界 -/

theorem index_lt_children_length {t : Tree} {n p : NodeId} {i : Nat}
    (hp : parentOf t n = some p) (hi : index t n = some i) :
    i < (childrenOf t p).length := by
  unfold index at hi
  rw [hp] at hi
  simp only [Option.bind_some] at hi
  exact (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).1

/-! ## detach と length -/

theorem lengthOf_detach_parent {t t' : Tree} {n p : NodeId}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (hd : detach t n = .ok t')
    (hlen : ChildCountKind t p) :
    lengthOf t' p + 1 = lengthOf t p := by
  have hlen' : ChildCountKind t' p := hlen.map (shapePreserving_detach hd)
  have hch : childrenOf t' p = removeAll (childrenOf t p) n := detach_childrenOf hwf hp hd
  have hmem : n ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hp
  have hnd : (childrenOf t p).Nodup := by
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
    rw [childrenOf_eq hpd]
    exact hwf.children_nodup p pd hpd
  rw [lengthOf_eq_children hlen', lengthOf_eq_children hlen, hch]
  exact length_removeAll hnd hmem

/-! ## 状態の射影が同じなら性質も移る -/

/-- record を積む step のように木と range を変えない step の後でも、両端の validity は残る。 -/
theorem rangeEndpointsValid_congr {s₁ s₂ : DOMState} (ht : s₁.tree = s₂.tree)
    (hr : s₁.ranges = s₂.ranges) (h : RangeEndpointsValid s₂) : RangeEndpointsValid s₁ := by
  intro r hrm
  rw [ht]
  exact h r (by rw [← hr]; exact hrm)

/-! ## remove と range -/

theorem remove_ranges {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    s'.ranges = s.ranges.map (liveRangePreRemoveRange s.tree n p ((index s.tree n).getD 0)) := by
  simp only [remove, hp] at h
  split at h
  · simp at h
  · next sd hd =>
    -- step 20-21 は range を変えない。
    have hr : s'.ranges = sd.ranges := by
      split at h
      · rw [← Except.ok.inj h]; simp
      · rw [← Except.ok.inj h]; simp
    rw [hr]
    obtain ⟨_, _, hs⟩ := detachWithLiveAdjust_cases hd
    rw [hs, DOMState.withTree_ranges, iteratorPreRemove_ranges]
    simp only [liveRangePreRemove, hp]

/--
`remove` の後も boundary point は木の中にある。

三つの場合がある。
削除された部分木の中を指していた点は `(parent, index)` に移り、
parent を指していて index より後ろにあった点は 1 手前にずれ、
それ以外は変わらない。
-/
theorem valid_liveRangePreRemoveBP {t t' : Tree} {n p : NodeId} {i : Nat} {bp : BoundaryPoint}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (hi : index t n = some i)
    (hlen : ChildCountKind t p) (hd : detach t n = .ok t')
    (hbp : ValidBoundaryPoint t bp) :
    ValidBoundaryPoint t' (liveRangePreRemoveBP t n p i bp) := by
  have hshrink : lengthOf t' p + 1 = lengthOf t p := lengthOf_detach_parent hwf hp hd hlen
  have hilt : i < (childrenOf t p).length := index_lt_children_length hp hi
  have hip : i < lengthOf t p := by rw [lengthOf_eq_children hlen]; exact hilt
  obtain ⟨pd', hpd'⟩ : ∃ pd', t'.get? p = some pd' := by
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
    have hk := shapePreserving_detach hd p
    rw [hpd] at hk
    cases hq : t'.get? p with
    | none => rw [hq] at hk; simp at hk
    | some pd' => exact ⟨pd', rfl⟩
  have hpd'len : pd'.length = lengthOf t' p := by unfold lengthOf; rw [hpd']
  obtain ⟨d, hdd, hoff⟩ := hbp
  by_cases hin : isInclusiveAncestorOf t n bp.node = true
  · have hres : liveRangePreRemoveBP t n p i bp = { node := p, offset := i } := by
      simp [liveRangePreRemoveBP, rangeMoveOutOfSubtree, rangeShiftAfterRemove, hin]
    rw [hres]
    exact ⟨pd', hpd', by simp only []; omega⟩
  · have hbpn : bp.node ≠ n := by
      intro he
      exact hin (by rw [he]; simp [isInclusiveAncestorOf])
    have hmove : liveRangePreRemoveBP t n p i bp = rangeShiftAfterRemove p i bp := by
      simp [liveRangePreRemoveBP, rangeMoveOutOfSubtree, hin]
    rw [hmove]
    by_cases hnp : bp.node = p
    · have hoffp : bp.offset ≤ lengthOf t p := by
        rw [← hnp]; unfold lengthOf; rw [hdd]; exact hoff
      by_cases hgt : i < bp.offset
      · have hres : rangeShiftAfterRemove p i bp = { bp with offset := bp.offset - 1 } := by
          simp [rangeShiftAfterRemove, hnp, hgt]
        rw [hres]
        refine ⟨pd', ?_, ?_⟩
        · show t'.get? bp.node = some pd'
          rw [hnp]; exact hpd'
        · show bp.offset - 1 ≤ pd'.length
          omega
      · have hres : rangeShiftAfterRemove p i bp = bp := by
          simp [rangeShiftAfterRemove, hgt]
        rw [hres]
        refine ⟨pd', ?_, ?_⟩
        · rw [hnp]; exact hpd'
        · omega
    · have hres : rangeShiftAfterRemove p i bp = bp := by
        simp [rangeShiftAfterRemove, hnp]
      rw [hres]
      have hframe : t'.get? bp.node = t.get? bp.node := by
        refine detach_frame hd hbpn ?_
        intro q hq
        rw [hp] at hq
        cases hq
        exact hnp
      exact ⟨d, by rw [hframe]; exact hdd, hoff⟩

/-- 移された boundary point は、削除された部分木の外にある。 -/
theorem liveRangePreRemoveBP_outside {t : Tree} {n p : NodeId} {i : Nat}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (bp : BoundaryPoint) :
    isInclusiveAncestorOf t n (liveRangePreRemoveBP t n p i bp).node = false := by
  have hnp : isInclusiveAncestorOf t n p = false := by
    cases hb : isInclusiveAncestorOf t n p with
    | false => rfl
    | true =>
      exfalso
      rcases (isInclusiveAncestorOf_iff hwf n p).mp hb with he | ha
      · exact hwf.acyclic n (Ancestor.step (he ▸ hp))
      · exact hwf.acyclic n (ha.trans_ancestor (Ancestor.step hp))
  by_cases hin : isInclusiveAncestorOf t n bp.node = true
  · have hres : liveRangePreRemoveBP t n p i bp = { node := p, offset := i } := by
      simp [liveRangePreRemoveBP, rangeMoveOutOfSubtree, rangeShiftAfterRemove, hin]
    rw [hres]; exact hnp
  · have hres : (liveRangePreRemoveBP t n p i bp).node = bp.node := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree rangeShiftAfterRemove
      rw [if_neg hin]
      split <;> rfl
    rw [hres]
    simpa using hin

/-! ## remove の定理 -/

/-- PLAN §8.3。`remove` は range の両端が木の中にあることを保つ。 -/
theorem remove_preserves_endpoints {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hlen : ChildCountKind s.tree p) (hv : RangeEndpointsValid s)
    (h : remove s n b = .ok s') : RangeEndpointsValid s' := by
  obtain ⟨i, hi⟩ := index_isSome hwf hp
  have hd := (remove_ok h).2
  have hranges : s'.ranges = s.ranges.map (liveRangePreRemoveRange s.tree n p i) := by
    rw [remove_ranges hp h, hi]; rfl
  intro r hr
  rw [hranges] at hr
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
  obtain ⟨hs, he⟩ := hv r₀ hr₀
  rw [← hrr]
  exact ⟨valid_liveRangePreRemoveBP hwf hp hi hlen hd hs,
    valid_liveRangePreRemoveBP hwf hp hi hlen hd he⟩

/--
PLAN §8.3 / `memo.md` §7。削除された node の inclusive descendant を端点に持つ range は、
`remove` の後には存在しない。

public API はすべて `remove` を経由するので（`Dom/Properties/Algorithms.lean`）、
どの API から始めてもこの性質は成り立つ。
-/
theorem remove_leaves_subtree {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    ∀ r ∈ s'.ranges,
      isInclusiveAncestorOf s.tree n r.start.node = false ∧
        isInclusiveAncestorOf s.tree n r.«end».node = false := by
  obtain ⟨i, hi⟩ := index_isSome hwf hp
  have hranges : s'.ranges = s.ranges.map (liveRangePreRemoveRange s.tree n p i) := by
    rw [remove_ranges hp h, hi]; rfl
  intro r hr
  rw [hranges] at hr
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
  rw [← hrr]
  exact ⟨liveRangePreRemoveBP_outside hwf hp r₀.start,
    liveRangePreRemoveBP_outside hwf hp r₀.«end»⟩

/-! ## insert と range -/

theorem lengthOf_insertAt_parent {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (hlen : ChildCountKind t parent)
    (h : insertAt t parent node child = .ok t') :
    lengthOf t' parent = lengthOf t parent + 1 := by
  have hlen' : ChildCountKind t' parent := hlen.map (shapePreserving_insertAt h)
  rw [lengthOf_eq_children hlen', lengthOf_eq_children hlen, insertAt_childrenOf hwf h]
  exact ListUtil.length_insertBefore _ _ _

/-- `setOwnerDocument` は node の length を変えないので boundary point の validity を保つ。 -/
theorem ValidBoundaryPoint.setOwnerDocument {t : Tree} {n doc : NodeId} {bp : BoundaryPoint}
    (h : ValidBoundaryPoint t bp) : ValidBoundaryPoint (Dom.setOwnerDocument t n doc) bp := by
  obtain ⟨d, hd, hoff⟩ := h
  rw [ValidBoundaryPoint, get?_setOwnerDocument, hd]
  by_cases hm : bp.node ∈ preorder t n
  · exact ⟨{ d with ownerDocument := doc }, by simp [hm], by simpa [NodeData.length] using hoff⟩
  · exact ⟨d, by simp [hm], hoff⟩

/-- `insertAt` は node の length を減らさないので boundary point の validity を保つ。 -/
theorem valid_of_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    {bp : BoundaryPoint} (hwf : WellFormed t) (hlen : ChildCountKind t parent)
    (h : insertAt t parent node child = .ok t') (hbp : ValidBoundaryPoint t bp) :
    ValidBoundaryPoint t' bp := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, ht⟩ := insertAt_ok_cases h
  obtain ⟨d, hdd, hoff⟩ := hbp
  by_cases hbn : bp.node = parent
  · have hgrow : lengthOf t' parent = lengthOf t parent + 1 :=
      lengthOf_insertAt_parent hwf hlen h
    obtain ⟨pd', hpd'⟩ : ∃ pd', t'.get? parent = some pd' := by
      have hk := shapePreserving_insertAt h parent
      rw [hpd] at hk
      cases hq : t'.get? parent with
      | none => rw [hq] at hk; simp at hk
      | some pd' => exact ⟨pd', rfl⟩
    have hpd'len : pd'.length = lengthOf t' parent := by unfold lengthOf; rw [hpd']
    have hoffp : bp.offset ≤ lengthOf t parent := by
      rw [← hbn]; unfold lengthOf; rw [hdd]; exact hoff
    exact ⟨pd', by rw [hbn]; exact hpd', by rw [hbn] at *; omega⟩
  · by_cases hnn : bp.node = node
    · subst hnn
      rw [hnd] at hdd
      cases hdd
      refine ⟨{ nd with parent := some parent }, ?_, hoff⟩
      rw [ht]; exact get?_insertAtIn_self t parent bp.node child pd nd
    · refine ⟨d, ?_, hoff⟩
      rw [ht, get?_insertAtIn_other hnn hbn]
      exact hdd

/--
挿入側の offset 調整を通した boundary point は、`insertAt` の後も木の中にある。

parent の children がちょうど一つ増えるので、
挿入位置より後ろを指していた点の offset を 1 増やしても範囲に収まる。
-/
theorem valid_rangeShiftAfterInsert {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    {idx : Nat} {bp : BoundaryPoint}
    (hwf : WellFormed t) (hlen : ChildCountKind t parent)
    (h : insertAt t parent node child = .ok t') (hbp : ValidBoundaryPoint t bp) :
    ValidBoundaryPoint t' (rangeShiftAfterInsert parent idx 1 bp) := by
  by_cases hcond : bp.node = parent ∧ idx < bp.offset
  · obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, ht⟩ := insertAt_ok_cases h
    obtain ⟨d, hdd, hoff⟩ := hbp
    have hgrow : lengthOf t' parent = lengthOf t parent + 1 :=
      lengthOf_insertAt_parent hwf hlen h
    obtain ⟨pd', hpd'⟩ : ∃ pd', t'.get? parent = some pd' := by
      have hk := shapePreserving_insertAt h parent
      rw [hpd] at hk
      cases hq : t'.get? parent with
      | none => rw [hq] at hk; simp at hk
      | some pd' => exact ⟨pd', rfl⟩
    have hpd'len : pd'.length = lengthOf t' parent := by unfold lengthOf; rw [hpd']
    have hoffp : bp.offset ≤ lengthOf t parent := by
      rw [← hcond.1]; unfold lengthOf; rw [hdd]; exact hoff
    have hres : rangeShiftAfterInsert parent idx 1 bp = { bp with offset := bp.offset + 1 } := by
      simp [rangeShiftAfterInsert, hcond.1, hcond.2]
    rw [hres]
    exact ⟨pd', by show t'.get? bp.node = some pd'; rw [hcond.1]; exact hpd', by
      show bp.offset + 1 ≤ pd'.length; omega⟩
  · have hres : rangeShiftAfterInsert parent idx 1 bp = bp := by
      unfold rangeShiftAfterInsert
      rw [if_neg hcond]
    rw [hres]
    exact valid_of_insertAt hwf hlen h hbp

/-! ## public API への持ち上げ -/

/--
PLAN §8.3。`remove` を経由する public API はすべて range の両端を木の中に保つ。

`memo.md` §7 の「どの API から始めても Range adjustment が迂回されない」を、
`remove` についてだけ示せば足りるという形で表している。
-/
theorem preRemove_preserves_endpoints {s s' : DOMState} {child parent : NodeId}
    (hwf : WellFormed s.tree) (hlen : ChildCountKind s.tree parent)
    (hv : RangeEndpointsValid s) (h : preRemove s child parent = .ok s') :
    RangeEndpointsValid s' := by
  unfold preRemove at h
  split at h
  · simp at h
  · next hp =>
    exact remove_preserves_endpoints hwf (by simpa using hp) hlen hv h

theorem removeChild_preserves_endpoints {s s' : DOMState} {parent child : NodeId}
    (hwf : WellFormed s.tree) (hlen : ChildCountKind s.tree parent)
    (hv : RangeEndpointsValid s) (h : removeChild s parent child = .ok s') :
    RangeEndpointsValid s' :=
  preRemove_preserves_endpoints hwf hlen hv h

theorem nodeRemove_preserves_endpoints {s s' : DOMState} {this : NodeId}
    (hwf : WellFormed s.tree)
    (hlen : ∀ p, parentOf s.tree this = some p → ChildCountKind s.tree p)
    (hv : RangeEndpointsValid s) (h : nodeRemove s this = .ok s') :
    RangeEndpointsValid s' := by
  unfold nodeRemove at h
  split at h
  · rw [← Except.ok.inj h]; exact hv
  · next p hp => exact remove_preserves_endpoints hwf hp (hlen p hp) hv h

/--
`move` も `remove` を経由するので、削除された部分木から range は追い出される。

挿入側の調整は offset しか変えないので、node についての性質はそのまま残る。
-/
theorem move_leaves_subtree {s s' : DOMState} {node newParent p : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (hp : parentOf s.tree node = some p)
    (h : move s node newParent child = .ok s') :
    ∀ r ∈ s'.ranges,
      isInclusiveAncestorOf s.tree node r.start.node = false ∧
        isInclusiveAncestorOf s.tree node r.«end».node = false := by
  obtain ⟨s₁, hr, hranges⟩ := move_ranges h
  intro r hrmem
  rw [hranges] at hrmem
  obtain ⟨r₀, hr₀, hstart, hend⟩ := liveRangeInsertAdjust_nodes s₁ newParent child 1 r hrmem
  obtain ⟨h1, h2⟩ := remove_leaves_subtree hwf hp hr r₀ hr₀
  exact ⟨by rw [hstart]; exact h1, by rw [hend]; exact h2⟩

/-! ## insert の途中で許す「余裕」つきの validity -/

/--
`parent` を指す boundary point については offset が `length + slack` 以下であればよい、
という緩めた validity。

仕様の `insert` は step 5 で「これから入る node の個数」だけ offset を先に増やしてから
step 7 で実際に挿入する。その途中では offset が parent の length を一時的に超えるので、
この形で不変量を持ち回る。`slack = 0` のときはちょうど `ValidBoundaryPoint` になる。
-/
def BoundaryValidUpTo (t : Tree) (parent : NodeId) (slack : Nat) (bp : BoundaryPoint) : Prop :=
  ∃ d, t.get? bp.node = some d ∧
    bp.offset ≤ d.length + (if bp.node = parent then slack else 0)

def RangeValidUpTo (s : DOMState) (parent : NodeId) (slack : Nat) : Prop :=
  ∀ r ∈ s.ranges,
    BoundaryValidUpTo s.tree parent slack r.start ∧ BoundaryValidUpTo s.tree parent slack r.«end»

theorem boundaryValidUpTo_zero {t : Tree} {parent : NodeId} {bp : BoundaryPoint} :
    BoundaryValidUpTo t parent 0 bp ↔ ValidBoundaryPoint t bp := by
  unfold BoundaryValidUpTo ValidBoundaryPoint
  constructor
  · rintro ⟨d, hd, hoff⟩
    exact ⟨d, hd, by split at hoff <;> omega⟩
  · rintro ⟨d, hd, hoff⟩
    exact ⟨d, hd, by split <;> omega⟩

theorem rangeValidUpTo_zero {s : DOMState} {parent : NodeId} :
    RangeValidUpTo s parent 0 ↔ RangeEndpointsValid s := by
  unfold RangeValidUpTo RangeEndpointsValid EndpointsValid
  constructor
  · intro h r hr
    exact ⟨boundaryValidUpTo_zero.mp (h r hr).1, boundaryValidUpTo_zero.mp (h r hr).2⟩
  · intro h r hr
    exact ⟨boundaryValidUpTo_zero.mpr (h r hr).1, boundaryValidUpTo_zero.mpr (h r hr).2⟩

theorem boundaryValidUpTo_mono {t : Tree} {parent : NodeId} {a b : Nat} {bp : BoundaryPoint}
    (hab : a ≤ b) (h : BoundaryValidUpTo t parent a bp) : BoundaryValidUpTo t parent b bp := by
  obtain ⟨d, hd, hoff⟩ := h
  exact ⟨d, hd, by split at hoff <;> split <;> omega⟩

/-! ## setOwnerDocument は長さを変えない -/

theorem length_setOwnerDocument {t : Tree} {n doc m : NodeId} {d : NodeData}
    (h : (Dom.setOwnerDocument t n doc).get? m = some d) :
    ∃ d₀, t.get? m = some d₀ ∧ d.length = d₀.length := by
  rw [get?_setOwnerDocument] at h
  cases h₀ : t.get? m with
  | none => rw [h₀] at h; simp at h
  | some d₀ =>
    rw [h₀] at h
    by_cases hm : m ∈ preorder t n
    · simp only [Option.map_some, if_pos hm] at h
      exact ⟨d₀, rfl, by rw [← Option.some.inj h]; simp [NodeData.length]⟩
    · simp only [Option.map_some, if_neg hm] at h
      exact ⟨d₀, rfl, by rw [← Option.some.inj h]⟩

theorem boundaryValidUpTo_setOwnerDocument {t : Tree} {n doc parent : NodeId} {slack : Nat}
    {bp : BoundaryPoint} (h : BoundaryValidUpTo t parent slack bp) :
    BoundaryValidUpTo (Dom.setOwnerDocument t n doc) parent slack bp := by
  obtain ⟨d, hd, hoff⟩ := h
  obtain ⟨d', hd', hlen⟩ : ∃ d', (Dom.setOwnerDocument t n doc).get? bp.node = some d' ∧
      d'.length = d.length := by
    rw [get?_setOwnerDocument, hd]
    by_cases hm : bp.node ∈ preorder t n
    · exact ⟨{ d with ownerDocument := doc }, by simp [hm], rfl⟩
    · exact ⟨d, by simp [hm], rfl⟩
  exact ⟨d', hd', by rw [hlen]; exact hoff⟩

/-! ## insertAt と余裕つき validity -/

theorem parentOf_insertAt_other {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') {m : NodeId} (hm : m ≠ node) :
    parentOf t' m = parentOf t m := by
  obtain ⟨pd, nd, hpd, hnd, _, _, _, ht⟩ := insertAt_ok_cases h
  rw [ht, parentOf_insertAtIn hpd, if_neg hm]

/-- `insertAt` は parent の children を一つ増やすので、余裕を一つ使える。 -/
theorem boundaryValidUpTo_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    {slack : Nat} {bp : BoundaryPoint} (hwf : WellFormed t) (hlen : ChildCountKind t parent)
    (h : insertAt t parent node child = .ok t')
    (hv : BoundaryValidUpTo t parent (slack + 1) bp) :
    BoundaryValidUpTo t' parent slack bp := by
  by_cases hbn : bp.node = parent
  · obtain ⟨d, hd, hoff⟩ := hv
    rw [if_pos hbn] at hoff
    have hgrow : lengthOf t' parent = lengthOf t parent + 1 :=
      lengthOf_insertAt_parent hwf hlen h
    have hdlen : lengthOf t parent = d.length := by unfold lengthOf; rw [← hbn, hd]
    obtain ⟨pd', hpd'⟩ : ∃ pd', t'.get? parent = some pd' := by
      have hk := shapePreserving_insertAt h parent
      obtain ⟨pd, hpd⟩ : ∃ pd, t.get? parent = some pd := ⟨d, by rw [← hbn]; exact hd⟩
      rw [hpd] at hk
      cases hq : t'.get? parent with
      | none => rw [hq] at hk; simp at hk
      | some pd' => exact ⟨pd', rfl⟩
    have hpd'len : pd'.length = lengthOf t' parent := by unfold lengthOf; rw [hpd']
    exact ⟨pd', by rw [hbn]; exact hpd', by rw [if_pos hbn]; omega⟩
  · have hvalid : ValidBoundaryPoint t bp := by
      obtain ⟨d, hd, hoff⟩ := hv
      rw [if_neg hbn] at hoff
      exact ⟨d, hd, by omega⟩
    exact boundaryValidUpTo_mono (Nat.zero_le _)
      (boundaryValidUpTo_zero.mpr (valid_of_insertAt hwf hlen h hvalid))

/-! ## 親を持たない node の列を入れる -/

theorem adopt_of_no_parent {s s₁ : DOMState} {node doc : NodeId}
    (hp : parentOf s.tree node = none) (h : adopt s node doc = .ok s₁) :
    s₁.ranges = s.ranges ∧
      (s₁.tree = s.tree ∨ s₁.tree = Dom.setOwnerDocument s.tree node doc) := by
  obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases h
  have hs₀ : s₀ = s := by
    rcases hstep with ⟨_, he⟩ | hr
    · exact he
    · exfalso
      obtain ⟨⟨q, hq⟩, _⟩ := remove_ok hr
      rw [hp] at hq
      simp at hq
  subst hs₀
  rcases hfinal with he | he <;> rw [he]
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

/--
parent を持たない node の列を順に入れるとき、
`insert` の step 5 で先に足しておいた余裕がちょうど使い切られる。
-/
theorem insertEach_valid_of_no_parent :
    ∀ (nodes : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      WellFormed s.tree → IsDocument s.tree doc → ChildCountKind s.tree parent → nodes.Nodup →
      (∀ n ∈ nodes, parentOf s.tree n = none) →
      RangeValidUpTo s parent nodes.length →
      insertEach s parent child doc nodes = .ok s' →
      RangeEndpointsValid s'
  | [], s, s', parent, child, doc, _, _, _, _, _, hv, h => by
    rw [insertEach] at h
    rw [← Except.ok.inj h]
    exact rangeValidUpTo_zero.mp (by simpa using hv)
  | n :: ns, s, s', parent, child, doc, hwf, hdoc, hlen, hnd, hnp, hv, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      obtain ⟨hr₁, ht₁⟩ := adopt_of_no_parent (hnp n (List.mem_cons_self ..)) ha
      split at h
      · simp at h
      · next s₂ hi =>
        obtain ⟨hi', hi₂⟩ := DOMState.mapTree_eq_ok hi
        have hwf₁ : WellFormed s₁.tree := adopt_preserves_wellformed hwf hdoc ha
        have hdoc₁ : IsDocument s₁.tree doc := hdoc.map (shapePreserving_adopt ha)
        have hlen₁ : ChildCountKind s₁.tree parent := hlen.map (shapePreserving_adopt ha)
        have hv₁ : RangeValidUpTo s₁ parent (ns.length + 1) := by
          intro r hr
          rw [hr₁] at hr
          obtain ⟨h1, h2⟩ := hv r hr
          simp only [List.length_cons] at h1 h2
          rcases ht₁ with he | he
          · rw [he]; exact ⟨h1, h2⟩
          · rw [he]
            exact ⟨boundaryValidUpTo_setOwnerDocument h1, boundaryValidUpTo_setOwnerDocument h2⟩
        have hv₂ : RangeValidUpTo s₂ parent ns.length := by
          intro r hr
          rw [hi₂] at hr ⊢
          simp only [DOMState.withTree_ranges, DOMState.withTree_tree] at hr ⊢
          obtain ⟨h1, h2⟩ := hv₁ r hr
          exact ⟨boundaryValidUpTo_insertAt hwf₁ hlen₁ hi' h1,
            boundaryValidUpTo_insertAt hwf₁ hlen₁ hi' h2⟩
        have hnp₂ : ∀ n' ∈ ns, parentOf s₂.tree n' = none := by
          intro n' hn'
          have hne : n' ≠ n := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hn')
          have h1 : parentOf s₂.tree n' = parentOf s₁.tree n' := by
            rw [hi₂]
            exact parentOf_insertAt_other hi' hne
          have h2 : parentOf s₁.tree n' = parentOf s.tree n' := by
            rcases ht₁ with he | he
            · rw [he]
            · rw [he, parentOf_setOwnerDocument]
          rw [h1, h2]
          exact hnp n' (List.mem_cons_of_mem _ hn')
        refine insertEach_valid_of_no_parent ns ?_ ?_ ?_ ?_ hnp₂ hv₂ h
        · rw [hi₂]; exact insertAt_preserves_wellformed hwf₁ hi'
        · rw [hi₂]; exact hdoc₁.map (shapePreserving_insertAt hi')
        · rw [hi₂]; exact hlen₁.map (shapePreserving_insertAt hi')
        · exact (List.nodup_cons.mp hnd).2

/-! ## step 5 の調整が作る余裕 -/

theorem boundaryValidUpTo_rangeShiftAfterInsert {t : Tree} {parent : NodeId} {idx k : Nat}
    {bp : BoundaryPoint} (hv : ValidBoundaryPoint t bp) :
    BoundaryValidUpTo t parent k (rangeShiftAfterInsert parent idx k bp) := by
  obtain ⟨d, hd, hoff⟩ := hv
  unfold rangeShiftAfterInsert
  by_cases hc : bp.node = parent ∧ idx < bp.offset
  · rw [if_pos hc]
    refine ⟨d, hd, ?_⟩
    show bp.offset + k ≤ d.length + (if bp.node = parent then k else 0)
    rw [if_pos hc.1]
    omega
  · rw [if_neg hc]
    exact ⟨d, hd, by split <;> omega⟩

/-- `insert` の step 5 は、parent を指す boundary point に `count` だけの余裕を作る。 -/
theorem rangeValidUpTo_liveRangeInsertAdjust {s : DOMState} {parent : NodeId}
    {child : Option NodeId} {k : Nat} (hv : RangeEndpointsValid s) :
    RangeValidUpTo (liveRangeInsertAdjust s parent child k) parent k := by
  intro r hr
  unfold liveRangeInsertAdjust at hr ⊢
  split at hr
  · obtain ⟨h1, h2⟩ := hv r hr
    exact ⟨boundaryValidUpTo_mono (Nat.zero_le _) (boundaryValidUpTo_zero.mpr h1),
      boundaryValidUpTo_mono (Nat.zero_le _) (boundaryValidUpTo_zero.mpr h2)⟩
  · obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
    obtain ⟨h1, h2⟩ := hv r₀ hr₀
    rw [← hrr]
    exact ⟨boundaryValidUpTo_rangeShiftAfterInsert h1,
      boundaryValidUpTo_rangeShiftAfterInsert h2⟩

/-! ## 同じ parent からまとめて外す -/

/-- `remove` の列は、既に parent を持たない node の parent を変えない。 -/
theorem removeEach_keeps_none :
    ∀ (ns : List NodeId) {s s' : DOMState} {n : NodeId} {b : Bool},
      parentOf s.tree n = none → removeEach s ns b = .ok s' → parentOf s'.tree n = none
  | [], s, s', n, b, hn, h => by rw [← Except.ok.inj h]; exact hn
  | m :: ms, s, s', n, b, hn, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      refine removeEach_keeps_none ms ?_ h
      rw [parentOf_detach (remove_ok hr).2]
      split
      · rfl
      · exact hn

/--
同じ parent を持つ node の列を順に `remove` する。

`insert` が DocumentFragment の children を先に外す step 4 に対応する。
-/
theorem removeEach_from_parent :
    ∀ (ns : List NodeId) {s s' : DOMState} {p : NodeId} {b : Bool},
      WellFormed s.tree → ChildCountKind s.tree p → ns.Nodup →
      (∀ n ∈ ns, parentOf s.tree n = some p) →
      RangeEndpointsValid s → removeEach s ns b = .ok s' →
      RangeEndpointsValid s' ∧ (∀ n ∈ ns, parentOf s'.tree n = none) ∧
        WellFormed s'.tree ∧ ChildCountKind s'.tree p ∧ ShapePreserving s.tree s'.tree
  | [], s, s', p, b, hwf, hlen, _, _, hv, h => by
    rw [← Except.ok.inj h]
    exact ⟨hv, by simp, hwf, hlen, ShapePreserving.refl _⟩
  | n :: ns, s, s', p, b, hwf, hlen, hnd, hpar, hv, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      have hpn : parentOf s.tree n = some p := hpar n (List.mem_cons_self ..)
      have hwf₁ : WellFormed s₁.tree := remove_preserves_wellformed hwf hr
      have hkp : ShapePreserving s.tree s₁.tree := shapePreserving_remove hr
      have hlen₁ : ChildCountKind s₁.tree p := hlen.map hkp
      have hv₁ : RangeEndpointsValid s₁ := remove_preserves_endpoints hwf hpn hlen hv hr
      have hnone : parentOf s₁.tree n = none := remove_parentOf hr
      have hpar₁ : ∀ m ∈ ns, parentOf s₁.tree m = some p := by
        intro m hm
        have hne : m ≠ n := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hm)
        rw [parentOf_detach (remove_ok hr).2, if_neg hne]
        exact hpar m (List.mem_cons_of_mem _ hm)
      obtain ⟨hv', hnone', hwf', hlen', hkp'⟩ :=
        removeEach_from_parent ns hwf₁ hlen₁ (List.nodup_cons.mp hnd).2 hpar₁ hv₁ h
      refine ⟨hv', ?_, hwf', hlen', hkp.trans hkp'⟩
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact removeEach_keeps_none ns hnone h
      · exact hnone' m hm

/-! ## DocumentFragment を展開する insert -/

/--
PLAN §8.3。DocumentFragment を展開する `insert` も range の両端を木の中に保つ。

step 4 で fragment の children をすべて外してから step 7 で入れ直すので、
step 7 の時点ではどの node も parent を持たない。
step 5 で足した余裕はちょうど children の個数ぶんで、それが使い切られる。
-/
theorem insert_fragment_preserves_endpoints {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} {nd : NodeData}
    (hwf : WellFormed s.tree) (hnd : s.tree.get? node = some nd)
    (hk : (nd.kind == NodeKind.documentFragment) = true)
    (hlen : ChildCountKind s.tree parent)
    (hv : RangeEndpointsValid s) (h : insert s node parent child b = .ok s') :
    RangeEndpointsValid s' := by
  obtain ⟨nd', hnd', hcase⟩ := insert_cases h
  rw [hnd] at hnd'
  cases hnd'
  clear h
  rcases hcase with ⟨_, _, hsx⟩ | ⟨_, _, s₁, hre, h⟩ | ⟨hnf, _⟩
  · rw [hsx]; exact hv
  · -- fragment の children は fragment を parent に持つ
    have hfrag : ChildCountKind s.tree node := by
      refine childCountKind_of_kind ?_
      intro d hd
      rw [hnd] at hd
      cases hd
      exact Or.inr (Or.inl (by simpa using hk))
    have hnodup : nd.children.Nodup := hwf.children_nodup node nd hnd
    have hpar : ∀ m ∈ nd.children, parentOf s.tree m = some node := by
      intro m hm
      exact parentOf_of_mem_childrenOf hwf (by rw [childrenOf_eq hnd]; exact hm)
    obtain ⟨hv₁, hnone, hwf₁, _, hkp⟩ :=
      removeEach_from_parent nd.children hwf hfrag hnodup hpar hv hre
    have hlen₁ : ChildCountKind s₁.tree parent := hlen.map hkp
    -- step 5 と 7
    obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases h
    have hproj : s'.tree = sx.tree ∧ s'.ranges = sx.ranges := by
      rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨by simp, by simp⟩
    refine rangeEndpointsValid_congr hproj.1 hproj.2 ?_
    obtain ⟨pd, hpd, hx⟩ := insertEachAt_cases hx
    refine insertEach_valid_of_no_parent nd.children ?_ ?_ ?_ hnodup ?_ ?_ hx
    · simpa using hwf₁
    · exact isDocument_ownerDocument (by simpa using hwf₁) hpd
    · simpa using hlen₁
    · intro m hm
      simpa using hnone m hm
    · exact rangeValidUpTo_liveRangeInsertAdjust
        (rangeEndpointsValid_congr (by simp) (by simp) hv₁)
  · exact absurd (by simpa using hk) hnf

/-! ## parent を持つ node の insert -/

/--
削除側の調整も、余裕つきの validity を保つ。

`parent` がちょうど削除元だった場合は、children が一つ減るのと同時に
offset も一つ減るので、余裕はそのまま残る。
-/
theorem boundaryValidUpTo_liveRangePreRemoveBP {t t' : Tree} {n q parent : NodeId}
    {i slack : Nat} {bp : BoundaryPoint}
    (hwf : WellFormed t) (hp : parentOf t n = some q) (hi : index t n = some i)
    (hlenq : ChildCountKind t q) (hnotanc : isInclusiveAncestorOf t n parent = false)
    (hd : detach t n = .ok t')
    (hv : BoundaryValidUpTo t parent slack bp) :
    BoundaryValidUpTo t' parent slack (liveRangePreRemoveBP t n q i bp) := by
  by_cases hbp : bp.node = parent
  · obtain ⟨d, hdd, hoff⟩ := hv
    rw [if_pos hbp] at hoff
    have hnotin : isInclusiveAncestorOf t n bp.node = false := by rw [hbp]; exact hnotanc
    have hmove : liveRangePreRemoveBP t n q i bp = rangeShiftAfterRemove q i bp := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
      rw [if_neg (by simp [hnotin])]
    rw [hmove]
    have hpn : parent ≠ n := by
      intro he
      rw [← he,
        (isInclusiveAncestorOf_iff hwf parent parent).mpr (Or.inl rfl)] at hnotanc
      simp at hnotanc
    have hlenpd : lengthOf t parent = d.length := by unfold lengthOf; rw [← hbp, hdd]
    by_cases hq : q = parent
    · subst hq
      have hshrink : lengthOf t' q + 1 = lengthOf t q := lengthOf_detach_parent hwf hp hd hlenq
      have hiq : i < lengthOf t q := by
        rw [lengthOf_eq_children hlenq]; exact index_lt_children_length hp hi
      obtain ⟨pd', hpd'⟩ : ∃ pd', t'.get? q = some pd' := by
        obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
        have hkk := shapePreserving_detach hd q
        rw [hpd] at hkk
        cases hqq : t'.get? q with
        | none => rw [hqq] at hkk; simp at hkk
        | some pd' => exact ⟨pd', rfl⟩
      have hpd'len : pd'.length = lengthOf t' q := by unfold lengthOf; rw [hpd']
      unfold rangeShiftAfterRemove
      by_cases hgt : bp.node = q ∧ i < bp.offset
      · rw [if_pos hgt]
        refine ⟨pd', by show t'.get? bp.node = some pd'; rw [hbp]; exact hpd', ?_⟩
        show bp.offset - 1 ≤ pd'.length + (if bp.node = q then slack else 0)
        rw [if_pos hbp]
        omega
      · rw [if_neg hgt]
        have hle : bp.offset ≤ i := by
          rcases Nat.lt_or_ge i bp.offset with hlt | hge
          · exact (hgt ⟨hbp, hlt⟩).elim
          · exact hge
        refine ⟨pd', by show t'.get? bp.node = some pd'; rw [hbp]; exact hpd', ?_⟩
        show bp.offset ≤ pd'.length + (if bp.node = q then slack else 0)
        rw [if_pos hbp]
        omega
    · have hres : rangeShiftAfterRemove q i bp = bp := by
        unfold rangeShiftAfterRemove
        exact if_neg (fun hc => hq (by rw [← hc.1, hbp]))
      rw [hres]
      have hframe : t'.get? bp.node = t.get? bp.node := by
        refine detach_frame hd (by rw [hbp]; exact hpn) ?_
        intro q' hq'
        rw [hp] at hq'
        cases hq'
        rw [hbp]
        exact fun he => hq he.symm
      exact ⟨d, by rw [hframe]; exact hdd, by rw [if_pos hbp]; exact hoff⟩
  · have hvalid : ValidBoundaryPoint t bp := by
      obtain ⟨d, hdd, hoff⟩ := hv
      rw [if_neg hbp] at hoff
      exact ⟨d, hdd, by omega⟩
    exact boundaryValidUpTo_mono (Nat.zero_le _)
      (boundaryValidUpTo_zero.mpr (valid_liveRangePreRemoveBP hwf hp hi hlenq hd hvalid))

/--
PLAN §8.3。fragment でない node の `insert` は、node が parent を持っていても
range の両端を木の中に保つ。

仕様は挿入側の調整（step 5）を adopt → remove（step 7）より前に置くので、
その途中では offset が parent の length を一時的に超える。
`BoundaryValidUpTo` の「余裕」として持ち回ると、
削除側の調整（parent がちょうど削除元なら length と offset が同時に一つ減る）と
挿入（length が一つ増える）を通って、最後にちょうど valid に戻ることが示せる。
-/
theorem insert_single_preserves_endpoints {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} {nd : NodeData}
    (hwf : WellFormed s.tree) (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : insert s node parent child b = .ok s') :
    RangeEndpointsValid s' := by
  obtain ⟨pd, s₁, hpd, ha, hi, hsr⟩ := insert_single hnd hk h
  obtain ⟨pd', nd', hpd', hnd', hnp', hanc1, _, _⟩ := insertAt_ok_cases hi
  have hwf0 : WellFormed (liveRangeInsertAdjust s parent child 1).tree := by simpa using hwf
  have hdoc0 : IsDocument (liveRangeInsertAdjust s parent child 1).tree pd.ownerDocument := by
    simpa using isDocument_ownerDocument hwf hpd
  have hwf1 : WellFormed s₁.tree := adopt_preserves_wellformed hwf0 hdoc0 ha
  -- node が parent の inclusive ancestor でないことを、insertAt の検査から引き戻す
  have hanc : isInclusiveAncestorOf s.tree node parent = false := by
    cases hb : isInclusiveAncestorOf s.tree node parent with
    | false => rfl
    | true =>
      exfalso
      have hia : InclusiveAncestor s.tree node parent :=
        (isInclusiveAncestorOf_iff hwf node parent).mp hb
      obtain ⟨s₀', hstep, hfinal⟩ := adopt_ok_cases ha
      have hstep' : InclusiveAncestor s₀'.tree node parent := by
        rcases hstep with ⟨_, he⟩ | hr
        · rw [he]; simpa using hia
        · rcases hia with heq | hanc' 
          · exact Or.inl heq
          · refine Or.inr (ancestor_detach_of_not_below (remove_ok hr).2 (by simpa using hanc') ?_)
            rintro ⟨_, hcyc⟩
            exact hwf.acyclic node (by simpa using hcyc)
      have hia1 : InclusiveAncestor s₁.tree node parent := by
        rcases hfinal with he | he
        · rw [he]; exact hstep'
        · rw [he]
          rcases hstep' with heq | hanc'
          · exact Or.inl heq
          · exact Or.inr (ancestor_setOwnerDocument.mpr hanc')
      rw [(isInclusiveAncestorOf_iff hwf1 node parent).mpr hia1] at hanc1
      simp at hanc1
  -- step 5 の調整で余裕を一つ作る
  have hv0 : RangeValidUpTo (liveRangeInsertAdjust s parent child 1) parent 1 :=
    rangeValidUpTo_liveRangeInsertAdjust hv
  -- adopt を通しても余裕つき validity は保たれる
  have hv1 : RangeValidUpTo s₁ parent 1 := by
    obtain ⟨s₀', hstep, hfinal⟩ := adopt_ok_cases ha
    have hv0' : RangeValidUpTo s₀' parent 1 := by
      rcases hstep with ⟨_, he⟩ | hr
      · rw [he]; exact hv0
      · obtain ⟨⟨q, hq⟩, hdd⟩ := remove_ok hr
        have hq' : parentOf s.tree node = some q := by simpa using hq
        obtain ⟨i, hidx⟩ := index_isSome hwf hq'
        have hrng := remove_ranges hq hr
        intro r hr'
        rw [hrng] at hr'
        obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr'
        obtain ⟨h1, h2⟩ := hv0 r₀ hr₀
        rw [← hrr]
        have hidx' : (index (liveRangeInsertAdjust s parent child 1).tree node).getD 0 = i := by
          simp only [liveRangeInsertAdjust_tree, hidx]; rfl
        rw [hidx']
        constructor
        · exact boundaryValidUpTo_liveRangePreRemoveBP hwf0 hq (by simpa using hidx)
            (by simpa using hlenq q hq') (by simpa using hanc) hdd h1
        · exact boundaryValidUpTo_liveRangePreRemoveBP hwf0 hq (by simpa using hidx)
            (by simpa using hlenq q hq') (by simpa using hanc) hdd h2
    rcases hfinal with he | he
    · rw [he]; exact hv0'
    · rw [he]
      intro r hr'
      obtain ⟨h1, h2⟩ := hv0' r hr'
      exact ⟨boundaryValidUpTo_setOwnerDocument h1, boundaryValidUpTo_setOwnerDocument h2⟩
  -- 最後の insertAt で余裕を使い切る
  have hlen1 : ChildCountKind s₁.tree parent :=
    (show ChildCountKind (liveRangeInsertAdjust s parent child 1).tree parent by simpa using hlen
      ).map (shapePreserving_adopt ha)
  intro r hrmem
  rw [hsr] at hrmem
  obtain ⟨h1, h2⟩ := hv1 r hrmem
  exact ⟨boundaryValidUpTo_zero.mp (boundaryValidUpTo_insertAt hwf1 hlen1 hi h1),
    boundaryValidUpTo_zero.mp (boundaryValidUpTo_insertAt hwf1 hlen1 hi h2)⟩

/--
PLAN §8.3。`insert` は range の両端を木の中に保つ。

DocumentFragment を展開する場合とそうでない場合の両方を含む。
-/
theorem insert_preserves_endpoints {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : insert s node parent child b = .ok s') :
    RangeEndpointsValid s' := by
  cases hnd : s.tree.get? node with
  | none => rw [insert, hnd] at h; simp at h
  | some nd =>
    by_cases hk : (nd.kind == NodeKind.documentFragment) = true
    · exact insert_fragment_preserves_endpoints hwf hnd hk hlen hv h
    · exact insert_single_preserves_endpoints hwf hnd hk hlen hlenq hv h


/-! ## move の endpoints -/

/--
PLAN §8.3 の形。`move` は range の両端を木の中に保つ。

`move` は `remove` の pre-remove steps を走らせてから挿入側の調整をかけるので、
`remove` 側の保存に挿入側の「余裕を一つ作って使い切る」議論を繋ぐだけでよい。
-/
theorem move_preserves_endpoints {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (hlen : ChildCountKind s.tree newParent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : move s node newParent child = .ok s') :
    RangeEndpointsValid s' := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt h
  obtain ⟨s₂, hr₂, hrng⟩ := move_ranges h
  have hs : s₂ = s₁ := by
    rw [hr] at hr₂
    exact (Except.ok.inj hr₂).symm
  rw [hs] at hrng
  obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
  have hv₁ : RangeEndpointsValid s₁ :=
    remove_preserves_endpoints hwf hp (hlenq p hp) hv hr
  have hwf₁ : WellFormed s₁.tree := remove_preserves_wellformed hwf hr
  have hlen₁ : ChildCountKind s₁.tree newParent := hlen.map (shapePreserving_remove hr)
  have hup : RangeValidUpTo (liveRangeInsertAdjust s₁ newParent child 1) newParent 1 :=
    rangeValidUpTo_liveRangeInsertAdjust hv₁
  intro r hrmem
  rw [hrng] at hrmem
  obtain ⟨h1, h2⟩ := hup r hrmem
  simp only [liveRangeInsertAdjust_tree] at h1 h2
  exact ⟨boundaryValidUpTo_zero.mp (boundaryValidUpTo_insertAt hwf₁ hlen₁ hi h1),
    boundaryValidUpTo_zero.mp (boundaryValidUpTo_insertAt hwf₁ hlen₁ hi h2)⟩

/-- `moveBefore` も `move` を経由する。 -/
theorem moveBefore_preserves_endpoints {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : moveBefore s parent node child = .ok s') :
    RangeEndpointsValid s' := by
  obtain ⟨_, _, _, _, hm⟩ := moveBefore_ok h
  exact move_preserves_endpoints hwf hlen hlenq hv hm

/-! ## boundary point の順序（両端が同じ node の場合） -/

/--
両端が同じ node を指す boundary point の順序は、offset の比較そのものである。

仕様の boundary point position は step 2 で「nodeA が nodeB なら offset を比べる」と
決めているので、この場合は木の形に依らない。
-/
theorem boundaryLE_same_node {t : Tree} {a b : BoundaryPoint} (h : a.node = b.node) :
    BoundaryLE t a b ↔ a.offset ≤ b.offset := by
  unfold BoundaryLE bpPosition
  rw [if_pos h]
  constructor
  · rintro ⟨_, hne⟩
    exact Nat.compare_ne_gt.mp hne
  · intro hle
    exact ⟨by rw [h], Nat.compare_ne_gt.mpr hle⟩

/--
両端が同じ node を指し、順序も正しい range の集まり。

`BoundaryLE` の保存は一般には示せていないが、この形の range については示せる。
生成器が作る range もこの形である。
-/
def RangesSameNodeOrdered (s : DOMState) : Prop :=
  ∀ r ∈ s.ranges, r.start.node = r.«end».node ∧ r.start.offset ≤ r.«end».offset

theorem boundaryLE_of_sameNodeOrdered {s : DOMState} (h : RangesSameNodeOrdered s) :
    ∀ r ∈ s.ranges, BoundaryLE s.tree r.start r.«end» :=
  fun r hr => (boundaryLE_same_node (h r hr).1).mpr (h r hr).2

/-! ## 調整は同じ node の上で単調である -/

theorem rangeShiftAfterRemove_mono {q : NodeId} {i : Nat} {a b : BoundaryPoint}
    (hnode : a.node = b.node) (hle : a.offset ≤ b.offset) :
    (rangeShiftAfterRemove q i a).node = (rangeShiftAfterRemove q i b).node ∧
      (rangeShiftAfterRemove q i a).offset ≤ (rangeShiftAfterRemove q i b).offset := by
  unfold rangeShiftAfterRemove
  by_cases hq : a.node = q
  · by_cases h1 : i < a.offset
    · rw [if_pos ⟨hq, h1⟩, if_pos ⟨by rw [← hnode]; exact hq, by omega⟩]
      exact ⟨hnode, by show a.offset - 1 ≤ b.offset - 1; omega⟩
    · rw [if_neg (fun hc => h1 hc.2)]
      by_cases h2 : i < b.offset
      · rw [if_pos ⟨by rw [← hnode]; exact hq, h2⟩]
        exact ⟨hnode, by show a.offset ≤ b.offset - 1; omega⟩
      · rw [if_neg (fun hc => h2 hc.2)]
        exact ⟨hnode, hle⟩
  · rw [if_neg (fun hc => hq hc.1), if_neg (fun hc => hq (by rw [hnode]; exact hc.1))]
    exact ⟨hnode, hle⟩

theorem liveRangePreRemoveBP_mono {t : Tree} {n q : NodeId} {i : Nat} {a b : BoundaryPoint}
    (hnode : a.node = b.node) (hle : a.offset ≤ b.offset) :
    (liveRangePreRemoveBP t n q i a).node = (liveRangePreRemoveBP t n q i b).node ∧
      (liveRangePreRemoveBP t n q i a).offset ≤ (liveRangePreRemoveBP t n q i b).offset := by
  by_cases hin : isInclusiveAncestorOf t n a.node = true
  · have ha : liveRangePreRemoveBP t n q i a = rangeShiftAfterRemove q i ⟨q, i⟩ := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
      rw [if_pos hin]
    have hb : liveRangePreRemoveBP t n q i b = rangeShiftAfterRemove q i ⟨q, i⟩ := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
      rw [if_pos (by rw [← hnode]; exact hin)]
    rw [ha, hb]
    exact ⟨rfl, Nat.le_refl _⟩
  · have ha : liveRangePreRemoveBP t n q i a = rangeShiftAfterRemove q i a := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
      rw [if_neg hin]
    have hb : liveRangePreRemoveBP t n q i b = rangeShiftAfterRemove q i b := by
      unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
      rw [if_neg (by rw [← hnode]; exact hin)]
    rw [ha, hb]
    exact rangeShiftAfterRemove_mono hnode hle

theorem rangeShiftAfterInsert_mono {parent : NodeId} {idx k : Nat} {a b : BoundaryPoint}
    (hnode : a.node = b.node) (hle : a.offset ≤ b.offset) :
    (rangeShiftAfterInsert parent idx k a).node = (rangeShiftAfterInsert parent idx k b).node ∧
      (rangeShiftAfterInsert parent idx k a).offset ≤
        (rangeShiftAfterInsert parent idx k b).offset := by
  unfold rangeShiftAfterInsert
  by_cases hq : a.node = parent
  · by_cases h1 : idx < a.offset
    · rw [if_pos ⟨hq, h1⟩, if_pos ⟨by rw [← hnode]; exact hq, by omega⟩]
      exact ⟨hnode, by show a.offset + k ≤ b.offset + k; omega⟩
    · rw [if_neg (fun hc => h1 hc.2)]
      by_cases h2 : idx < b.offset
      · rw [if_pos ⟨by rw [← hnode]; exact hq, h2⟩]
        exact ⟨hnode, by show a.offset ≤ b.offset + k; omega⟩
      · rw [if_neg (fun hc => h2 hc.2)]
        exact ⟨hnode, hle⟩
  · rw [if_neg (fun hc => hq hc.1), if_neg (fun hc => hq (by rw [hnode]; exact hc.1))]
    exact ⟨hnode, hle⟩

theorem rangesSameNodeOrdered_congr {s₁ s₂ : DOMState} (hr : s₁.ranges = s₂.ranges)
    (h : RangesSameNodeOrdered s₂) : RangesSameNodeOrdered s₁ := by
  intro r hrm
  exact h r (by rw [← hr]; exact hrm)

/-! ## 各 algorithm が同じ node の上の順序を保つこと -/

theorem remove_preserves_sameNodeOrdered {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s')
    (hv : RangesSameNodeOrdered s) : RangesSameNodeOrdered s' := by
  intro r hr
  rw [remove_ranges hp h] at hr
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
  obtain ⟨hn, ho⟩ := hv r₀ hr₀
  rw [← hrr]
  exact liveRangePreRemoveBP_mono hn ho

theorem removeEach_preserves_sameNodeOrdered :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      RangesSameNodeOrdered s → removeEach s ns b = .ok s' → RangesSameNodeOrdered s'
  | [], s, s', b, hv, h => by rw [← Except.ok.inj h]; exact hv
  | n :: ns, s, s', b, hv, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
      exact removeEach_preserves_sameNodeOrdered ns
        (remove_preserves_sameNodeOrdered hp hr hv) h

theorem adopt_preserves_sameNodeOrdered {s s' : DOMState} {node doc : NodeId}
    (hv : RangesSameNodeOrdered s) (h : adopt s node doc = .ok s') :
    RangesSameNodeOrdered s' := by
  obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases h
  have hv₀ : RangesSameNodeOrdered s₀ := by
    rcases hstep with ⟨_, he⟩ | hr
    · rw [he]; exact hv
    · obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
      exact remove_preserves_sameNodeOrdered hp hr hv
  rcases hfinal with he | he <;> rw [he]
  · exact hv₀
  · intro r hr; exact hv₀ r hr

theorem insertEach_preserves_sameNodeOrdered :
    ∀ (nodes : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      RangesSameNodeOrdered s → insertEach s parent child doc nodes = .ok s' →
      RangesSameNodeOrdered s'
  | [], s, s', _, _, _, hv, h => by rw [insertEach] at h; rw [← Except.ok.inj h]; exact hv
  | n :: ns, s, s', parent, child, doc, hv, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      split at h
      · simp at h
      · next s₂ hi =>
        refine insertEach_preserves_sameNodeOrdered ns ?_ h
        rw [(DOMState.mapTree_eq_ok hi).2]
        intro r hr
        exact adopt_preserves_sameNodeOrdered hv ha r hr

theorem liveRangeInsertAdjust_preserves_sameNodeOrdered {s : DOMState} {parent : NodeId}
    {child : Option NodeId} {k : Nat} (hv : RangesSameNodeOrdered s) :
    RangesSameNodeOrdered (liveRangeInsertAdjust s parent child k) := by
  intro r hr
  unfold liveRangeInsertAdjust at hr
  split at hr
  · exact hv r hr
  · obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
    obtain ⟨hn, ho⟩ := hv r₀ hr₀
    rw [← hrr]
    exact rangeShiftAfterInsert_mono hn ho

/-- PLAN §8.3。`insert` は「両端が同じ node を指す range」の順序を保つ。 -/
theorem insert_preserves_sameNodeOrdered {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hv : RangesSameNodeOrdered s)
    (h : insert s node parent child b = .ok s') : RangesSameNodeOrdered s' := by
  have hstep : ∀ (u : DOMState) (ns : List NodeId) (b' : Bool), RangesSameNodeOrdered u →
      insertNodesAt u parent child ns b' = .ok s' → RangesSameNodeOrdered s' := by
    intro u ns b' hu hun
    obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases hun
    have hrx : s'.ranges = sx.ranges := by
      rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rfl
      · simp
    intro r hr
    rw [hrx] at hr
    obtain ⟨_, _, hx⟩ := insertEachAt_cases hx
    exact insertEach_preserves_sameNodeOrdered ns
      (liveRangeInsertAdjust_preserves_sameNodeOrdered hu) hx r hr
  obtain ⟨_, _, hcase⟩ := insert_cases h
  rcases hcase with ⟨_, _, hsx⟩ | ⟨_, _, _, hre, hins⟩ | ⟨_, hins⟩
  · rw [hsx]; exact hv
  · exact hstep _ _ _ (rangesSameNodeOrdered_congr (by simp)
      (removeEach_preserves_sameNodeOrdered _ hv hre)) hins
  · exact hstep s _ _ hv hins

/-- `remove` の後も、両端が同じ node を指す range は正しく並んでいる。 -/
theorem remove_preserves_boundaryLE_sameNode {s s' : DOMState} {n p : NodeId}
    (hp : parentOf s.tree n = some p) (h : remove s n = .ok s')
    (hv : RangesSameNodeOrdered s) :
    ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end» :=
  boundaryLE_of_sameNodeOrdered (remove_preserves_sameNodeOrdered hp h hv)

/--
PLAN §8.3。`remove` は range の順序を保つ。両端が別の node を指す場合も含む。

`Dom/Properties/Path.lean` の key 表現（`bpPosition_eq_lexCmp`）を使う。
live range pre-remove steps は key の上では `shiftKey` として働き、
`shiftKey` は辞書式順序について単調である。
-/
theorem remove_preserves_boundaryLE {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hv : RangeEndpointsValid s)
    (hord : ∀ r ∈ s.ranges, BoundaryLE s.tree r.start r.«end»)
    (h : remove s n = .ok s') :
    ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end» := by
  obtain ⟨i, hi⟩ := index_isSome hwf hp
  have hwf' : WellFormed s'.tree := remove_preserves_wellformed hwf h
  have hranges : s'.ranges = s.ranges.map (liveRangePreRemoveRange s.tree n p i) := by
    rw [remove_ranges hp h, hi]; rfl
  intro r hr
  rw [hranges] at hr
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
  obtain ⟨⟨ad, had, _⟩, ⟨bd, hbd, _⟩⟩ := hv r₀ hr₀
  rw [← hrr]
  exact boundaryLE_detach hwf hwf' hp hi (remove_ok h).2 had hbd (hord r₀ hr₀)

/-- `remove` は `RangeValid` を保つ。 -/
theorem remove_preserves_rangesValid {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hlen : ChildCountKind s.tree p) (hv : RangesValid s) (h : remove s n = .ok s') :
    RangesValid s' := by
  intro r hr
  obtain ⟨hs, he⟩ := remove_preserves_endpoints hwf hp hlen hv.endpoints h r hr
  exact ⟨hs, he, remove_preserves_boundaryLE hwf hp hv.endpoints
    (fun r₀ hr₀ => (hv r₀ hr₀).2.2) h r hr⟩

/-! ### remove を経由する public API への持ち上げ -/

theorem preRemove_preserves_rangesValid {s s' : DOMState} {child parent : NodeId}
    (hwf : WellFormed s.tree) (hlen : ChildCountKind s.tree parent)
    (hv : RangesValid s) (h : preRemove s child parent = .ok s') : RangesValid s' := by
  unfold preRemove at h
  split at h
  · simp at h
  · next hp => exact remove_preserves_rangesValid hwf (by simpa using hp) hlen hv h

theorem removeChild_preserves_rangesValid {s s' : DOMState} {parent child : NodeId}
    (hwf : WellFormed s.tree) (hlen : ChildCountKind s.tree parent)
    (hv : RangesValid s) (h : removeChild s parent child = .ok s') : RangesValid s' :=
  preRemove_preserves_rangesValid hwf hlen hv h

theorem nodeRemove_preserves_rangesValid {s s' : DOMState} {this : NodeId}
    (hwf : WellFormed s.tree)
    (hlen : ∀ p, parentOf s.tree this = some p → ChildCountKind s.tree p)
    (hv : RangesValid s) (h : nodeRemove s this = .ok s') : RangesValid s' := by
  unfold nodeRemove at h
  split at h
  · rw [← Except.ok.inj h]; exact hv
  · next p hp => exact remove_preserves_rangesValid hwf hp (hlen p hp) hv h

/-- `move` も `remove` と挿入側の調整を通るだけなので、同じ node の上の順序を保つ。 -/
theorem move_preserves_sameNodeOrdered {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hv : RangesSameNodeOrdered s)
    (h : move s node newParent child = .ok s') : RangesSameNodeOrdered s' := by
  obtain ⟨s₁, hr, hranges⟩ := move_ranges h
  obtain ⟨⟨p, hp⟩, _⟩ := remove_ok hr
  intro r hrmem
  rw [hranges] at hrmem
  exact liveRangeInsertAdjust_preserves_sameNodeOrdered
    (remove_preserves_sameNodeOrdered hp hr hv) r hrmem

/-- `insert` の後も、両端が同じ node を指す range は正しく並んでいる。 -/
theorem insert_preserves_boundaryLE {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hv : RangesSameNodeOrdered s)
    (h : insert s node parent child b = .ok s') :
    ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end» :=
  boundaryLE_of_sameNodeOrdered (insert_preserves_sameNodeOrdered hv h)

/-! ## insert 側の public API への持ち上げ -/

theorem preInsert_preserves_endpoints {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : preInsert s node parent child = .ok s') :
    RangeEndpointsValid s' := by
  unfold preInsert at h
  split at h
  · simp at h
  · exact insert_preserves_endpoints hwf hlen hlenq hv h

theorem appendChild_preserves_endpoints {s s' : DOMState} {parent node : NodeId}
    (hwf : WellFormed s.tree) (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : appendChild s parent node = .ok s') :
    RangeEndpointsValid s' :=
  preInsert_preserves_endpoints hwf hlen hlenq hv h

theorem insertBefore_preserves_endpoints {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (hlen : ChildCountKind s.tree parent)
    (hlenq : ∀ q, parentOf s.tree node = some q → ChildCountKind s.tree q)
    (hv : RangeEndpointsValid s) (h : insertBefore s parent node child = .ok s') :
    RangeEndpointsValid s' :=
  preInsert_preserves_endpoints hwf hlen hlenq hv h

theorem preInsert_preserves_sameNodeOrdered {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} (hv : RangesSameNodeOrdered s)
    (h : preInsert s node parent child = .ok s') : RangesSameNodeOrdered s' := by
  unfold preInsert at h
  split at h
  · simp at h
  · exact insert_preserves_sameNodeOrdered hv h

theorem preRemove_preserves_sameNodeOrdered {s s' : DOMState} {child parent : NodeId}
    (hv : RangesSameNodeOrdered s) (h : preRemove s child parent = .ok s') :
    RangesSameNodeOrdered s' := by
  unfold preRemove at h
  split at h
  · simp at h
  · next hp => exact remove_preserves_sameNodeOrdered (by simpa using hp) h hv

/-! ## pre-remove steps の二つの調整は可換である -/

/--
**§5.5 の step 3-4 と step 5-6 は、順序を入れ替えても結果が変わらない。**

step 5-6（offset をずらす）は boundary point の `node` を変えないので、
step 3-4（部分木の外へ移す）の条件に影響しない。逆に step 3-4 が移した先の
offset はちょうど `index` なので、step 5-6 の条件（`index` より大きい）に当てはまらない。

仕様は順序を定めているが、この定理があるので実装はどちらの順でもよい。
差分テストで順序を入れ替えても不一致が出ないのはこのためである
（`docs/status.md` の「定理が落ちても観測できるとは限らない」）。
-/
theorem liveRangePreRemoveBP_comm (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) :
    rangeShiftAfterRemove parent index (rangeMoveOutOfSubtree t node parent index bp)
      = rangeMoveOutOfSubtree t node parent index (rangeShiftAfterRemove parent index bp) := by
  unfold rangeMoveOutOfSubtree
  rw [rangeShiftAfterRemove_node]
  cases hin : isInclusiveAncestorOf t node bp.node with
  | true => simp [rangeShiftAfterRemove]
  | false => simp

end Dom
