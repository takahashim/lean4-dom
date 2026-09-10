import Dom.Range.Adjust
import Dom.Properties.Algorithms

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
theorem ChildCountKind.map {t t' : Tree} {n : NodeId} (hk : KindPreserving t t')
    (h : ChildCountKind t n) : ChildCountKind t' n := by
  intro d' hd'
  have hm := hk n
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

theorem index_isSome {t : Tree} {n p : NodeId} (hwf : WellFormed t)
    (hp : parentOf t n = some p) : ∃ i, index t n = some i := by
  have hmem : n ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hp
  unfold index
  rw [hp]
  simp only [Option.bind_some]
  cases hf : (childrenOf t p).findIdx? (fun c => decide (c = n)) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    exfalso
    rw [List.findIdx?_eq_none_iff] at hf
    have hn := hf n hmem
    simp at hn

/-! ## detach と length -/

theorem lengthOf_detach_parent {t t' : Tree} {n p : NodeId}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (hd : detach t n = .ok t')
    (hlen : ChildCountKind t p) :
    lengthOf t' p + 1 = lengthOf t p := by
  have hlen' : ChildCountKind t' p := hlen.map (kindPreserving_detach hd)
  have hch : childrenOf t' p = removeAll (childrenOf t p) n := detach_childrenOf hwf hp hd
  have hmem : n ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hp
  have hnd : (childrenOf t p).Nodup := by
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
    rw [childrenOf_eq hpd]
    exact hwf.children_nodup p pd hpd
  rw [lengthOf_eq_children hlen', lengthOf_eq_children hlen, hch]
  exact length_removeAll hnd hmem

/-! ## remove と range -/

theorem remove_ranges {s s' : DOMState} {n p : NodeId} (hp : parentOf s.tree n = some p)
    (h : remove s n = .ok s') :
    s'.ranges = s.ranges.map (liveRangePreRemoveRange s.tree n p ((index s.tree n).getD 0)) := by
  simp only [remove, hp] at h
  unfold detachWithLiveAdjust at h
  obtain ⟨_, hs⟩ := DOMState.mapTree_eq_ok h
  rw [hs]
  show (iteratorPreRemove (liveRangePreRemove s n) n).ranges = _
  rw [iteratorPreRemove_ranges]
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
    have hk := kindPreserving_detach hd p
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
theorem remove_preserves_endpoints {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hlen : ChildCountKind s.tree p) (hv : RangeEndpointsValid s)
    (h : remove s n = .ok s') : RangeEndpointsValid s' := by
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
theorem remove_leaves_subtree {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n = .ok s') :
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
  have hlen' : ChildCountKind t' parent := hlen.map (kindPreserving_insertAt h)
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
      have hk := kindPreserving_insertAt h parent
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
      have hk := kindPreserving_insertAt h parent
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
      simp only [rangeShiftAfterInsert, Bool.and_eq_true, decide_eq_true_eq]
      rw [if_neg hcond]
    rw [hres]
    exact valid_of_insertAt hwf hlen h hbp

/--
PLAN §8.3。parent を持たない node の `insert` は range の両端を木の中に保つ。

parent を持つ node の場合は、`insert` の中で `adopt` が `remove` を呼ぶので、
挿入側の調整と削除側の調整が続けて走る。
仕様は挿入側の調整（step 5）を adopt（step 7）より前に置いているため、
その途中では offset が parent の length を一時的に超えうる。
合成の証明は残りとして `docs/status.md` に記す。
-/
theorem insert_preserves_endpoints {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {nd : NodeData}
    (hwf : WellFormed s.tree) (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (hnp : nd.parent = none) (hlen : ChildCountKind s.tree parent)
    (hv : RangeEndpointsValid s) (h : insert s node parent child = .ok s') :
    RangeEndpointsValid s' := by
  obtain ⟨pd, s₁, hpd, ha, hi, hsr⟩ := insert_single hnd hk h
  -- node に parent が無いので adopt は remove を呼ばない
  have hnpar : parentOf (liveRangeInsertAdjust s parent child 1).tree node = none := by
    simp only [liveRangeInsertAdjust_tree, parentOf, hnd]
    simpa using hnp
  obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases ha
  have hs₀ : s₀ = liveRangeInsertAdjust s parent child 1 := by
    rcases hstep with ⟨_, he⟩ | hr
    · exact he
    · exfalso
      obtain ⟨⟨q, hq⟩, _⟩ := remove_ok hr
      rw [hnpar] at hq
      simp at hq
  -- s₁ の tree は s.tree か、その node document を付け替えたもの
  have hs₁ : s₁.ranges = (liveRangeInsertAdjust s parent child 1).ranges ∧
      ∀ bp, ValidBoundaryPoint s.tree bp → ValidBoundaryPoint s₁.tree bp := by
    rcases hfinal with he | he
    · rw [he, hs₀]
      exact ⟨rfl, fun bp hbp => by simpa using hbp⟩
    · rw [he, hs₀]
      refine ⟨rfl, fun bp hbp => ?_⟩
      show ValidBoundaryPoint (Dom.setOwnerDocument _ node pd.ownerDocument) bp
      exact ValidBoundaryPoint.setOwnerDocument (by simpa using hbp)
  have hlen₁ : ChildCountKind s₁.tree parent := by
    rcases hfinal with he | he
    · rw [he, hs₀]; simpa using hlen
    · rw [he, hs₀]
      exact (show ChildCountKind s.tree parent from hlen).map
        (by simpa using kindPreserving_setOwnerDocument s.tree node pd.ownerDocument)
  have hwf₁ : WellFormed s₁.tree :=
    adopt_preserves_wellformed (by simpa using hwf)
      (by simpa using isDocument_ownerDocument hwf hpd) ha
  intro r hr
  rw [hsr, hs₁.1] at hr
  -- child が指定されているかで、range が調整されるかが決まる
  cases hc : child with
  | none =>
    rw [hc] at hr
    simp only [liveRangeInsertAdjust] at hr
    obtain ⟨hstart, hend⟩ := hv r hr
    exact ⟨valid_of_insertAt hwf₁ hlen₁ hi (hs₁.2 _ hstart),
      valid_of_insertAt hwf₁ hlen₁ hi (hs₁.2 _ hend)⟩
  | some c =>
    rw [hc] at hr
    simp only [liveRangeInsertAdjust] at hr
    obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
    obtain ⟨hstart, hend⟩ := hv r₀ hr₀
    rw [← hrr]
    exact ⟨valid_rangeShiftAfterInsert hwf₁ hlen₁ hi (hs₁.2 _ hstart),
      valid_rangeShiftAfterInsert hwf₁ hlen₁ hi (hs₁.2 _ hend)⟩

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

end Dom
