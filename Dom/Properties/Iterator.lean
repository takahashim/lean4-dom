import Dom.Traversal.NodeIterator
import Dom.Properties.Range

/-!
# Phase 6 の theorem

PLAN §9.2 に挙げた性質を証明する。

* `remove_preserves_iterators_valid` — `remove` は iterator の reference を
  木の中かつ root の inclusive descendant に保つ
* `remove_iterators_leave_subtree` — 削除された node の inclusive descendant は、
  操作後どの iterator の reference にもならない（root が生き残る場合）
-/

namespace Dom

open Dom.ListUtil

/-! ## adjust a node pointer の性質 -/

/-- 削除する node は自分の parent の inclusive ancestor ではない。 -/
theorem not_inclusiveAncestor_parent {t : Tree} {n p : NodeId} (hwf : WellFormed t)
    (hp : parentOf t n = some p) : isInclusiveAncestorOf t n p = false := by
  cases hb : isInclusiveAncestorOf t n p with
  | false => rfl
  | true =>
    exfalso
    rcases (isInclusiveAncestorOf_iff hwf n p).mp hb with he | ha
    · exact hwf.acyclic n (Ancestor.step (he ▸ hp))
    · exact hwf.acyclic n (ha.trans_ancestor (Ancestor.step hp))

/-- 前の兄弟の部分木は、削除する node の部分木と交わらない。 -/
theorem not_inclusiveAncestor_prevSubtree {t : Tree} {n p prev x : NodeId} (hwf : WellFormed t)
    (hp : parentOf t n = some p) (hprev : parentOf t prev = some p) (hne : prev ≠ n)
    (hx : InclusiveAncestor t prev x) : isInclusiveAncestorOf t n x = false := by
  cases hb : isInclusiveAncestorOf t n x with
  | false => rfl
  | true =>
    exact absurd (sibling_subtrees_disjoint hwf hprev hp hne hx
      ((isInclusiveAncestorOf_iff hwf n x).mp hb)) (by simp)

/-- 前の兄弟は同じ parent を持つ。 -/
theorem parentOf_previousSibling {t : Tree} {n p prev : NodeId} (hwf : WellFormed t)
    (hp : parentOf t n = some p) (h : previousSibling t n = some prev) :
    parentOf t prev = some p ∧ prev ≠ n := by
  simp only [previousSibling, hp] at h
  split at h
  · simp at h
  · next _ u v hq =>
    have hsplit : childrenOf t p = u ++ n :: v := ListUtil.splitAt?_eq_some hq
    have hmem : prev ∈ u := List.mem_of_getLast? h
    have hmemc : prev ∈ childrenOf t p := by rw [hsplit]; exact List.mem_append_left _ hmem
    refine ⟨parentOf_of_mem_childrenOf hwf hmemc, ?_⟩
    intro he
    subst he
    have hnd : (childrenOf t p).Nodup := by
      obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
      rw [childrenOf_eq hpd]; exact hwf.children_nodup p pd hpd
    rw [hsplit] at hnd
    exact (List.nodup_append.mp hnd).2.2 prev hmem prev (List.mem_cons_self ..) rfl

/-! ## adjust a node pointer の性質 -/

theorem exists_get?_of_kindPreserving {t t' : Tree} {m : NodeId} {d : NodeData}
    (hk : KindPreserving t t') (h : t.get? m = some d) : ∃ d', t'.get? m = some d' := by
  have hm := hk m
  rw [h] at hm
  cases hq : t'.get? m with
  | none => rw [hq] at hm; simp at hm
  | some d' => exact ⟨d', rfl⟩

theorem exists_of_inclusiveAncestor {t : Tree} {r x : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) (h : InclusiveAncestor t r x) : ∃ d, t.get? x = some d := by
  rcases h with rfl | ha
  · exact ⟨rd, hr⟩
  · obtain ⟨q, hq⟩ := ha.parent_isSome
    obtain ⟨d, hd, _⟩ := parentOf_eq_some hq
    exact ⟨d, hd⟩

theorem exists_root_of_validIterator {t : Tree} {it : IteratorState} (hwf : WellFormed t)
    (hv : ValidIterator t it) : ∃ rd, t.get? it.root = some rd := by
  obtain ⟨⟨d, hd⟩, hincl⟩ := hv
  rcases hincl with he | ha
  · exact ⟨d, by rw [he]; exact hd⟩
  · exact exists_data_of_parentOf hwf (Ancestor.exists_child ha).choose_spec.1

/-- 削除する node が root の inclusive ancestor でないなら、root は削除する node の ancestor である。 -/
theorem ancestor_root_of_not_above {t : Tree} {root tbr node : NodeId} (hwf : WellFormed t)
    (hroot : isInclusiveAncestorOf t tbr root = false)
    (htbr : isInclusiveAncestorOf t tbr node = true)
    (hnode : InclusiveAncestor t root node) : Ancestor t root tbr := by
  have h1 := (isInclusiveAncestorOf_iff hwf tbr node).mp htbr
  rcases inclusive_ancestor_linear hnode h1 with h | h
  · rcases h with he | ha
    · exfalso
      rw [(isInclusiveAncestorOf_iff hwf tbr root).mpr (Or.inl he.symm)] at hroot
      simp at hroot
    · exact ha
  · exfalso
    rw [(isInclusiveAncestorOf_iff hwf tbr root).mpr h] at hroot
    simp at hroot

theorem inclusiveAncestor_lastD_preorder {t : Tree} {prev : NodeId} {d : NodeData}
    (hwf : WellFormed t) (hprev : t.get? prev = some d) :
    InclusiveAncestor t prev (ListUtil.lastD (preorder t prev) prev) := by
  rcases ListUtil.lastD_mem_or (preorder t prev) prev with hm | he
  · exact (mem_preorder_iff hwf hprev _).mp hm
  · rw [he]; exact Or.inl rfl

/--
`adjust a node pointer` の結果は、削除される部分木の外にあり、root の inclusive descendant である。

step 1 の二つ目の条件（削除する node が root の inclusive ancestor）に当たる場合は
pointer をそのまま返すので、ここでは root が生き残る場合を扱う。
-/
theorem adjustNodePointer_spec {t : Tree} {root tbr p node : NodeId} {before : Bool}
    (hwf : WellFormed t) (hp : parentOf t tbr = some p)
    (hroot : isInclusiveAncestorOf t tbr root = false)
    (hnode : InclusiveAncestor t root node) :
    isInclusiveAncestorOf t tbr (adjustNodePointer t root tbr node before).1 = false ∧
      InclusiveAncestor t root (adjustNodePointer t root tbr node before).1 := by
  unfold adjustNodePointer
  by_cases hA : isInclusiveAncestorOf t tbr node = true
  · rw [if_neg (by simp [hA]), if_neg (by simp [hroot])]
    -- root は tbr の ancestor
    have hrt : Ancestor t root tbr := ancestor_root_of_not_above hwf hroot hA hnode
    have hrp : InclusiveAncestor t root p := inclusiveAncestor_of_ancestor_parent hrt hp
    split
    · next next hnext =>
      -- step 2：find? の述語がそのまま結論になる
      have hfind : isInclusiveAncestorOf t root next = true ∧
          isInclusiveAncestorOf t tbr next = false := by
        revert hnext
        split
        · intro hnext
          unfold firstFollowingOutside at hnext
          split at hnext
          · simp at hnext
          · next q hq =>
            have hfs := List.find?_some hnext
            simp only [Bool.and_eq_true] at hfs
            exact ⟨hfs.1, by simpa using hfs.2⟩
        · intro hnext; simp at hnext
      exact ⟨hfind.2, (isInclusiveAncestorOf_iff hwf root next).mp hfind.1⟩
    · next hnone =>
      split
      · next hps =>
        rw [hp]
        exact ⟨not_inclusiveAncestor_parent hwf hp, hrp⟩
      · next prev hps =>
        obtain ⟨hprevp, hne⟩ := parentOf_previousSibling hwf hp hps
        obtain ⟨pd, hpd, _⟩ := parentOf_eq_some hprevp
        have hlast := inclusiveAncestor_lastD_preorder hwf hpd
        refine ⟨not_inclusiveAncestor_prevSubtree hwf hp hprevp hne hlast, ?_⟩
        exact (InclusiveAncestor.trans_inclusive hrp (Or.inr (Ancestor.step hprevp))
          ).trans_inclusive hlast
  · rw [if_pos (by simpa using hA)]
    exact ⟨by simpa using hA, hnode⟩

/-! ## remove と iterator -/

theorem remove_iterators {s s' : DOMState} {n p : NodeId} (hp : parentOf s.tree n = some p)
    (h : remove s n = .ok s') :
    s'.iterators = s.iterators.map fun it =>
      if ownerDocumentOf s.tree it.root == ownerDocumentOf s.tree n then
        iteratorPreRemoveOne s.tree n it
      else it := by
  simp only [remove, hp] at h
  unfold detachWithLiveAdjust at h
  obtain ⟨_, hs⟩ := DOMState.mapTree_eq_ok h
  rw [hs]
  show (iteratorPreRemove (liveRangePreRemove s n) n).iterators = _
  unfold iteratorPreRemove
  simp

/-- 対象になった iterator は、`remove` の後も valid のままである。 -/
theorem iteratorPreRemoveOne_valid {t t' : Tree} {n p : NodeId} {it : IteratorState}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (hd : detach t n = .ok t')
    (hv : ValidIterator t it) : ValidIterator t' (iteratorPreRemoveOne t n it) := by
  obtain ⟨rd, hrd⟩ := exists_root_of_validIterator hwf hv
  by_cases hroot : isInclusiveAncestorOf t n it.root = true
  · -- root ごと外れる場合。仕様は pointer を触らない。
    have hres : iteratorPreRemoveOne t n it = it := by
      unfold iteratorPreRemoveOne adjustNodePointer
      by_cases hA : isInclusiveAncestorOf t n it.reference = true
      · simp [hA, hroot]
      · simp [hA]
    rw [hres]
    refine ⟨exists_get?_of_kindPreserving (kindPreserving_detach hd) hv.1.choose_spec, ?_⟩
    refine inclusiveAncestor_detach_of_not_below hd hv.2 ?_
    rintro ⟨_, hrn⟩
    rcases (isInclusiveAncestorOf_iff hwf n it.root).mp hroot with he | ha
    · exact hwf.acyclic n (by rw [← he] at hrn; exact hrn)
    · exact hwf.acyclic n (ha.trans_ancestor hrn)
  · have hroot' : isInclusiveAncestorOf t n it.root = false := by simpa using hroot
    obtain ⟨hout, hin⟩ := adjustNodePointer_spec (before := it.pointerBeforeReference)
      hwf hp hroot' hv.2
    have hrefeq : (iteratorPreRemoveOne t n it).reference =
        (adjustNodePointer t it.root n it.reference it.pointerBeforeReference).1 := rfl
    obtain ⟨dr, hdr⟩ := exists_of_inclusiveAncestor hrd hin
    refine ⟨?_, ?_⟩
    · rw [hrefeq]
      exact exists_get?_of_kindPreserving (kindPreserving_detach hd) hdr
    · show InclusiveAncestor t' it.root (iteratorPreRemoveOne t n it).reference
      rw [hrefeq]
      refine inclusiveAncestor_detach_of_not_below hd hin ?_
      rintro ⟨hincl, _⟩
      rw [(isInclusiveAncestorOf_iff hwf n _).mpr hincl] at hout
      simp at hout

/-! ## 状態のレベルの定理 -/

/--
別の node document に属する iterator は、仕様どおり触られない。
その reference が削除される部分木を指していないことは、
node document が木の構造と整合していれば成り立つが、
`WellFormed` はそれを要求していないので前提として置く。
-/
def OtherDocumentIteratorsOutside (s : DOMState) (n : NodeId) : Prop :=
  ∀ it ∈ s.iterators,
    ownerDocumentOf s.tree it.root ≠ ownerDocumentOf s.tree n →
      isInclusiveAncestorOf s.tree n it.reference = false

/-- PLAN §9.2。`remove` は iterator の reference を木の中かつ root の inclusive descendant に保つ。 -/
theorem remove_preserves_iterators_valid {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hv : IteratorsValid s) (hother : OtherDocumentIteratorsOutside s n)
    (h : remove s n = .ok s') : IteratorsValid s' := by
  have hd := (remove_ok h).2
  intro it hit
  rw [remove_iterators hp h] at hit
  obtain ⟨it₀, hit₀, hie⟩ := List.mem_map.mp hit
  rw [← hie]
  by_cases hsame : (ownerDocumentOf s.tree it₀.root == ownerDocumentOf s.tree n) = true
  · rw [if_pos hsame]
    exact iteratorPreRemoveOne_valid hwf hp hd (hv it₀ hit₀)
  · rw [if_neg hsame]
    have hout := hother it₀ hit₀ (by simpa using hsame)
    obtain ⟨hex, hincl⟩ := hv it₀ hit₀
    refine ⟨exists_get?_of_kindPreserving (kindPreserving_detach hd) hex.choose_spec, ?_⟩
    refine inclusiveAncestor_detach_of_not_below hd hincl ?_
    rintro ⟨hi, _⟩
    rw [(isInclusiveAncestorOf_iff hwf n _).mpr hi] at hout
    simp at hout

/--
PLAN §9.2 / `memo.md` §8。削除された node の inclusive descendant は、
操作後どの iterator の reference にもならない。

root ごと外れる iterator（削除する node が root の inclusive ancestor）は
仕様が意図的に触らないので、除いてある。
-/
theorem remove_iterators_leave_subtree {s s' : DOMState} {n p : NodeId}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p)
    (hv : IteratorsValid s) (hother : OtherDocumentIteratorsOutside s n)
    (h : remove s n = .ok s') :
    ∀ it ∈ s'.iterators,
      isInclusiveAncestorOf s.tree n it.root = false →
        isInclusiveAncestorOf s.tree n it.reference = false := by
  intro it hit hroot
  rw [remove_iterators hp h] at hit
  obtain ⟨it₀, hit₀, hie⟩ := List.mem_map.mp hit
  by_cases hsame : (ownerDocumentOf s.tree it₀.root == ownerDocumentOf s.tree n) = true
  · rw [← hie, if_pos hsame] at hroot ⊢
    exact (adjustNodePointer_spec (before := it₀.pointerBeforeReference) hwf hp hroot
      (hv it₀ hit₀).2).1
  · rw [← hie, if_neg hsame] at hroot ⊢
    exact hother it₀ hit₀ (by simpa using hsame)

/-- `move` も `remove` を経由するので、同じことが成り立つ。 -/
theorem move_iterators_leave_subtree {s s' : DOMState} {node newParent p : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree) (hp : parentOf s.tree node = some p)
    (hv : IteratorsValid s) (hother : OtherDocumentIteratorsOutside s node)
    (h : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      ∀ it ∈ s₁.iterators,
        isInclusiveAncestorOf s.tree node it.root = false →
          isInclusiveAncestorOf s.tree node it.reference = false := by
  obtain ⟨s₁, hr, _⟩ := move_eq_remove_insertAt h
  exact ⟨s₁, hr, remove_iterators_leave_subtree hwf hp hv hother hr⟩

end Dom
