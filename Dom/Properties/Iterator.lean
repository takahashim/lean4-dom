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

/-! ## detach と ancestor 関係 -/

theorem parentOf_detach {t t' : Tree} {n : NodeId} (hd : detach t n = .ok t') (m : NodeId) :
    parentOf t' m = if m = n then none else parentOf t m := by
  rcases detach_ok_cases hd with ⟨d, hdd, hdp, rfl⟩ | ⟨d, p, pd, hdd, hdp, hpd, rfl⟩
  · by_cases hm : m = n
    · rw [if_pos hm, hm]; simp [parentOf, hdd, hdp]
    · rw [if_neg hm]
  · exact parentOf_detachFrom hpd m

/--
`detach` が外す辺が経路上に無ければ、ancestor 関係は残る。

`n` の親への辺だけが消えるので、`x` から `a` へ登る経路がその辺を通らなければよい。
経路がその辺を通るのは「`n` が `x` の inclusive ancestor」かつ「`a` が `n` の ancestor」のときである。
-/
theorem ancestor_detach_of_not_below {t t' : Tree} {n a : NodeId}
    (hd : detach t n = .ok t') {x : NodeId} (h : Ancestor t a x) :
    ¬ (InclusiveAncestor t n x ∧ Ancestor t a n) → Ancestor t' a x := by
  induction h with
  | @step m hp =>
    intro hnot
    have hmn : m ≠ n := by
      intro he
      exact hnot ⟨Or.inl he.symm, by rw [← he]; exact Ancestor.step hp⟩
    refine Ancestor.step ?_
    rw [parentOf_detach hd, if_neg hmn]
    exact hp
  | @trans m b hp hprev ih =>
    -- hp : parentOf t b = some m（b が下、m がその parent）
    intro hnot
    have hbn : b ≠ n := by
      intro he
      exact hnot ⟨Or.inl he.symm, by rw [← he]; exact Ancestor.trans hp hprev⟩
    refine Ancestor.trans (by rw [parentOf_detach hd, if_neg hbn]; exact hp) (ih ?_)
    rintro ⟨hnm, han⟩
    refine hnot ⟨?_, han⟩
    rcases hnm with he | ha
    · exact Or.inr (by rw [← he] at hp; exact Ancestor.step hp)
    · exact Or.inr (ha.trans_ancestor (Ancestor.step hp))

theorem inclusiveAncestor_detach_of_not_below {t t' : Tree} {n r x : NodeId}
    (hd : detach t n = .ok t') (h : InclusiveAncestor t r x)
    (hnot : ¬ (InclusiveAncestor t n x ∧ Ancestor t r n)) : InclusiveAncestor t' r x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (ancestor_detach_of_not_below hd h hnot)

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

theorem inclusiveAncestor_of_ancestor_parent {t : Tree} {r n p : NodeId}
    (h : Ancestor t r n) (hp : parentOf t n = some p) : InclusiveAncestor t r p := by
  obtain ⟨q, hq, hcase⟩ := h.cases_parent
  rw [hp] at hq
  cases hq
  rcases hcase with rfl | ha
  · exact Or.inl rfl
  · exact Or.inr ha

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
