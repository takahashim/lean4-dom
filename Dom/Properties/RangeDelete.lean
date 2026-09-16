import Dom.Range.Api
import Dom.Properties.Range

/-!
# `Range.deleteContents()` の契約

§5.5 の `deleteContents` は step 4 で「range に含まれる node のうち、親が含まれない
ものだけ」を集めて順に外す。この形が `removeEach` にとって安全であること
（外した node の子孫をもう一度外そうとしない）は仕様の意図だが、
差分テストからは出てこないのでここで示す。
-/

namespace Dom

variable {t : Tree} {r : RangeState}

/-! ## step 4 の `nodesToRemove` -/

theorem mem_nodesToRemove_iff (n : NodeId) :
    n ∈ nodesToRemove t r ↔
      n ∈ treeOrder t r.start.node ∧ containedInRange t r n = true ∧
        ∀ p, parentOf t n = some p → containedInRange t r p = false := by
  unfold nodesToRemove
  rw [List.mem_filter]
  constructor
  · rintro ⟨hmem, hcond⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
    refine ⟨hmem, hcond.1, fun p hp => ?_⟩
    have := hcond.2
    rw [hp] at this
    exact this
  · rintro ⟨hmem, hc, hp⟩
    refine ⟨hmem, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hc, ?_⟩
    cases hq : parentOf t n with
    | none => rfl
    | some p => exact hp p hq

/-- 外す node の列に重複は無い。 -/
theorem nodesToRemove_nodup (hwf : WellFormed t) : (nodesToRemove t r).Nodup := by
  unfold nodesToRemove
  exact (treeOrder_nodup hwf r.start.node).filter _

/--
**外す node の親は、同じ列には入っていない。**

step 4 の「親も含まれるものを落とす」がこれである。`removeEach` は列を順に
`remove` するので、親と子が両方入っていると、親を外した後に子の `remove` が
`notFoundError` になる。
-/
theorem parentOf_not_mem_nodesToRemove {n p : NodeId} (hn : n ∈ nodesToRemove t r)
    (hp : parentOf t n = some p) : p ∉ nodesToRemove t r := by
  intro hpm
  have h1 := ((mem_nodesToRemove_iff n).mp hn).2.2 p hp
  have h2 := ((mem_nodesToRemove_iff p).mp hpm).2.1
  rw [h1] at h2
  simp at h2

/-- 含まれる node は range の start と同じ木にある。 -/
theorem root_eq_of_containedInRange {n : NodeId} (h : containedInRange t r n = true) :
    root t n = root t r.start.node := by
  unfold containedInRange at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-! ## step 5-6 の新しい boundary point -/

/-- start が end の inclusive ancestor なら、その場に潰れる（step 5）。 -/
theorem deleteContentsNewBP_of_inclusiveAncestor
    (h : isInclusiveAncestorOf t r.start.node r.«end».node = true) :
    deleteContentsNewBP t r = r.start := by
  unfold deleteContentsNewBP
  rw [if_pos h]

/-! ## step 1 -/

/-- **潰れている range に対する `deleteContents()` は何もしない（step 1）。** -/
theorem rangeDeleteContents_of_collapsed {s : DOMState} {i : Nat} {r : RangeState}
    (hr : s.ranges[i]? = some r) (hc : r.start = r.«end») :
    rangeDeleteContents s i = .ok s := by
  unfold rangeDeleteContents
  rw [hr]
  show (if r.start == r.«end» then Except.ok s else _) = _
  rw [if_pos (by simp [hc])]

end Dom
