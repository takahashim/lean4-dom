import Dom.Mutation.Create
import Dom.Properties.Tree

/-!
# node を作る効果と frame

作る algorithm はどれも「木に node を一つ足す」だけである。
効果も frame もその一つの形（`AddsNode`）で述べ、各 method はそれを満たすと言う。
-/

namespace Dom

/--
木が node を一つだけ増やしたこと。

`fresh` が無いと「もともと居た node を上書きした」場合を除けない。
-/
structure AddsNode (t t' : Tree) (n : NodeId) (d : NodeData) : Prop where
  /-- 作る前には無かった。 -/
  fresh : t.get? n = none
  /-- 作った後にはある。 -/
  created : t'.get? n = some d
  /-- ほかの node は何も変わらない。 -/
  others : ∀ m, m ≠ n → t'.get? m = t.get? m

namespace AddsNode

variable {t t' : Tree} {n : NodeId} {d : NodeData}

/-- 木にあった node は、作った id とは違う。 -/
theorem ne_of_mem (h : AddsNode t t' n d) {m : NodeId} {md : NodeData}
    (hm : t.get? m = some md) : m ≠ n := by
  intro he
  rw [he, h.fresh] at hm
  simp at hm

theorem parentOf_self (h : AddsNode t t' n d) (hp : d.parent = none) :
    parentOf t' n = none := by
  simp [parentOf_eq, h.created, hp]

theorem childrenOf_self (h : AddsNode t t' n d) (hc : d.children = []) :
    childrenOf t' n = [] := by
  rw [childrenOf_eq h.created, hc]

theorem parentOf_other (h : AddsNode t t' n d) {m : NodeId} (hm : m ≠ n) :
    parentOf t' m = parentOf t m := by
  simp [parentOf_eq, h.others m hm]

theorem childrenOf_other (h : AddsNode t t' n d) {m : NodeId} (hm : m ≠ n) :
    childrenOf t' m = childrenOf t m := by
  exact childrenOf_congr (h.others m hm)

theorem ownerDocumentOf_other (h : AddsNode t t' n d) {m : NodeId} (hm : m ≠ n) :
    ownerDocumentOf t' m = ownerDocumentOf t m := by
  simp [ownerDocumentOf_eq, h.others m hm]

/-- **作った node は誰の子でもない。** -/
theorem not_child (h : AddsNode t t' n d) (hwf : WellFormed t) (hc : d.children = [])
    (m : NodeId) : n ∉ childrenOf t' m := by
  intro hmem
  by_cases hmn : m = n
  · rw [hmn, h.childrenOf_self hc] at hmem
    simp at hmem
  · rw [h.childrenOf_other hmn] at hmem
    obtain ⟨nd, hnd, -⟩ := parentOf_eq_some (parentOf_of_mem_childrenOf hwf hmem)
    rw [h.fresh] at hnd
    simp at hnd

/-- 新しい辺は無いので、ancestor 関係は変わらない。 -/
theorem ancestor_of (h : AddsNode t t' n d) (hwf : WellFormed t) (hc : d.children = [])
    (hp : d.parent = none) {a m : NodeId} (ha : Ancestor t' a m) : Ancestor t a m := by
  have key : ∀ x y : NodeId, parentOf t' x = some y → parentOf t x = some y := by
    intro x y hx
    by_cases hxn : x = n
    · rw [hxn, h.parentOf_self hp] at hx; simp at hx
    · rw [← h.parentOf_other hxn]; exact hx
  induction ha with
  | step hpx => exact Ancestor.step (key _ _ hpx)
  | trans hpx _ ih => exact Ancestor.trans (key _ _ hpx) ih

theorem ancestor_to (h : AddsNode t t' n d) {a m : NodeId} (ha : Ancestor t a m) :
    Ancestor t' a m := by
  have key : ∀ x y : NodeId, parentOf t x = some y → parentOf t' x = some y := by
    intro x y hx
    obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hx
    rw [h.parentOf_other (h.ne_of_mem hxd)]
    exact hx
  induction ha with
  | step hpx => exact Ancestor.step (key _ _ hpx)
  | trans hpx _ ih => exact Ancestor.trans (key _ _ hpx) ih

end AddsNode

/-! ## 各 method が `AddsNode` を満たす -/

theorem withFresh_addsNode (s : DOMState) (d : NodeData) :
    AddsNode s.tree (withFresh s d).2.tree (withFresh s d).1 d where
  fresh := freshId_get?_eq_none s.tree
  created := by simp [withFresh]
  others := fun m hm => by
    have hm' : m ≠ freshId s.tree := hm
    simpa [withFresh] using get?_insertNode_ne s.tree hm' d

/-- `withFresh` は木しか触らない。 -/
@[simp] theorem withFresh_ranges (s : DOMState) (d : NodeData) :
    (withFresh s d).2.ranges = s.ranges := rfl

@[simp] theorem withFresh_iterators (s : DOMState) (d : NodeData) :
    (withFresh s d).2.iterators = s.iterators := rfl

@[simp] theorem withFresh_observers (s : DOMState) (d : NodeData) :
    (withFresh s d).2.observers = s.observers := rfl

@[simp] theorem withFresh_registrations (s : DOMState) (d : NodeData) :
    (withFresh s d).2.registrations = s.registrations := rfl

end Dom
