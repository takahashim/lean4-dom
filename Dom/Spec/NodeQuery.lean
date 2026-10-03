import Dom.Properties.NodeQuery

/-!
# `contains`・`getRootNode`・`compareDocumentPosition` の関係仕様

`Dom/Query/NodeQuery.lean` の三つの method が返すものを、実行関数の道具（fuel 付きの
`root`・`isAncestorOf`・`precedes`）を使わずに §4.2 の語彙で言い、実行関数がそれに
一致することを示す。

| 関係 | 本文 |
| --- | --- |
| `IsRoot t r n` | §4.2 の root。`n` の inclusive ancestor で parent を持たないもの |
| `SameTree t x y` | 二つの node が同じ root を持つ |
| `PrecedesStruct t x y` | §4.2 の tree order で `x` が `y` に先行する（`Dom/Properties/Tree.lean`） |
| `DocumentPositionSpec` | §4.4 `compareDocumentPosition` の step 6-10 |

`PrecedesStruct` は「ancestor であるか、共通の parent の下で index の小さい子の側にいる」という
構造で書いた tree order で、preorder の列を使わない。

step 6 の「同じ木にない」場合は PRECEDING と FOLLOWING のどちらでもよい（一貫していれば）ので、
`DocumentPositionSpec` はそこで二つの値を許す。したがって `compareDocumentPosition` の
値が関係で **一意に決まる** のは同じ木にある場合だけで、`compareDocumentPosition_eq_iff` は
その場合の `↔` である。一貫性は `Dom/Properties/NodeQuery.lean` の
`compareDocumentPosition_disconnected_consistent` が押さえている。
-/

namespace Dom.Spec

open Dom

variable {t : Tree}

/-- DOM §4.2 の root。`r` は `n` の inclusive ancestor であり、parent を持たない。 -/
def IsRoot (t : Tree) (r n : NodeId) : Prop :=
  InclusiveAncestor t r n ∧ parentOf t r = none

/-- 二つの node が同じ root を持つ（同じ木にある）。 -/
def SameTree (t : Tree) (x y : NodeId) : Prop :=
  ∃ r, IsRoot t r x ∧ IsRoot t r y

/-- DOM §4.4 `compareDocumentPosition(other)` の戻り値の条件（attribute の枝を除く）。 -/
def DocumentPositionSpec (t : Tree) (node other : NodeId) (v : Nat) : Prop :=
  -- step 2
  (node = other ∧ v = 0) ∨
  -- step 6
  (node ≠ other ∧ ¬ SameTree t node other ∧
    (v = DocumentPosition.disconnected + DocumentPosition.implementationSpecific +
        DocumentPosition.preceding ∨
      v = DocumentPosition.disconnected + DocumentPosition.implementationSpecific +
        DocumentPosition.following)) ∨
  -- step 7
  (Ancestor t other node ∧ v = DocumentPosition.contains + DocumentPosition.preceding) ∨
  -- step 8
  (Ancestor t node other ∧ v = DocumentPosition.containedBy + DocumentPosition.following) ∨
  -- step 9-10
  (node ≠ other ∧ SameTree t node other ∧ ¬ Ancestor t other node ∧ ¬ Ancestor t node other ∧
    ((PrecedesStruct t other node ∧ v = DocumentPosition.preceding) ∨
      (¬ PrecedesStruct t other node ∧ v = DocumentPosition.following)))

/-! ## root -/

theorem isRoot_root (hwf : WellFormed t) (n : NodeId) : IsRoot t (root t n) n :=
  ⟨root_inclusive_ancestor t n, root_parent_eq_none hwf n⟩

/-- **`getRootNode()` は §4.2 の root をちょうど返す。** -/
theorem getRootNode_eq_iff (hwf : WellFormed t) (n r : NodeId) :
    getRootNode t n = r ↔ IsRoot t r n := by
  rw [getRootNode_eq]
  constructor
  · rintro rfl; exact isRoot_root hwf n
  · rintro ⟨ha, hp⟩; exact root_unique hwf ha hp

/-- 実行側の `root` の比較は、同じ木にあることちょうどである。 -/
theorem root_eq_root_iff (hwf : WellFormed t) (x y : NodeId) :
    root t x = root t y ↔ SameTree t x y := by
  constructor
  · intro h
    exact ⟨root t x, isRoot_root hwf x, by rw [h]; exact isRoot_root hwf y⟩
  · rintro ⟨r, hx, hy⟩
    rw [root_unique hwf hx.1 hx.2, root_unique hwf hy.1 hy.2]

theorem SameTree.of_ancestor (hwf : WellFormed t) {a n : NodeId} (h : Ancestor t a n) :
    SameTree t n a :=
  (root_eq_root_iff hwf n a).mp (root_eq_of_ancestor hwf h)

theorem SameTree.symm {x y : NodeId} (h : SameTree t x y) : SameTree t y x := by
  obtain ⟨r, hx, hy⟩ := h
  exact ⟨r, hy, hx⟩

/-! ## contains -/

/-- **`contains(other)` は、`other` が inclusive descendant であることちょうどである。** -/
theorem nodeContains_eq_true_iff (hwf : WellFormed t) (node other : NodeId) :
    nodeContains t node other = true ↔ InclusiveDescendant t other node :=
  nodeContains_iff hwf node other

/-! ## compareDocumentPosition -/

/-- **`compareDocumentPosition` の値は §4.4 の条件を満たす。** -/
theorem compareDocumentPosition_spec (hwf : WellFormed t) (node other : NodeId) :
    DocumentPositionSpec t node other (compareDocumentPosition t node other) := by
  unfold compareDocumentPosition DocumentPositionSpec
  by_cases he : node = other
  · rw [if_pos (by simp [he])]
    exact Or.inl ⟨he, rfl⟩
  rw [if_neg (by simp [he])]
  by_cases hr : root t other = root t node
  · have hsame : SameTree t node other := ((root_eq_root_iff hwf other node).mp hr).symm
    rw [if_neg (by simp [hr])]
    cases h1 : isAncestorOf t other node with
    | true =>
      rw [if_pos rfl]
      exact Or.inr (Or.inr (Or.inl ⟨(isAncestorOf_iff hwf _ _).mp h1, rfl⟩))
    | false =>
      have h1' : ¬ Ancestor t other node := fun h => by
        rw [(isAncestorOf_iff hwf _ _).mpr h] at h1; simp at h1
      rw [if_neg (by simp)]
      cases h2 : isAncestorOf t node other with
      | true =>
        rw [if_pos rfl]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(isAncestorOf_iff hwf _ _).mp h2, rfl⟩)))
      | false =>
        have h2' : ¬ Ancestor t node other := fun h => by
          rw [(isAncestorOf_iff hwf _ _).mpr h] at h2; simp at h2
        rw [if_neg (by simp)]
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨he, hsame, h1', h2', ?_⟩)))
        -- `other` は木にある。無ければ自分自身が root で、`node` の ancestor になってしまう。
        obtain ⟨od, hod⟩ : ∃ od, t.get? other = some od := by
          cases hod : t.get? other with
          | some od => exact ⟨od, rfl⟩
          | none =>
            exfalso
            have hro : root t other = other :=
              root_unique hwf (InclusiveAncestor.refl t other)
                (parentOf_eq_none_of_get?_eq_none hod)
            rcases root_inclusive_ancestor t node with h | h
            · exact he (h.symm.trans (hr.symm.trans hro))
            · rw [← hr, hro] at h; exact h1' h
        have hiff := precedes_iff_struct hwf hod hr (fun h => he h.symm)
        cases hp : precedes t other node with
        | true => exact Or.inl ⟨hiff.mp hp, by rw [if_pos rfl]⟩
        | false =>
          exact Or.inr ⟨fun h => by rw [hiff.mpr h] at hp; simp at hp, by rw [if_neg (by simp)]⟩
  · have hns : ¬ SameTree t node other := fun h =>
      hr ((root_eq_root_iff hwf other node).mpr h.symm)
    rw [if_pos (by simp [hr])]
    refine Or.inr (Or.inl ⟨he, hns, ?_⟩)
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- 同じ木にある（または同じ node の）場合、§4.4 の条件は値をただ一つに決める。 -/
theorem documentPositionSpec_unique (hwf : WellFormed t) {node other : NodeId} {v w : Nat}
    (hsame : SameTree t node other) (hv : DocumentPositionSpec t node other v)
    (hw : DocumentPositionSpec t node other w) : v = w := by
  have hasym : ¬ (Ancestor t other node ∧ Ancestor t node other) := fun ⟨h1, h2⟩ =>
    hwf.acyclic _ (h1.trans_ancestor h2)
  have hirr : ∀ {x}, ¬ Ancestor t x x := fun h => hwf.acyclic _ h
  unfold DocumentPositionSpec at hv hw
  rcases hv with ⟨he, rfl⟩ | ⟨-, hns, -⟩ | ⟨ha, rfl⟩ | ⟨ha, rfl⟩ | ⟨hne, -, hn1, hn2, hv⟩
  · rcases hw with ⟨-, rfl⟩ | ⟨hne, -⟩ | ⟨ha, -⟩ | ⟨ha, -⟩ | ⟨hne, -⟩
    · rfl
    · exact absurd he hne
    · subst he; exact absurd ha hirr
    · subst he; exact absurd ha hirr
    · exact absurd he hne
  · exact absurd hsame hns
  · rcases hw with ⟨he, -⟩ | ⟨-, hns, -⟩ | ⟨-, rfl⟩ | ⟨hb, -⟩ | ⟨-, -, hn1, -⟩
    · subst he; exact absurd ha hirr
    · exact absurd hsame hns
    · rfl
    · exact absurd ⟨ha, hb⟩ hasym
    · exact absurd ha hn1
  · rcases hw with ⟨he, -⟩ | ⟨-, hns, -⟩ | ⟨hb, -⟩ | ⟨-, rfl⟩ | ⟨-, -, -, hn2, -⟩
    · subst he; exact absurd ha hirr
    · exact absurd hsame hns
    · exact absurd ⟨hb, ha⟩ hasym
    · rfl
    · exact absurd ha hn2
  · rcases hw with ⟨he, -⟩ | ⟨-, hns, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨-, -, -, -, hw⟩
    · exact absurd he hne
    · exact absurd hsame hns
    · exact absurd hb hn1
    · exact absurd hb hn2
    · rcases hv with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ <;> rcases hw with ⟨hq, rfl⟩ | ⟨hq, rfl⟩
      · rfl
      · exact absurd hp hq
      · exact absurd hq hp
      · rfl

/--
**同じ木にある二つの node について、`compareDocumentPosition` の値は §4.4 の条件ちょうどである。**

同じ node は同じ木にあるので、step 2 もここに含まれる。
-/
theorem compareDocumentPosition_eq_iff (hwf : WellFormed t) {node other : NodeId}
    (hsame : SameTree t node other) (v : Nat) :
    compareDocumentPosition t node other = v ↔ DocumentPositionSpec t node other v := by
  constructor
  · rintro rfl; exact compareDocumentPosition_spec hwf node other
  · intro hv
    exact documentPositionSpec_unique hwf hsame (compareDocumentPosition_spec hwf node other) hv

/-- 同じ木にない二つの node では、DISCONNECTED と IMPLEMENTATION_SPECIFIC が立つ。 -/
theorem compareDocumentPosition_of_not_sameTree (hwf : WellFormed t) {node other : NodeId}
    (hns : ¬ SameTree t node other) :
    compareDocumentPosition t node other = 35 ∨ compareDocumentPosition t node other = 37 := by
  rcases compareDocumentPosition_spec hwf node other with
    ⟨rfl, -⟩ | ⟨-, -, h⟩ | ⟨ha, -⟩ | ⟨ha, -⟩ | ⟨-, hs, -⟩
  · exact absurd ⟨root t node, isRoot_root hwf node, isRoot_root hwf node⟩ hns
  · exact h
  · exact absurd (SameTree.of_ancestor hwf ha) hns
  · exact absurd (SameTree.of_ancestor hwf ha).symm hns
  · exact absurd hs hns

end Dom.Spec
