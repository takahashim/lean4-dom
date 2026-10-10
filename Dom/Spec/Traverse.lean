import Dom.Spec.TreeOrder
import Dom.Traversal.NodeIterator

/-!
# NodeIterator の traverse の関係仕様（§6.1）

本文の traverse は candidate reference を進めながら filter を呼ぶ loop だが、filter が null なら
filter の結果は whatToShow だけで決まる（`Accepts`）。そのとき loop が返すのは、

* type が next なら、「reference に後続する node（pointer before なら reference 自身も）」のうち、
  accept されるもので tree order で最初のもの、
* type が previous なら、「reference に先行する node（pointer before でなければ reference 自身も）」のうち、
  accept されるもので tree order で最後のもの

である。候補はどれも iterator collection（root の inclusive descendant）に限る。関係はこの形で書き、
実行関数（iterator collection の列を reference で分けて `find?` する）がそれを満たすことを示す。
-/

namespace Dom.Spec

open Dom.ListUtil

/-- traverse（next）の候補：§6.1 step 3.1。 -/
def NextCandidate (t : Tree) (it : IteratorState) (x : NodeId) : Prop :=
  InclusiveDescendant t x it.root ∧
    ((it.pointerBeforeReference = true ∧ x = it.reference) ∨ PrecedesStruct t it.reference x)

/-- traverse（previous）の候補：§6.1 step 3.2。 -/
def PreviousCandidate (t : Tree) (it : IteratorState) (x : NodeId) : Prop :=
  InclusiveDescendant t x it.root ∧
    ((it.pointerBeforeReference = false ∧ x = it.reference) ∨ PrecedesStruct t x it.reference)

/-- `P` を満たす node のうち tree order で最後のもの。 -/
def LastIn (t : Tree) (P : NodeId → Prop) (n : NodeId) : Prop :=
  P n ∧ ∀ m, P m → ¬ PrecedesStruct t n m

/-- §6.1 `nextNode()`：traverse の結果と、reference の更新（step 3.5.1）。 -/
def NextNodeResult (t : Tree) (it : IteratorState) (r : Option (NodeId × IteratorState)) : Prop :=
  (∃ n, r = some (n, { it with reference := n, pointerBeforeReference := false }) ∧
      FirstIn t (fun x => NextCandidate t it x ∧ Accepts t it.whatToShow x) n) ∨
  (r = none ∧ ∀ m, NextCandidate t it m → ¬ Accepts t it.whatToShow m)

/-- §6.1 `previousNode()`。 -/
def PreviousNodeResult (t : Tree) (it : IteratorState) (r : Option (NodeId × IteratorState)) :
    Prop :=
  (∃ n, r = some (n, { it with reference := n, pointerBeforeReference := true }) ∧
      LastIn t (fun x => PreviousCandidate t it x ∧ Accepts t it.whatToShow x) n) ∨
  (r = none ∧ ∀ m, PreviousCandidate t it m → ¬ Accepts t it.whatToShow m)

/-! ## 実行関数との一致 -/

theorem showsNode_iff (t : Tree) (w : Nat) (n : NodeId) :
    showsNode t w n = true ↔ Accepts t w n := by
  unfold showsNode Accepts kindOf
  cases h : t.get? n <;> simp

theorem nextNode_result_sound {t : Tree} (hwf : WellFormed t) {it : IteratorState} {rd : NodeData}
    (hroot : t.get? it.root = some rd) (hit : ValidIterator t it) :
    NextNodeResult t it (nextNode t it) := by
  have hl := treeOrderList_preorder hwf hroot
  have href : it.reference ∈ preorder t it.root := (hl.1 _).mpr hit.2
  obtain ⟨A, B, hsp⟩ := exists_splitAt?_of_mem href
  have hsplit := splitAt?_eq_some hsp
  -- 候補の列
  have hBmem : ∀ x ∈ B, InclusiveDescendant t x it.root := fun x hx =>
    (hl.1 x).mp (by rw [hsplit]; simp [hx])
  have hBsorted : B.Pairwise (PrecedesStruct t) := by
    have hp := hl.2
    rw [hsplit, List.pairwise_append] at hp
    exact (List.pairwise_cons.mp hp.2.1).2
  have hrefB : ∀ x ∈ B, PrecedesStruct t it.reference x := by
    have hp := hl.2
    rw [hsplit] at hp
    exact (pairwise_split hp).2
  -- 候補の列の要素が候補であること、候補が列にあること
  have hcand : ∀ x, x ∈ (if it.pointerBeforeReference then it.reference :: B else B) ↔
      NextCandidate t it x := by
    intro x
    unfold NextCandidate
    by_cases hpb : it.pointerBeforeReference = true
    · simp only [hpb, if_true, List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact ⟨hit.2, Or.inl ⟨by simp, rfl⟩⟩
        · exact ⟨hBmem x hx, Or.inr (hrefB x hx)⟩
      · rintro ⟨hxr, (⟨-, rfl⟩ | hprec)⟩
        · exact Or.inl rfl
        · exact Or.inr ((mem_right_of_split hwf hroot hl hsplit x).mpr ⟨(hl.1 x).mpr hxr, hprec⟩)
    · have hpb' : it.pointerBeforeReference = false := by simpa using hpb
      simp only [hpb', Bool.false_eq_true, if_false]
      constructor
      · intro hx
        exact ⟨hBmem x hx, Or.inr (hrefB x hx)⟩
      · rintro ⟨hxr, (⟨h, -⟩ | hprec)⟩
        · cases h
        · exact (mem_right_of_split hwf hroot hl hsplit x).mpr ⟨(hl.1 x).mpr hxr, hprec⟩
  have hcandmem : ∀ x ∈ (if it.pointerBeforeReference then it.reference :: B else B),
      InclusiveDescendant t x it.root := fun x hx => ((hcand x).mp hx).1
  have hcandsorted : (if it.pointerBeforeReference then it.reference :: B else B).Pairwise
      (PrecedesStruct t) := by
    by_cases hpb : it.pointerBeforeReference = true
    · simp only [hpb, if_true]
      exact List.Pairwise.cons hrefB hBsorted
    · have hpb' : it.pointerBeforeReference = false := by simpa using hpb
      simp only [hpb', Bool.false_eq_true, if_false]
      exact hBsorted
  unfold nextNode iteratorCollection
  rw [hsp]
  simp only
  cases hf : (if it.pointerBeforeReference then it.reference :: B else B).find?
      (showsNode t it.whatToShow) with
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    intro m hm hacc
    have := find?_none_of_sorted hf m ((hcand m).mpr hm)
    rw [(showsNode_iff t it.whatToShow m).mpr hacc] at this
    cases this
  | some n =>
    obtain ⟨hn, hpn, hfirst⟩ := find?_first_of_sorted hwf hroot hcandmem hcandsorted hf
    refine Or.inl ⟨n, rfl, ⟨(hcand n).mp hn, (showsNode_iff t it.whatToShow n).mp hpn⟩, ?_⟩
    rintro m ⟨hm, hacc⟩
    exact hfirst m ((hcand m).mpr hm) ((showsNode_iff t it.whatToShow m).mpr hacc)

theorem previousNode_result_sound {t : Tree} (hwf : WellFormed t) {it : IteratorState}
    {rd : NodeData} (hroot : t.get? it.root = some rd) (hit : ValidIterator t it) :
    PreviousNodeResult t it (previousNode t it) := by
  have hl := treeOrderList_preorder hwf hroot
  have href : it.reference ∈ preorder t it.root := (hl.1 _).mpr hit.2
  obtain ⟨A, B, hsp⟩ := exists_splitAt?_of_mem href
  have hsplit := splitAt?_eq_some hsp
  have hAmem : ∀ x ∈ A, InclusiveDescendant t x it.root := fun x hx =>
    (hl.1 x).mp (by rw [hsplit]; simp [hx])
  have hAsorted : A.Pairwise (PrecedesStruct t) := by
    have hp := hl.2
    rw [hsplit, List.pairwise_append] at hp
    exact hp.1
  have hAref : ∀ x ∈ A, PrecedesStruct t x it.reference := by
    have hp := hl.2
    rw [hsplit] at hp
    exact (pairwise_split hp).1
  have hcand : ∀ x, x ∈ (if it.pointerBeforeReference then A.reverse else it.reference :: A.reverse) ↔
      PreviousCandidate t it x := by
    intro x
    unfold PreviousCandidate
    by_cases hpb : it.pointerBeforeReference = true
    · simp only [hpb, if_true, List.mem_reverse]
      constructor
      · intro hx
        exact ⟨hAmem x hx, Or.inr (hAref x hx)⟩
      · rintro ⟨hxr, (⟨h, -⟩ | hprec)⟩
        · cases h
        · exact (mem_left_of_split hwf hroot hl hsplit x).mpr ⟨(hl.1 x).mpr hxr, hprec⟩
    · have hpb' : it.pointerBeforeReference = false := by simpa using hpb
      simp only [hpb', Bool.false_eq_true, if_false, List.mem_cons, List.mem_reverse]
      constructor
      · rintro (rfl | hx)
        · exact ⟨hit.2, Or.inl ⟨by simp, rfl⟩⟩
        · exact ⟨hAmem x hx, Or.inr (hAref x hx)⟩
      · rintro ⟨hxr, (⟨-, rfl⟩ | hprec)⟩
        · exact Or.inl rfl
        · exact Or.inr ((mem_left_of_split hwf hroot hl hsplit x).mpr ⟨(hl.1 x).mpr hxr, hprec⟩)
  have hcandmem : ∀ x ∈ (if it.pointerBeforeReference then A.reverse else it.reference :: A.reverse),
      InclusiveDescendant t x it.root := fun x hx => ((hcand x).mp hx).1
  have hcandsorted : (if it.pointerBeforeReference then A.reverse else it.reference :: A.reverse).Pairwise
      (fun a b => PrecedesStruct t b a) := by
    have hrev : A.reverse.Pairwise (fun a b => PrecedesStruct t b a) :=
      List.pairwise_reverse.mpr hAsorted
    by_cases hpb : it.pointerBeforeReference = true
    · simp only [hpb, if_true]
      exact hrev
    · have hpb' : it.pointerBeforeReference = false := by simpa using hpb
      simp only [hpb', Bool.false_eq_true, if_false]
      exact List.Pairwise.cons (fun x hx => hAref x (List.mem_reverse.mp hx)) hrev
  unfold previousNode iteratorCollection
  rw [hsp]
  simp only
  cases hf : (if it.pointerBeforeReference then A.reverse else it.reference :: A.reverse).find?
      (showsNode t it.whatToShow) with
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    intro m hm hacc
    have := find?_none_of_sorted hf m ((hcand m).mpr hm)
    rw [(showsNode_iff t it.whatToShow m).mpr hacc] at this
    cases this
  | some n =>
    obtain ⟨hn, hpn, hlast⟩ := find?_last_of_sorted hwf hroot hcandmem hcandsorted hf
    refine Or.inl ⟨n, rfl, ⟨(hcand n).mp hn, (showsNode_iff t it.whatToShow n).mp hpn⟩, ?_⟩
    rintro m ⟨hm, hacc⟩
    exact hlast m ((hcand m).mpr hm) ((showsNode_iff t it.whatToShow m).mpr hacc)

end Dom.Spec
