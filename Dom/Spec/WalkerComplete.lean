import Dom.Spec.WalkerSibling

/-!
# TreeWalker の走査の関係は結果を一つに決める（completeness）

七つの関係はどれも「候補のうち accept されるもので、ある順序で最初（または最後）のもの、無ければ null」である。
候補はどれも current の木（current の root の inclusive descendant）にあり、そこでは tree order は全順序なので、
条件を満たす node は高々一つで、null との両立もしない（`result_unique`）。だから関係を満たす結果は一つに決まり、
soundness と合わせると実行関数の結果に等しい（completeness）。

`lastChild()` と `previousSibling()` は鏡像の tree order で書いてあるので、子の列を反転した木の
`firstChild()`・`nextSibling()` の関係へ移して使う（`walkerLastChildResult_iff`・`walkerPreviousSiblingResult_iff`）。
-/

namespace Dom.Spec

open Dom

variable {t : Tree}

/-- 「最初の候補か、候補が無ければ null」の形の関係は、順序が候補の上で全順序なら結果を一つに決める。 -/
theorem result_unique {R : NodeId → NodeId → Prop} {Cand A : NodeId → Prop} {r₁ r₂ : Option NodeId}
    (htot : ∀ x y, Cand x → Cand y → x ≠ y → R x y ∨ R y x)
    (h₁ : (∃ n, r₁ = some n ∧ (Cand n ∧ A n) ∧ ∀ m, Cand m ∧ A m → ¬ R m n) ∨
      (r₁ = none ∧ ∀ m, Cand m → ¬ A m))
    (h₂ : (∃ n, r₂ = some n ∧ (Cand n ∧ A n) ∧ ∀ m, Cand m ∧ A m → ¬ R m n) ∨
      (r₂ = none ∧ ∀ m, Cand m → ¬ A m)) : r₁ = r₂ := by
  rcases h₁ with ⟨n₁, rfl, hn₁, hf₁⟩ | ⟨rfl, hno₁⟩ <;>
    rcases h₂ with ⟨n₂, rfl, hn₂, hf₂⟩ | ⟨rfl, hno₂⟩
  · refine congrArg some (Classical.byContradiction fun hne => ?_)
    rcases htot n₁ n₂ hn₁.1 hn₂.1 hne with h | h
    · exact hf₂ n₁ hn₁ h
    · exact hf₁ n₂ hn₂ h
  · exact absurd hn₁.2 (hno₂ n₁ hn₁.1)
  · exact absurd hn₂.2 (hno₁ n₂ hn₂.1)
  · rfl

/-- current の木の上で、tree order は全順序である。 -/
theorem precedes_total_in_root (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {Cand : NodeId → Prop} (hin : ∀ x, Cand x → InclusiveDescendant t x (root t w.current)) :
    ∀ x y, Cand x → Cand y → x ≠ y → PrecedesStruct t x y ∨ PrecedesStruct t y x := by
  obtain ⟨-, ⟨cd, hcd⟩⟩ := hw
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hcd
  intro x y hx hy hxy
  exact precedesStruct_total_of_mem hwf hrd (hin x hx) (hin y hy) hxy

/-- 逆向きの順序（`LastIn` の形）も全順序である。 -/
theorem precedes_total_flip {Cand : NodeId → Prop}
    (h : ∀ x y, Cand x → Cand y → x ≠ y → PrecedesStruct t x y ∨ PrecedesStruct t y x) :
    ∀ x y, Cand x → Cand y → x ≠ y →
      (fun a b => PrecedesStruct t b a) x y ∨ (fun a b => PrecedesStruct t b a) y x := by
  intro x y hx hy hxy
  rcases h x y hx hy hxy with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

theorem inRoot_of_ancestor (hwf : WellFormed t) {a x : NodeId} (h : Ancestor t a x) :
    InclusiveDescendant t x (root t a) := by
  rw [← root_eq_of_ancestor hwf h]; exact root_inclusive_ancestor t x

theorem inRoot_of_ancestor' (hwf : WellFormed t) {x c : NodeId} (h : Ancestor t x c) :
    InclusiveDescendant t x (root t c) := by
  rw [root_eq_of_ancestor hwf h]; exact root_inclusive_ancestor t x

/-! ## 一意性 -/

theorem walkerNextNodeResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerNextNodeResult t w r₁) (h₂ : WalkerNextNodeResult t w r₂) :
    r₁ = r₂ :=
  result_unique (R := PrecedesStruct t)
    (precedes_total_in_root hwf hw fun _ hx => precedesStruct_root hwf hx.1) h₁ h₂

theorem walkerPreviousNodeResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerPreviousNodeResult t w r₁)
    (h₂ : WalkerPreviousNodeResult t w r₂) : r₁ = r₂ :=
  result_unique (R := fun a b => PrecedesStruct t b a)
    (precedes_total_flip (precedes_total_in_root hwf hw fun _ hx => precedesStruct_root_left hwf hx.2.1))
    h₁ h₂

theorem walkerFirstChildResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerFirstChildResult t w r₁)
    (h₂ : WalkerFirstChildResult t w r₂) : r₁ = r₂ :=
  result_unique (R := PrecedesStruct t)
    (precedes_total_in_root hwf hw fun _ hx => inRoot_of_ancestor hwf hx.1) h₁ h₂

theorem walkerParentNodeResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerParentNodeResult t w r₁)
    (h₂ : WalkerParentNodeResult t w r₂) : r₁ = r₂ :=
  result_unique (R := fun a b => PrecedesStruct t b a)
    (precedes_total_flip (precedes_total_in_root hwf hw fun _ hx => inRoot_of_ancestor' hwf hx.1))
    h₁ h₂

/-- `nextSibling()` の候補は current の木にある。 -/
theorem nextSiblingCandidate_inRoot (hwf : WellFormed t) {w : WalkerState} {x : NodeId}
    (hx : WalkerNextSiblingCandidate t w x) : InclusiveDescendant t x (root t w.current) := by
  obtain ⟨-, a, s, ⟨ha, -⟩, ⟨q, -, -, haq, hsq, -⟩, hxs⟩ := hx
  have hqx : Ancestor t q x := by
    rcases hxs with rfl | h
    · exact Ancestor.step hsq
    · exact (Ancestor.step hsq).trans_ancestor h
  have hqc : Ancestor t q w.current := by
    rcases ha with rfl | h
    · exact Ancestor.step haq
    · exact (Ancestor.step haq).trans_ancestor h
  rw [root_eq_of_ancestor hwf hqc, ← root_eq_of_ancestor hwf hqx]
  exact root_inclusive_ancestor t x

theorem walkerNextSiblingResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerNextSiblingResult t w r₁)
    (h₂ : WalkerNextSiblingResult t w r₂) : r₁ = r₂ :=
  result_unique (R := PrecedesStruct t)
    (precedes_total_in_root hwf hw fun _ hx => nextSiblingCandidate_inRoot hwf hx) h₁ h₂

/-! ## 鏡像の二つ -/

theorem walkerLastChildResult_iff (hwf : WellFormed t) {w : WalkerState} {r : Option NodeId} :
    WalkerFirstChildResult (mirrorTree t) w r ↔ WalkerLastChildResult t w r := by
  unfold WalkerFirstChildResult FirstIn WalkerLastChildResult MirrorFirstIn
  simp only [walkerChildCandidate_mirrorTree_iff hwf, accepts_mirrorTree_iff,
    precedesStruct_mirrorTree_iff hwf]

theorem walkerPreviousSiblingResult_iff (hwf : WellFormed t) {w : WalkerState} {r : Option NodeId} :
    WalkerNextSiblingResult (mirrorTree t) w r ↔ WalkerPreviousSiblingResult t w r := by
  unfold WalkerNextSiblingResult FirstIn WalkerPreviousSiblingResult MirrorFirstIn
  simp only [nextSiblingCandidate_mirrorTree_iff hwf, accepts_mirrorTree_iff,
    precedesStruct_mirrorTree_iff hwf]

theorem walkerLastChildResult_unique (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r₁ r₂ : Option NodeId} (h₁ : WalkerLastChildResult t w r₁)
    (h₂ : WalkerLastChildResult t w r₂) : r₁ = r₂ :=
  walkerFirstChildResult_unique (wellFormed_mirrorTree hwf) (validWalker_mirrorTree hw)
    ((walkerLastChildResult_iff hwf).mpr h₁) ((walkerLastChildResult_iff hwf).mpr h₂)

theorem walkerPreviousSiblingResult_unique (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r₁ r₂ : Option NodeId} (h₁ : WalkerPreviousSiblingResult t w r₁)
    (h₂ : WalkerPreviousSiblingResult t w r₂) : r₁ = r₂ :=
  walkerNextSiblingResult_unique (wellFormed_mirrorTree hwf) (validWalker_mirrorTree hw)
    ((walkerPreviousSiblingResult_iff hwf).mpr h₁) ((walkerPreviousSiblingResult_iff hwf).mpr h₂)

/-! ## completeness -/

/-- **`nextNode()` の completeness。** 関係を満たす結果は、実行関数の結果である。 -/
theorem walkerNextNode_result_complete (hwf : WellFormed t) {w : WalkerState} (hw : ValidWalker t w)
    {r : Option NodeId} (h : WalkerNextNodeResult t w r) : r = walkerNextNode t w :=
  walkerNextNodeResult_unique hwf hw h (walkerNextNode_result_sound hwf hw)

/-- **`previousNode()` の completeness。** -/
theorem walkerPreviousNode_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerPreviousNodeResult t w r) :
    r = walkerPreviousNode t w :=
  walkerPreviousNodeResult_unique hwf hw h (walkerPreviousNode_result_sound hwf hw)

/-- **`firstChild()` の completeness。** -/
theorem walkerFirstChild_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerFirstChildResult t w r) :
    r = walkerFirstChild t w :=
  walkerFirstChildResult_unique hwf hw h (walkerFirstChild_result_sound hwf hw)

/-- **`lastChild()` の completeness。** -/
theorem walkerLastChild_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerLastChildResult t w r) :
    r = walkerLastChild t w :=
  walkerLastChildResult_unique hwf hw h (walkerLastChild_result_sound hwf hw)

/-- **`parentNode()` の completeness。** -/
theorem walkerParentNode_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerParentNodeResult t w r) :
    r = walkerParentNode t w :=
  walkerParentNodeResult_unique hwf hw h (walkerParentNode_result_sound hwf hw)

/-- **`nextSibling()` の completeness。** -/
theorem walkerNextSibling_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerNextSiblingResult t w r) :
    r = walkerSibling t w true :=
  walkerNextSiblingResult_unique hwf hw h (walkerNextSibling_result_sound hwf hw)

/-- **`previousSibling()` の completeness。** -/
theorem walkerPreviousSibling_result_complete (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) {r : Option NodeId} (h : WalkerPreviousSiblingResult t w r) :
    r = walkerSibling t w false :=
  walkerPreviousSiblingResult_unique hwf hw h (walkerPreviousSibling_result_sound hwf hw)

end Dom.Spec
