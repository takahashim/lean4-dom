import Dom.Properties.TreeOrder

/-!
# tree order の列（§4.2）と、その上の「最初の」

本文の多くの algorithm は「tree order で最初の」「following のうち最初の」と言う。実行関数は
`preorder`（前順の列）を `find?` で探すが、関係の側は列を使わず、§4.2 の tree order
（`PrecedesStruct`。ancestor であるか、共通の parent の下で index の小さい子の側にいる）で言う。

| 関係 | 本文 |
| --- | --- |
| `TreeOrderList t r l` | `r` の inclusive descendant を tree order に並べた列 |
| `FirstIn t P n` | `P` を満たす node のうち tree order で最初のもの |
| `Accepts t whatToShow n` | §6 "filter" の step 1-2（filter が null のとき） |

`TreeOrderList` は列を一意に決める（`treeOrderList_unique`）ので、「tree order の列」と言うことに
曖昧さは無い。実行関数の `preorder` がその列である（`treeOrderList_preorder`）。
-/

namespace Dom.Spec

open Dom.ListUtil

/-- `r` の inclusive descendant を tree order に並べた列。 -/
def TreeOrderList (t : Tree) (r : NodeId) (l : List NodeId) : Prop :=
  (∀ x, x ∈ l ↔ InclusiveDescendant t x r) ∧ l.Pairwise (PrecedesStruct t)

/-- `P` を満たす node のうち tree order で最初のもの。 -/
def FirstIn (t : Tree) (P : NodeId → Prop) (n : NodeId) : Prop :=
  P n ∧ ∀ m, P m → ¬ PrecedesStruct t m n

/-- §6 "filter" の step 1-2（filter は null）。node type の bit が whatToShow に立っている。 -/
def Accepts (t : Tree) (whatToShow : Nat) (n : NodeId) : Prop :=
  ∃ d, t.get? n = some d ∧ whatToShow.testBit (d.kind.nodeType - 1) = true

/-! ## tree order の性質 -/

/-- 木にある node の inclusive descendant は木にある。 -/
theorem exists_data_of_inclusive_descendant {t : Tree} (hwf : WellFormed t) {r x : NodeId}
    {rd : NodeData} (hx : InclusiveDescendant t x r) (hr : t.get? r = some rd) :
    ∃ d, t.get? x = some d :=
  exists_data_of_mem_preorderFuel t.size r x ((mem_preorder_iff hwf hr x).mpr hx)

theorem precedesStruct_irrefl {t : Tree} (hwf : WellFormed t) {x : NodeId} {d : NodeData}
    (hx : t.get? x = some d) : ¬ PrecedesStruct t x x := by
  intro h
  have := precedesIn_preorder_of_struct hwf hx (Or.inl rfl) (Or.inl rfl) h
  rw [precedesIn_self _ _ (preorder_nodup hwf x)] at this
  cases this

theorem precedesStruct_asymm {t : Tree} (hwf : WellFormed t) {r x y : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) (hx : InclusiveDescendant t x r) (hy : InclusiveDescendant t y r)
    (h : PrecedesStruct t x y) : ¬ PrecedesStruct t y x := by
  intro h'
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf hx hr
    exact precedesStruct_irrefl hwf hd h
  · have h1 := precedesIn_preorder_of_struct hwf hr hx hy h
    have h2 := precedesIn_preorder_of_struct hwf hr hy hx h'
    have hxm : x ∈ preorder t r := (mem_preorder_iff hwf hr x).mpr hx
    have hym : y ∈ preorder t r := (mem_preorder_iff hwf hr y).mpr hy
    have := precedesIn_asymm hxy hxm hym h1
    rw [h2] at this
    cases this

/-- 重複の無い列で、`precedesIn` が関係を含意するなら、列はその関係で整列している。 -/
theorem pairwise_of_precedesIn {R : NodeId → NodeId → Prop} :
    ∀ (l : List NodeId), l.Nodup →
      (∀ x y, x ∈ l → y ∈ l → x ≠ y → precedesIn l x y = true → R x y) → l.Pairwise R
  | [], _, _ => List.Pairwise.nil
  | a :: rest, hnd, h => by
    have hnd' := List.nodup_cons.mp hnd
    refine List.Pairwise.cons ?_ ?_
    · intro y hy
      have hne : a ≠ y := fun he => hnd'.1 (he ▸ hy)
      exact h a y (by simp) (by simp [hy]) hne (by rw [precedesIn_cons_self]; simpa using hy)
    · refine pairwise_of_precedesIn rest hnd'.2 ?_
      intro x y hx hy hxy hp
      have hxa : x ≠ a := fun he => hnd'.1 (he ▸ hx)
      have hya : y ≠ a := fun he => hnd'.1 (he ▸ hy)
      refine h x y (by simp [hx]) (by simp [hy]) hxy ?_
      rw [precedesIn_cons_ne (Ne.symm hxa) (Ne.symm hya)]
      exact hp

/-- 実行関数の `preorder` は tree order の列である。 -/
theorem treeOrderList_preorder {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) : TreeOrderList t r (preorder t r) := by
  refine ⟨fun x => mem_preorder_iff hwf hr x, ?_⟩
  refine pairwise_of_precedesIn _ (preorder_nodup hwf r) ?_
  intro x y hx hy hxy hp
  exact (precedesIn_preorder_iff_struct hwf hr ((mem_preorder_iff hwf hr x).mp hx)
    ((mem_preorder_iff hwf hr y).mp hy) hxy).mp hp

/-- tree order の列は一つしかない。 -/
theorem treeOrderList_unique {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {l₁ l₂ : List NodeId} (h₁ : TreeOrderList t r l₁)
    (h₂ : TreeOrderList t r l₂) : l₁ = l₂ := by
  refine eq_of_pairwise_of_mem_iff ?_ ?_ h₁.2 h₂.2 (fun x => by rw [h₁.1 x, h₂.1 x])
  · intro x hx
    obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf ((h₁.1 x).mp hx) hr
    exact precedesStruct_irrefl hwf hd
  · intro x hx y hy hxy
    exact precedesStruct_asymm hwf hr ((h₁.1 x).mp hx) ((h₁.1 y).mp hy) hxy

/-! ## 列の分解と「最初の」 -/

/-- 整列した列を `a` で分けると、後ろは `a` に後続するもの、前は `a` に先行するものである。 -/
theorem pairwise_split {R : NodeId → NodeId → Prop} {A B : List NodeId} {a : NodeId}
    (h : (A ++ a :: B).Pairwise R) : (∀ x ∈ A, R x a) ∧ (∀ x ∈ B, R a x) := by
  rw [List.pairwise_append] at h
  obtain ⟨_, hcons, hab⟩ := h
  refine ⟨fun x hx => hab x hx a (by simp), ?_⟩
  exact fun x hx => (List.pairwise_cons.mp hcons).1 x hx

/--
整列した列（関係は非対称）の、`a` より後ろの部分に入るのは、列にあって `a` に後続するものである。
-/
theorem mem_right_of_split {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {l A B : List NodeId} {a : NodeId}
    (hl : TreeOrderList t r l) (hsplit : l = A ++ a :: B) (x : NodeId) :
    x ∈ B ↔ x ∈ l ∧ PrecedesStruct t a x := by
  have hp := hl.2
  rw [hsplit] at hp
  obtain ⟨hA, hB⟩ := pairwise_split hp
  constructor
  · intro hx
    exact ⟨by rw [hsplit]; simp [hx], hB x hx⟩
  · rintro ⟨hxl, hax⟩
    have hxl' := hxl
    rw [hsplit] at hxl'
    rcases List.mem_append.mp hxl' with hxA | hxaB
    · exfalso
      exact precedesStruct_asymm hwf hr ((hl.1 a).mp (by rw [hsplit]; simp))
        ((hl.1 x).mp hxl) hax (hA x hxA)
    · rcases List.mem_cons.mp hxaB with rfl | hxB
      · exfalso
        obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf ((hl.1 x).mp hxl) hr
        exact precedesStruct_irrefl hwf hd hax
      · exact hxB

/-- 列の `a` より前の部分に入るのは、列にあって `a` に先行するものである。 -/
theorem mem_left_of_split {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {l A B : List NodeId} {a : NodeId}
    (hl : TreeOrderList t r l) (hsplit : l = A ++ a :: B) (x : NodeId) :
    x ∈ A ↔ x ∈ l ∧ PrecedesStruct t x a := by
  have hp := hl.2
  rw [hsplit] at hp
  obtain ⟨hA, hB⟩ := pairwise_split hp
  constructor
  · intro hx
    exact ⟨by rw [hsplit]; simp [hx], hA x hx⟩
  · rintro ⟨hxl, hxa⟩
    have hxl' := hxl
    rw [hsplit] at hxl'
    rcases List.mem_append.mp hxl' with hxA | hxaB
    · exact hxA
    · exfalso
      rcases List.mem_cons.mp hxaB with rfl | hxB
      · obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf ((hl.1 x).mp hxl) hr
        exact precedesStruct_irrefl hwf hd hxa
      · exact precedesStruct_asymm hwf hr ((hl.1 x).mp hxl)
          ((hl.1 a).mp (by rw [hsplit]; simp)) hxa (hB x hxB)

/--
非対称な関係で整列した列で `find?` が返すものは、`p` を満たす列の要素のうち、その関係で最初のものである。
-/
theorem find?_first_of_pairwise {R : NodeId → NodeId → Prop} {cand : List NodeId}
    (hirr : ∀ x ∈ cand, ¬ R x x) (hasym : ∀ x ∈ cand, ∀ y ∈ cand, R x y → ¬ R y x)
    (hsorted : cand.Pairwise R) {p : NodeId → Bool} {n : NodeId} (h : cand.find? p = some n) :
    n ∈ cand ∧ p n = true ∧ ∀ m ∈ cand, p m = true → ¬ R m n := by
  obtain ⟨hpn, l₁, l₂, hsplit, hl₁⟩ := List.find?_eq_some_iff_append.mp h
  have hn : n ∈ cand := by rw [hsplit]; simp
  refine ⟨hn, hpn, ?_⟩
  intro m hm hpm hmn
  have hp := hsorted
  rw [hsplit] at hp
  obtain ⟨hA, hB⟩ := pairwise_split hp
  have hm' := hm
  rw [hsplit] at hm'
  rcases List.mem_append.mp hm' with hmA | hmB
  · exact absurd hpm (by simpa using hl₁ m hmA)
  · rcases List.mem_cons.mp hmB with rfl | hmB
    · exact hirr m hm hmn
    · exact hasym n hn m hm (hB m hmB) hmn

/--
tree order で整列した列（inclusive descendant の部分列）で `find?` が返すものは、`p` を満たす列の要素のうち
tree order で最初のものである。
-/
theorem find?_first_of_sorted {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {cand : List NodeId} (hmem : ∀ x ∈ cand, InclusiveDescendant t x r)
    (hsorted : cand.Pairwise (PrecedesStruct t)) {p : NodeId → Bool} {n : NodeId}
    (h : cand.find? p = some n) :
    n ∈ cand ∧ p n = true ∧ ∀ m ∈ cand, p m = true → ¬ PrecedesStruct t m n :=
  find?_first_of_pairwise
    (fun x hx => by
      obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf (hmem x hx) hr
      exact precedesStruct_irrefl hwf hd)
    (fun x hx y hy => precedesStruct_asymm hwf hr (hmem x hx) (hmem y hy)) hsorted h

/-- 同じことを、tree order の逆（後ろから見る列）で言う。 -/
theorem find?_last_of_sorted {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {cand : List NodeId} (hmem : ∀ x ∈ cand, InclusiveDescendant t x r)
    (hsorted : cand.Pairwise (fun a b => PrecedesStruct t b a)) {p : NodeId → Bool} {n : NodeId}
    (h : cand.find? p = some n) :
    n ∈ cand ∧ p n = true ∧ ∀ m ∈ cand, p m = true → ¬ PrecedesStruct t n m :=
  find?_first_of_pairwise
    (fun x hx => by
      obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf (hmem x hx) hr
      exact precedesStruct_irrefl hwf hd)
    (fun x hx y hy hxy => precedesStruct_asymm hwf hr (hmem y hy) (hmem x hx) hxy) hsorted h

/-- `find?` が何も返さないなら、列に `p` を満たすものは無い。 -/
theorem find?_none_of_sorted {cand : List NodeId} {p : NodeId → Bool}
    (h : cand.find? p = none) : ∀ m ∈ cand, p m = false := by
  intro m hm
  have := List.find?_eq_none.mp h m hm
  simpa using this

end Dom.Spec
