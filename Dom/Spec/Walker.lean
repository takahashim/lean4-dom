import Dom.Spec.TreeOrder
import Dom.Spec.Traverse
import Dom.Traversal.TreeWalker
import Dom.Properties.Walker

/-!
# TreeWalker の走査の関係仕様（§6.2）

filter が null なら、`nextNode()`・`previousNode()`・"traverse children"（first）・`parentNode()` は
それぞれ「ある候補の集まりのうち accept されるもので tree order で最初（または最後）のもの」である。
候補の集まりを本文の loop から読み取って関係にする。

* `nextNode()`：current に後続する node。ただし走査は `root` を見終えて上がろうとするところで止まる
  （step 3.4.1「temporary が root なら null」）ので、root の最後の inclusive descendant `L` を見終えたら止まる。
  current が `L` 以前（`L` 自身を含む）にあれば、`L` より後ろは候補でない。
* `previousNode()`：current に先行する node。current が root なら何も見ない（step 2）。走査が root に達したとき、
  root に children があれば root へ親として上がってきたところで、root を見て止まる（step 2.4-2.5 と step 2 の
  while 条件）。root に children が無ければ root を前の兄弟（かその最後の子）として見て、root に前の兄弟が
  無ければ止まり（step 2.3）、あれば inner loop がそちらへ続く（step 2.2.5）。止まるなら root より前は候補でない。
* "traverse children"（first）：current の子孫。親へ上がったときにそれが root か current なら止まる（step 3.4.4）。
  root へ親として上がるのは、root が current の子孫で children を持ち、その子孫を見終えたときだけである。
  root が葉なら、root を見たあとも兄弟へ進む（step 3.4.2）。
* `parentNode()`：current の祖先を近いほうから root まで。

`lastChild()` と "traverse siblings" は `Dom/Spec/WalkerMirror.lean`・`Dom/Spec/WalkerSibling.lean` にある。

実行関数がこれらを満たすことは `walkerNextNode_result_sound`・`walkerFirstChild_result_sound`・
`walkerParentNode_result_sound` と、`Dom/Spec/WalkerSibling.lean` の `walkerPreviousNode_result_sound` が示す
（`ValidWalker` を仮定する。`previousNode()` の証明は兄弟の列の補題を使うので、そちらに置いてある）。
関係が結果を一つに決めること（completeness）は `Dom/Spec/WalkerComplete.lean` にある。
-/

namespace Dom.Spec

open Dom.ListUtil

/-- `L` が `r` の inclusive descendant のうち tree order で最後のもの。 -/
def LastDescendantOf (t : Tree) (r L : NodeId) : Prop :=
  InclusiveDescendant t L r ∧ ∀ x, InclusiveDescendant t x r → ¬ PrecedesStruct t L x

/-- `nextNode()` の候補。 -/
def WalkerNextCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  PrecedesStruct t w.current x ∧
    ∀ L, LastDescendantOf t w.root L → (w.current = L ∨ PrecedesStruct t w.current L) →
      ¬ PrecedesStruct t L x

/-- `s` が `a` の後ろの兄弟。 -/
def FollowingSibling (t : Tree) (a s : NodeId) : Prop :=
  ∃ p i j, parentOf t a = some p ∧ parentOf t s = some p ∧ index t a = some i ∧
    index t s = some j ∧ i < j

/-- `s` が `a` の前の兄弟。 -/
def PrecedingSibling (t : Tree) (a s : NodeId) : Prop :=
  ∃ p i j, parentOf t a = some p ∧ parentOf t s = some p ∧ index t a = some i ∧
    index t s = some j ∧ j < i

/--
`previousNode()` の走査が root `r` に達したところで止まる。

`r` に child があれば、走査は `r` の最初の子から `r` へ親として上がってきて（step 2.4-2.5）、
step 2 の while 条件で止まる。`r` に前の兄弟が無ければ、`r` を見終えたところで step 2.3「node が root なら
null」に当たる。どちらでもない（`r` が葉で前の兄弟を持つ）なら、step 2.2 の inner loop が前の兄弟へ続く。
-/
def PreviousStopsAtRoot (t : Tree) (r : NodeId) : Prop :=
  (∃ y, parentOf t y = some r) ∨ ¬ ∃ s, PrecedingSibling t r s

/--
`previousNode()` の候補。current が root なら無い（step 2）。走査が root に達してそこで止まるなら、
root より前は候補でない。
-/
def WalkerPreviousCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  w.current ≠ w.root ∧ PrecedesStruct t x w.current ∧
    (PrecedesStruct t w.root w.current → PreviousStopsAtRoot t w.root → ¬ PrecedesStruct t x w.root)

/--
"traverse children"（first）の候補：current の子孫。step 3.4.4 で root へ親として上がるのは、
root が current の子孫で、その最後の inclusive descendant `L` が root 自身でない（root に children がある）とき、
`L` を見終えたところである。そこより後ろは候補でない。
-/
def WalkerChildCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  Ancestor t w.current x ∧
    ∀ L, LastDescendantOf t w.root L → Ancestor t w.root L → Ancestor t w.current w.root →
      ¬ PrecedesStruct t L x

/-- `parentNode()` の候補：current の strict ancestor のうち、root より上でないもの。 -/
def WalkerParentCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  Ancestor t x w.current ∧ ¬ (InclusiveAncestor t w.root w.current ∧ Ancestor t x w.root)

def WalkerNextNodeResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧ FirstIn t (fun x => WalkerNextCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerNextCandidate t w m → ¬ Accepts t w.whatToShow m)

def WalkerPreviousNodeResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧
      LastIn t (fun x => WalkerPreviousCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerPreviousCandidate t w m → ¬ Accepts t w.whatToShow m)

def WalkerFirstChildResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧ FirstIn t (fun x => WalkerChildCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerChildCandidate t w m → ¬ Accepts t w.whatToShow m)

def WalkerParentNodeResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧
      LastIn t (fun x => WalkerParentCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerParentCandidate t w m → ¬ Accepts t w.whatToShow m)

/-! ## 補題 -/

/-- `L` で切る `takeUntilIncl`：`L` が列にあれば、最初の `L` までの prefix。 -/
theorem takeUntilIncl_split {L : NodeId} :
    ∀ {l A B : List NodeId}, l = A ++ L :: B → L ∉ A →
      takeUntilIncl (· == L) l = A ++ [L]
  | _, [], B, rfl, _ => by simp [takeUntilIncl]
  | _, a :: A, B, rfl, hA => by
    have haL : a ≠ L := fun h => hA (by simp [h])
    have : L ∉ A := fun h => hA (by simp [h])
    simp [takeUntilIncl, haL, takeUntilIncl_split (l := A ++ L :: B) rfl this]

theorem takeUntilIncl_of_not_mem {L : NodeId} :
    ∀ {l : List NodeId}, L ∉ l → takeUntilIncl (· == L) l = l
  | [], _ => rfl
  | a :: l, h => by
    have haL : a ≠ L := fun he => h (by simp [he])
    have : L ∉ l := fun he => h (by simp [he])
    simp [takeUntilIncl, haL, takeUntilIncl_of_not_mem this]

/-- tree order で先行し合う node は、同じ root の下にある。 -/
theorem precedesStruct_root {t : Tree} (hwf : WellFormed t) {x y : NodeId}
    (h : PrecedesStruct t x y) : InclusiveDescendant t y (root t x) := by
  rcases h with hanc | ⟨p, cx, cy, i, j, hcx, hcy, -, -, -, hxcx, hycy⟩
  · rw [← root_eq_of_ancestor hwf hanc]; exact root_inclusive_ancestor t y
  · have hpx : Ancestor t p x := by
      rcases hxcx with rfl | h
      · exact Ancestor.step hcx
      · exact (Ancestor.step hcx).trans_ancestor h
    have hpy : Ancestor t p y := by
      rcases hycy with rfl | h
      · exact Ancestor.step hcy
      · exact (Ancestor.step hcy).trans_ancestor h
    rw [root_eq_of_ancestor hwf hpx, ← root_eq_of_ancestor hwf hpy]
    exact root_inclusive_ancestor t y

theorem exists_data_root {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : ∃ rd, t.get? (root t n) = some rd := by
  rcases root_inclusive_ancestor t n with h | h
  · exact ⟨d, by rw [h]; exact hn⟩
  · exact exists_data_of_ancestor hwf h

/-- tree order で整列した列の要素どうしは、どちらかが先行する。 -/
theorem precedesStruct_total_of_mem {t : Tree} (hwf : WellFormed t) {r x y : NodeId}
    {rd : NodeData} (hr : t.get? r = some rd) (hx : InclusiveDescendant t x r)
    (hy : InclusiveDescendant t y r) (hxy : x ≠ y) :
    PrecedesStruct t x y ∨ PrecedesStruct t y x := by
  have hxm := (mem_preorder_iff hwf hr x).mpr hx
  have hym := (mem_preorder_iff hwf hr y).mpr hy
  rcases precedesIn_total hxm hym hxy with h | h
  · exact Or.inl ((precedesIn_preorder_iff_struct hwf hr hx hy hxy).mp h)
  · exact Or.inr ((precedesIn_preorder_iff_struct hwf hr hy hx (Ne.symm hxy)).mp h)

/-- `lastDescendant` は root の最後の inclusive descendant である。 -/
theorem lastDescendantOf_lastDescendant {t : Tree} (hwf : WellFormed t) {r : NodeId}
    {rd : NodeData} (hr : t.get? r = some rd) : LastDescendantOf t r (lastDescendant t r) := by
  have hl := treeOrderList_preorder hwf hr
  have hne : preorder t r ≠ [] := by
    intro h; have := (hl.1 r).mpr (Or.inl rfl); rw [h] at this; simp at this
  obtain ⟨init, last, hsplit⟩ := List.eq_nil_or_concat (preorder t r) |>.resolve_left hne
  have hL : lastDescendant t r = last := by
    unfold lastDescendant; rw [hsplit]; simp
  rw [hL]
  have hmem : ∀ x, InclusiveDescendant t x r ↔ x ∈ init ∨ x = last := by
    intro x; rw [← hl.1 x, hsplit]; simp
  refine ⟨(hmem last).mpr (Or.inr rfl), ?_⟩
  intro x hx hprec
  have hp := hl.2
  rw [hsplit, List.concat_eq_append, List.pairwise_append] at hp
  rcases (hmem x).mp hx with hxi | rfl
  · exact precedesStruct_asymm hwf hr hx ((hmem last).mpr (Or.inr rfl))
      (hp.2.2 x hxi last (by simp)) hprec
  · obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf hx hr
    exact precedesStruct_irrefl hwf hd hprec

theorem lastDescendantOf_unique {t : Tree} (hwf : WellFormed t) {r L₁ L₂ : NodeId}
    {rd : NodeData} (hr : t.get? r = some rd) (h₁ : LastDescendantOf t r L₁)
    (h₂ : LastDescendantOf t r L₂) : L₁ = L₂ := by
  refine Classical.byContradiction fun hne => ?_
  rcases precedesStruct_total_of_mem hwf hr h₁.1 h₂.1 hne with h | h
  · exact h₁.2 L₂ h₂.1 h
  · exact h₂.2 L₁ h₁.1 h

/-! ## 整列した列から結果を読む -/

theorem takeUntilIncl_sublist {L : NodeId} :
    ∀ (l : List NodeId), (takeUntilIncl (· == L) l).Sublist l
  | [] => List.Sublist.slnil
  | a :: l => by
    unfold takeUntilIncl
    split
    · exact ((List.nil_sublist l).cons_cons a)
    · exact (takeUntilIncl_sublist l).cons_cons a

/--
非対称な関係 `R` で整列した列 `l` を `L` で切った列の要素は、`l` の要素で `L` に `R` で後続しないもの
（`L` が列に無ければ `l` 全体）。
-/
theorem mem_takeUntilIncl_iff {R : NodeId → NodeId → Prop} {l : List NodeId} {L : NodeId}
    (hirr : ∀ x ∈ l, ¬ R x x) (hasym : ∀ x ∈ l, ∀ y ∈ l, R x y → ¬ R y x)
    (hsorted : l.Pairwise R) (x : NodeId) :
    x ∈ takeUntilIncl (· == L) l ↔ x ∈ l ∧ (L ∈ l → ¬ R L x) := by
  by_cases hL : L ∈ l
  · obtain ⟨A, B, hsp⟩ := exists_splitAt?_of_mem hL
    have hAB := splitAt?_eq_some hsp
    rw [takeUntilIncl_split hAB (splitAt?_not_mem_left hsp)]
    have hp := hsorted
    rw [hAB] at hp
    obtain ⟨hA, hB⟩ := pairwise_split hp
    constructor
    · intro hx
      have hx' : x ∈ A ∨ x = L := by simpa using hx
      have hxl : x ∈ l := by
        rw [hAB]
        rcases hx' with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (by simp [h])
      refine ⟨hxl, fun _ hLx => ?_⟩
      rcases hx' with hxA | rfl
      · exact hasym x hxl L hL (hA x hxA) hLx
      · exact hirr x hxl hLx
    · rintro ⟨hxl, hn⟩
      have hxl' := hxl
      rw [hAB] at hxl'
      simp only [List.mem_append, List.mem_cons] at hxl'
      rcases hxl' with h | h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (by simp [h])
      · exact absurd (hB x h) (hn hL)
  · rw [takeUntilIncl_of_not_mem hL]
    exact ⟨fun h => ⟨h, fun h' => absurd h' hL⟩, fun h => h.1⟩

/-- `cutAtRootExit` で切った列の要素：`L` が root でなく列にあれば、`L` に `R` で後続しないもの。 -/
theorem mem_cutAtRootExit_iff {R : NodeId → NodeId → Prop} {l : List NodeId} {r L : NodeId}
    (hirr : ∀ x ∈ l, ¬ R x x) (hasym : ∀ x ∈ l, ∀ y ∈ l, R x y → ¬ R y x)
    (hsorted : l.Pairwise R) (x : NodeId) :
    x ∈ cutAtRootExit r L l ↔ x ∈ l ∧ (L ≠ r → L ∈ l → ¬ R L x) := by
  unfold cutAtRootExit
  split
  · next h =>
    have h' : L = r := by simpa using h
    exact ⟨fun hx => ⟨hx, fun hne => absurd h' hne⟩, fun h => h.1⟩
  · next h =>
    have hne : L ≠ r := by simpa using h
    rw [mem_takeUntilIncl_iff hirr hasym hsorted]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2 hne⟩⟩

theorem cutAtRootExit_sublist (r L : NodeId) (l : List NodeId) : (cutAtRootExit r L l).Sublist l := by
  unfold cutAtRootExit
  split
  · exact List.Sublist.refl _
  · exact takeUntilIncl_sublist l

/-- 候補の列（非対称な関係で整列）で `find?` した結果は、候補で accept されるもののうち最初のもの。 -/
theorem result_of_sorted {R : NodeId → NodeId → Prop} {Cand : NodeId → Prop} {C : List NodeId}
    {t : Tree} {ws : Nat} (hiff : ∀ x, x ∈ C ↔ Cand x) (hirr : ∀ x ∈ C, ¬ R x x)
    (hasym : ∀ x ∈ C, ∀ y ∈ C, R x y → ¬ R y x) (hsorted : C.Pairwise R) :
    (∃ n, C.find? (showsNode t ws) = some n ∧ (Cand n ∧ Accepts t ws n) ∧
        ∀ m, Cand m ∧ Accepts t ws m → ¬ R m n) ∨
      (C.find? (showsNode t ws) = none ∧ ∀ m, Cand m → ¬ Accepts t ws m) := by
  cases hf : C.find? (showsNode t ws) with
  | none =>
    refine Or.inr ⟨rfl, fun m hm hacc => ?_⟩
    have := find?_none_of_sorted hf m ((hiff m).mpr hm)
    rw [(showsNode_iff t ws m).mpr hacc] at this
    cases this
  | some n =>
    obtain ⟨hn, hpn, hfirst⟩ := find?_first_of_pairwise hirr hasym hsorted hf
    refine Or.inl ⟨n, rfl, ⟨(hiff n).mp hn, (showsNode_iff t ws n).mp hpn⟩, ?_⟩
    rintro m ⟨hm, hacc⟩
    exact hfirst m ((hiff m).mpr hm) ((showsNode_iff t ws m).mpr hacc)

/-- 木の中で、tree order は非反射的で非対称である。 -/
theorem precedesStruct_order_on {t : Tree} (hwf : WellFormed t) {r : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) {C : List NodeId} (hmem : ∀ x ∈ C, InclusiveDescendant t x r) :
    (∀ x ∈ C, ¬ PrecedesStruct t x x) ∧
      (∀ x ∈ C, ∀ y ∈ C, PrecedesStruct t x y → ¬ PrecedesStruct t y x) :=
  ⟨fun x hx => by
      obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf (hmem x hx) hr
      exact precedesStruct_irrefl hwf hd,
    fun x hx y hy => precedesStruct_asymm hwf hr (hmem x hx) (hmem y hy)⟩

/-- `y` に先行する node は、`y` の root の下にある。 -/
theorem precedesStruct_root_left {t : Tree} (hwf : WellFormed t) {x y : NodeId}
    (h : PrecedesStruct t x y) : InclusiveDescendant t x (root t y) := by
  have hy := precedesStruct_root hwf h
  have : root t y = root t x := root_unique hwf hy (root_parent_eq_none hwf x)
  rw [this]; exact root_inclusive_ancestor t x

/-- strict ancestor の列は、根に近いほど後ろにある（tree order では先行する）。 -/
theorem ancestorChain_pairwise {t : Tree} :
    ∀ (f : Nat) (n : NodeId), (ancestorChain t f n).Pairwise (fun a b => PrecedesStruct t b a)
  | 0, _ => by simp [ancestorChain]
  | f + 1, n => by
    unfold ancestorChain
    split
    · exact List.Pairwise.nil
    · next p _ =>
      refine List.Pairwise.cons ?_ (ancestorChain_pairwise f p)
      intro x hx
      exact Or.inl (mem_ancestorChain_ancestor f p x hx)

/-! ## `parentNode()` -/

theorem walkerParentNode_result_sound {t : Tree} (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerParentNodeResult t w (walkerParentNode t w) := by
  obtain ⟨⟨rootd, hrootd⟩, ⟨cd, hcd⟩⟩ := hw
  obtain ⟨rtd, hrtd⟩ := exists_data_root hwf hcd
  unfold walkerParentNode
  split
  · next heq =>
    have heq' : w.current = w.root := by simpa using heq
    refine Or.inr ⟨rfl, fun m hm _ => ?_⟩
    exact hm.2 ⟨Or.inl heq'.symm, heq' ▸ hm.1⟩
  · next hne =>
    have hne' : w.current ≠ w.root := by simpa using hne
    have hA : ∀ x, x ∈ ancestors t w.current ↔ Ancestor t x w.current := mem_ancestors_iff hwf _
    have hAmem : ∀ x ∈ ancestors t w.current, InclusiveDescendant t x (root t w.current) := by
      intro x hx
      have hxc := (hA x).mp hx
      rw [root_eq_of_ancestor hwf hxc]
      exact root_inclusive_ancestor t x
    have hAsorted : (ancestors t w.current).Pairwise (fun a b => PrecedesStruct t b a) :=
      ancestorChain_pairwise _ _
    obtain ⟨hirr, hasym⟩ := precedesStruct_order_on hwf hrtd hAmem
    have hiff : ∀ x, x ∈ takeUntilIncl (· == w.root) (ancestors t w.current) ↔
        WalkerParentCandidate t w x := by
      intro x
      rw [mem_takeUntilIncl_iff (R := fun a b => PrecedesStruct t b a) hirr
        (fun a ha b hb h => hasym b hb a ha h) hAsorted, hA, hA]
      unfold WalkerParentCandidate
      constructor
      · rintro ⟨hxc, hn⟩
        refine ⟨hxc, fun ⟨hrc, hxr⟩ => ?_⟩
        rcases hrc with heq | hrc
        · exact hne' heq.symm
        · exact hn hrc (Or.inl hxr)
      · rintro ⟨hxc, hn⟩
        refine ⟨hxc, fun hrc hp => ?_⟩
        have hxm := (hA x).mpr hxc
        have hrm := (hA w.root).mpr hrc
        rcases inclusive_ancestor_linear (Or.inr hxc) (Or.inr hrc) with h | h
        · rcases h with rfl | h
          · exact hirr _ hxm hp
          · exact hn ⟨Or.inr hrc, h⟩
        · rcases h with rfl | h
          · exact hirr _ hrm hp
          · exact hasym x hxm w.root hrm hp (Or.inl h)
    have hsub := takeUntilIncl_sublist (L := w.root) (ancestors t w.current)
    have hmem' : ∀ x ∈ takeUntilIncl (· == w.root) (ancestors t w.current),
        InclusiveDescendant t x (root t w.current) := fun x hx => hAmem x (hsub.subset hx)
    obtain ⟨hirr', hasym'⟩ := precedesStruct_order_on hwf hrtd hmem'
    have := result_of_sorted (t := t) (ws := w.whatToShow) (R := fun a b => PrecedesStruct t b a) hiff
      hirr' (fun a ha b hb h => hasym' b hb a ha h) (hAsorted.sublist hsub)
    unfold WalkerParentNodeResult LastIn
    rcases this with ⟨n, hf, hn, hlast⟩ | ⟨hf, hnone⟩
    · exact Or.inl ⟨n, by rw [← hf]; rfl, hn, hlast⟩
    · exact Or.inr ⟨by rw [← hf]; rfl, hnone⟩

/-! ## `nextNode()` -/

theorem walkerNextNode_result_sound {t : Tree} (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerNextNodeResult t w (walkerNextNode t w) := by
  obtain ⟨⟨rootd, hrootd⟩, ⟨cd, hcd⟩⟩ := hw
  obtain ⟨rtd, hrtd⟩ := exists_data_root hwf hcd
  have hl := treeOrderList_preorder hwf hrtd
  have hc : w.current ∈ preorder t (root t w.current) :=
    (hl.1 _).mpr (root_inclusive_ancestor t w.current)
  have hLd := lastDescendantOf_lastDescendant hwf hrootd
  -- 候補でありうるのは current の木の node で、current に後続するもの
  have hinP : ∀ x, PrecedesStruct t w.current x → x ∈ preorder t (root t w.current) :=
    fun x hx => (hl.1 x).mpr (precedesStruct_root hwf hx)
  have hcand_simp : ∀ x, WalkerNextCandidate t w x ↔ PrecedesStruct t w.current x ∧
      ((w.current = lastDescendant t w.root ∨ PrecedesStruct t w.current (lastDescendant t w.root)) →
        ¬ PrecedesStruct t (lastDescendant t w.root) x) := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 _ hLd⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun L hL => ?_⟩
      rw [lastDescendantOf_unique hwf hrootd hL hLd]; exact h2
  unfold walkerNextNode
  unfold treeOrder
  obtain ⟨X, after, hsp⟩ := exists_splitAt?_of_mem hc
  have hsplit := splitAt?_eq_some hsp
  rw [hsp]
  simp only
  have hafter : ∀ x, x ∈ after ↔ PrecedesStruct t w.current x := by
    intro x
    rw [mem_right_of_split hwf hrtd hl hsplit x]
    exact ⟨fun h => h.2, fun h => ⟨hinP x h, h⟩⟩
  have hafterSorted : after.Pairwise (PrecedesStruct t) := by
    have hp := hl.2
    rw [hsplit, List.pairwise_append] at hp
    exact (List.pairwise_cons.mp hp.2.1).2
  have hafterMem : ∀ x ∈ after, InclusiveDescendant t x (root t w.current) := fun x hx =>
    (hl.1 x).mp (by rw [hsplit]; simp [hx])
  split
  · -- current が root の最後の inclusive descendant
    next heq =>
    have heq' : w.current = lastDescendant t w.root := by simpa using heq
    refine Or.inr ⟨rfl, fun m hm _ => ?_⟩
    obtain ⟨h1, h2⟩ := (hcand_simp m).mp hm
    exact h2 (Or.inl heq') (heq' ▸ h1)
  · next hne =>
    have hne' : w.current ≠ lastDescendant t w.root := by simpa using hne
    -- 候補の列
    obtain ⟨C, hC, hCsub_iff, hCsub⟩ : ∃ C, takeUntilIncl (· == lastDescendant t w.root) after = C ∧
        (∀ x, x ∈ C ↔ WalkerNextCandidate t w x) ∧ C.Sublist after := by
      by_cases hLa : lastDescendant t w.root ∈ after
      · obtain ⟨A, B, hspA⟩ := exists_splitAt?_of_mem hLa
        have hAB := splitAt?_eq_some hspA
        have hnA := splitAt?_not_mem_left hspA
        refine ⟨A ++ [lastDescendant t w.root], takeUntilIncl_split hAB hnA, ?_, ?_⟩
        · intro x
          rw [hcand_simp]
          have hpL := (hafter _).mp hLa
          constructor
          · intro hx
            have hx' : x ∈ A ∨ x = lastDescendant t w.root := by simpa using hx
            have hxa : x ∈ after := by
              rw [hAB]
              rcases hx' with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (by simp [h])
            refine ⟨(hafter x).mp hxa, fun _ hLx => ?_⟩
            have hp := hafterSorted
            rw [hAB] at hp
            obtain ⟨hA', hB'⟩ := pairwise_split hp
            rcases hx' with hxA | rfl
            · exact precedesStruct_asymm hwf hrtd (hafterMem _ hLa) (hafterMem _ hxa) hLx (hA' x hxA)
            · obtain ⟨d, hd⟩ := exists_data_of_inclusive_descendant hwf (hafterMem _ hLa) hrtd
              exact precedesStruct_irrefl hwf hd hLx
          · rintro ⟨h1, h2⟩
            have hxa := (hafter x).mpr h1
            have := h2 (Or.inr hpL)
            have hxl : x ∈ after := hxa
            rw [hAB] at hxl
            simp only [List.mem_append, List.mem_cons] at hxl ⊢
            rcases hxl with h | h | h
            · exact Or.inl h
            · exact Or.inr (by simp [h])
            · have hp := hafterSorted
              rw [hAB] at hp
              exact absurd ((pairwise_split hp).2 x h) this
        · rw [hAB]; exact ((List.nil_sublist B).cons_cons _).append_left A
      · refine ⟨after, takeUntilIncl_of_not_mem hLa, ?_, List.Sublist.refl _⟩
        intro x
        rw [hcand_simp, hafter]
        constructor
        · intro h
          refine ⟨h, fun hor => ?_⟩
          rcases hor with heq | hp
          · exact absurd heq hne'
          · exact absurd ((hafter _).mpr hp) hLa
        · exact fun h => h.1
    rw [hC]
    have hCsorted := hafterSorted.sublist hCsub
    have hCmem : ∀ x ∈ C, InclusiveDescendant t x (root t w.current) :=
      fun x hx => hafterMem x (hCsub.subset hx)
    cases hf : C.find? (walkerAccepts t w) with
    | none =>
      refine Or.inr ⟨rfl, fun m hm hacc => ?_⟩
      have := find?_none_of_sorted hf m ((hCsub_iff m).mpr hm)
      rw [walkerAccepts_eq, (showsNode_iff t w.whatToShow m).mpr hacc] at this
      cases this
    | some n =>
      obtain ⟨hn, hpn, hfirst⟩ := find?_first_of_sorted hwf hrtd hCmem hCsorted hf
      rw [walkerAccepts_eq] at hpn
      refine Or.inl ⟨n, rfl, ⟨(hCsub_iff n).mp hn, (showsNode_iff t w.whatToShow n).mp hpn⟩, ?_⟩
      rintro m ⟨hm, hacc⟩
      exact hfirst m ((hCsub_iff m).mpr hm)
        (by rw [walkerAccepts_eq]; exact (showsNode_iff t w.whatToShow m).mpr hacc)

/-! ## "traverse children"（first） -/

/-- `preorder t c` の先頭を除いた列は、`c` の strict descendant を tree order に並べたもの。 -/
theorem mem_preorder_drop_one {t : Tree} (hwf : WellFormed t) {c : NodeId} {cd : NodeData}
    (hcd : t.get? c = some cd) (x : NodeId) :
    x ∈ (preorder t c).drop 1 ↔ Ancestor t c x := by
  have hl := treeOrderList_preorder hwf hcd
  obtain ⟨f, hf⟩ : ∃ f, t.size = f + 1 := by
    cases h : t.size with
    | zero =>
      have := (hl.1 c).mpr (Or.inl rfl)
      unfold preorder at this; rw [h] at this; simp [preorderFuel] at this
    | succ f => exact ⟨f, rfl⟩
  have hform : preorder t c = [] ++ c :: (childrenOf t c).flatMap (preorderFuel t f) := by
    unfold preorder; rw [hf, preorderFuel_succ_pos hcd]; rfl
  have hdrop : (preorder t c).drop 1 = (childrenOf t c).flatMap (preorderFuel t f) := by
    rw [hform]; rfl
  rw [hdrop, mem_right_of_split hwf hcd hl hform x, hl.1 x]
  constructor
  · rintro ⟨hxc, hp⟩
    rcases hxc with rfl | h
    · exact absurd hp (precedesStruct_irrefl hwf hcd)
    · exact h
  · intro h
    exact ⟨Or.inr h, Or.inl h⟩

theorem walkerFirstChild_result_sound {t : Tree} (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerFirstChildResult t w (walkerFirstChild t w) := by
  obtain ⟨⟨rootd, hrootd⟩, ⟨cd, hcd⟩⟩ := hw
  have hl := treeOrderList_preorder hwf hcd
  have hLd := lastDescendantOf_lastDescendant hwf hrootd
  have hD := mem_preorder_drop_one hwf hcd
  have hDmem : ∀ x ∈ (preorder t w.current).drop 1, InclusiveDescendant t x w.current :=
    fun x hx => Or.inr ((hD x).mp hx)
  have hDsorted : ((preorder t w.current).drop 1).Pairwise (PrecedesStruct t) :=
    hl.2.sublist (List.drop_sublist _ _)
  obtain ⟨hirr, hasym⟩ := precedesStruct_order_on hwf hcd hDmem
  have hiff : ∀ x, x ∈ cutAtRootExit w.root (lastDescendant t w.root) ((preorder t w.current).drop 1) ↔
      WalkerChildCandidate t w x := by
    intro x
    rw [mem_cutAtRootExit_iff hirr hasym hDsorted, hD, hD]
    unfold WalkerChildCandidate
    constructor
    · rintro ⟨hxc, hn⟩
      refine ⟨hxc, fun L hL hrL hcr => ?_⟩
      rw [lastDescendantOf_unique hwf hrootd hL hLd] at hrL ⊢
      refine hn (fun he => ?_) (hcr.trans_ancestor hrL)
      rw [he] at hrL
      exact ancestor_irrefl hwf _ hrL
    · rintro ⟨hxc, hn⟩
      refine ⟨hxc, fun hne hcL => ?_⟩
      -- root に children がある（`L` が root でない）ので、root は `L` の ancestor である。
      have hrL : Ancestor t w.root (lastDescendant t w.root) := by
        rcases hLd.1 with h | h
        · exact absurd h.symm hne
        · exact h
      -- current と root は、どちらも L の inclusive ancestor なので比べられる。
      have hxroot : Ancestor t w.current w.root ∨ InclusiveDescendant t x w.root := by
        rcases inclusive_ancestor_linear (Or.inr hcL) hLd.1 with h | h
        · rcases h with heq | h
          · exact Or.inr (heq ▸ Or.inr hxc)
          · exact Or.inl h
        · rcases h with heq | h
          · exact Or.inr (heq ▸ Or.inr hxc)
          · exact Or.inr (Or.inr (h.trans_ancestor hxc))
      rcases hxroot with hcr | hxr
      · exact hn _ hLd hrL hcr
      · exact hLd.2 x hxr
  have hsub := cutAtRootExit_sublist w.root (lastDescendant t w.root) ((preorder t w.current).drop 1)
  have hmem' : ∀ x ∈ cutAtRootExit w.root (lastDescendant t w.root) ((preorder t w.current).drop 1),
      InclusiveDescendant t x w.current := fun x hx => hDmem x (hsub.subset hx)
  obtain ⟨hirr', hasym'⟩ := precedesStruct_order_on hwf hcd hmem'
  have := result_of_sorted (t := t) (ws := w.whatToShow) hiff hirr' hasym' (hDsorted.sublist hsub)
  unfold walkerFirstChild WalkerFirstChildResult FirstIn
  rcases this with ⟨n, hf, hn, hfirst⟩ | ⟨hf, hnone⟩
  · exact Or.inl ⟨n, by rw [← hf]; rfl, hn, hfirst⟩
  · exact Or.inr ⟨by rw [← hf]; rfl, hnone⟩

end Dom.Spec
