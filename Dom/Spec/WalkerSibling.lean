import Dom.Spec.WalkerMirror
import Dom.Spec.ValidityOrder
import Dom.Validity.PreserveInsertAt

/-!
# "traverse siblings" の関係仕様（§6.2 `nextSibling()`・`previousSibling()`）

filter は null なので FILTER_REJECT は出ない。本文の loop はこうなる。

* current が root なら null（step 2）。
* 段ごとに、node の後ろ（前）の兄弟を順に見る。兄弟が accept されなければその子へ降り（step 3.2.4）、
  兄弟と子を尽くせば次の兄弟へ進む（step 3.2.5）。降りる途中の node は SKIP されたものばかりなので、
  一つの段で見るのは兄弟の部分木を順に並べたものである。
* 段を尽くしたら parent へ上がる（step 3.3）。parent が null か root なら null、parent が accept されても
  null（step 3.4-3.5）。

だから候補は「current から上がれる inclusive ancestor `a`（`SiblingClimb`）の後ろ（前）の兄弟の inclusive
descendant」で、結果はそのうち accept されるもので tree order（鏡像の tree order）で最初のものである。
-/

namespace Dom.Spec

open Dom

/-- `s` が `a` の後ろの兄弟。 -/
def FollowingSibling (t : Tree) (a s : NodeId) : Prop :=
  ∃ p i j, parentOf t a = some p ∧ parentOf t s = some p ∧ index t a = some i ∧
    index t s = some j ∧ i < j

/-- `s` が `a` の前の兄弟。 -/
def PrecedingSibling (t : Tree) (a s : NodeId) : Prop :=
  ∃ p i j, parentOf t a = some p ∧ parentOf t s = some p ∧ index t a = some i ∧
    index t s = some j ∧ j < i

/--
step 3.3-3.5：current から `a` まで上がれる。current と `a` の間（current を除き `a` を含む）の node は
どれも root でなく、accept されない。
-/
def SiblingClimb (t : Tree) (w : WalkerState) (a : NodeId) : Prop :=
  InclusiveAncestor t a w.current ∧
    ∀ y, Ancestor t y w.current → InclusiveAncestor t a y →
      y ≠ w.root ∧ ¬ Accepts t w.whatToShow y

/-- `nextSibling()` の候補。 -/
def WalkerNextSiblingCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  w.current ≠ w.root ∧
    ∃ a s, SiblingClimb t w a ∧ FollowingSibling t a s ∧ InclusiveAncestor t s x

/-- `previousSibling()` の候補。 -/
def WalkerPreviousSiblingCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  w.current ≠ w.root ∧
    ∃ a s, SiblingClimb t w a ∧ PrecedingSibling t a s ∧ InclusiveAncestor t s x

/-- **§6.2 `nextSibling()` の関係。** 候補のうち accept されるもので tree order で最初のもの。 -/
def WalkerNextSiblingResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧
      FirstIn t (fun x => WalkerNextSiblingCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerNextSiblingCandidate t w m → ¬ Accepts t w.whatToShow m)

/--
**§6.2 `previousSibling()` の関係。** 候補のうち accept されるもので、鏡像の tree order（前の兄弟を近い
ほうから見て、降りるときは最後の子へ降りる順）で最初のもの。
-/
def WalkerPreviousSiblingResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧
      MirrorFirstIn t (fun x => WalkerPreviousSiblingCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerPreviousSiblingCandidate t w m → ¬ Accepts t w.whatToShow m)

/-! ## 後ろの兄弟 -/

variable {t : Tree}

theorem mem_followingSiblings (hwf : WellFormed t) (n s : NodeId) :
    s ∈ followingSiblings t n ↔ FollowingSibling t n s := by
  unfold followingSiblings
  cases hp : parentOf t n with
  | none =>
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨p, -, -, hp', -⟩
    rw [hp] at hp'; cases hp'
  | some p =>
  simp only []
  have hmem : n ∈ childrenOf t p := (mem_childrenOf_iff hwf n p).mp hp
  obtain ⟨A, B, hsp⟩ := ListUtil.exists_splitAt?_of_mem hmem
  have hAB := ListUtil.splitAt?_eq_some hsp
  have hnA := ListUtil.splitAt?_not_mem_left hsp
  rw [hsp]
  simp only []
  constructor
  · intro hs
    have hsc : s ∈ childrenOf t p := by rw [hAB]; simp [hs]
    have hsp' := (mem_childrenOf_iff hwf s p).mpr hsc
    obtain ⟨i, j, hi, hj, hij⟩ := index_lt_of_mem_right hwf hAB hnA hs hp hsp'
    exact ⟨p, i, j, hp, hsp', hi, hj, hij⟩
  · rintro ⟨p', i, j, hp', hsp', hi, hj, hij⟩
    rw [hp] at hp'
    cases hp'
    have hsc : s ∈ childrenOf t p := (mem_childrenOf_iff hwf s p).mp hsp'
    rw [hAB] at hsc
    simp only [List.mem_append, List.mem_cons] at hsc
    rcases hsc with hsA | rfl | hsB
    · obtain ⟨i', j', hi', hj', hlt⟩ := index_lt_of_mem_left hwf hAB hnA hsA hp hsp'
      rw [hi'] at hj; rw [hj'] at hi; cases hj; cases hi
      omega
    · rw [hi] at hj; cases hj; omega
    · exact hsB

theorem mem_siblingCandidates (hwf : WellFormed t) (n x : NodeId) :
    x ∈ siblingCandidates t n true ↔ ∃ s, FollowingSibling t n s ∧ InclusiveAncestor t s x := by
  simp only [siblingCandidates, if_true, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hx⟩
    have hfs := (mem_followingSiblings hwf n s).mp hs
    have hfs' := hfs
    obtain ⟨p, -, -, -, hsp, -⟩ := hfs'
    obtain ⟨sd, hsd, -⟩ := parentOf_eq_some hsp
    exact ⟨s, hfs, (mem_preorder_iff hwf hsd x).mp hx⟩
  · intro h
    obtain ⟨s, hfs, hx⟩ := h
    have hfs' := hfs
    obtain ⟨p, -, -, -, hsp, -⟩ := hfs'
    obtain ⟨sd, hsd, -⟩ := parentOf_eq_some hsp
    exact ⟨s, (mem_followingSiblings hwf n s).mpr hfs, (mem_preorder_iff hwf hsd x).mpr hx⟩

/-! ## 段ごとの候補を並べた列 -/

/-- 実行関数 `walkerSiblingSearch` が見る候補を、止まる所まで順に並べた列（証明の道具）。 -/
def sibLevels (t : Tree) (w : WalkerState) : List NodeId → List NodeId
  | [] => []
  | [n] => siblingCandidates t n true
  | n :: p :: rest =>
    siblingCandidates t n true ++
      (if p == w.root || walkerAccepts t w p then [] else sibLevels t w (p :: rest))

theorem walkerSiblingSearch_eq (w : WalkerState) :
    ∀ l : List NodeId, walkerSiblingSearch t w true l = (sibLevels t w l).find? (walkerAccepts t w)
  | [] => rfl
  | [n] => rfl
  | n :: p :: rest => by
    simp only [walkerSiblingSearch, sibLevels, List.find?_append]
    cases (siblingCandidates t n true).find? (walkerAccepts t w) with
    | some x => rfl
    | none =>
      simp only [Option.none_or]
      split
      · rfl
      · exact walkerSiblingSearch_eq w (p :: rest)

/-- `n` から上がっていく段の候補。 -/
def CandFrom (t : Tree) (w : WalkerState) (n x : NodeId) : Prop :=
  ∃ a s, InclusiveAncestor t a n ∧
    (∀ y, Ancestor t y n → InclusiveAncestor t a y → y ≠ w.root ∧ ¬ Accepts t w.whatToShow y) ∧
    FollowingSibling t a s ∧ InclusiveAncestor t s x

theorem stop_iff (w : WalkerState) (p : NodeId) :
    (p == w.root || walkerAccepts t w p) = true ↔ (p = w.root ∨ Accepts t w.whatToShow p) := by
  rw [Bool.or_eq_true, beq_iff_eq, walkerAccepts_eq, showsNode_iff]

theorem mem_sibLevels (hwf : WellFormed t) (w : WalkerState) (x : NodeId) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k →
      (x ∈ sibLevels t w (n :: ancestors t n) ↔ CandFrom t w n x) := by
  intro k
  induction k with
  | zero =>
    intro n hlen
    have hnil : ancestors t n = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil]
    simp only [sibLevels]
    rw [mem_siblingCandidates hwf]
    constructor
    · rintro ⟨s, hfs, hx⟩
      refine ⟨n, s, Or.inl rfl, fun y hy hny => ?_, hfs, hx⟩
      exfalso
      rcases hny with rfl | h
      · exact ancestor_irrefl hwf _ hy
      · exact ancestor_asymm hwf h hy
    · rintro ⟨a, s, ha, -, hfs, hx⟩
      rcases ha with rfl | ha
      · exact ⟨s, hfs, hx⟩
      · obtain ⟨p, hp, -⟩ := ha.cases_parent
        rw [ancestors_eq_cons hwf hp] at hnil
        cases hnil
  | succ k ih =>
    intro n hlen
    cases hp : parentOf t n with
    | none =>
      have hnil : ancestors t n = [] := by
        unfold ancestors
        cases t.size with
        | zero => rfl
        | succ f => exact ancestorChain_succ_none hp
      rw [hnil]
      simp only [sibLevels]
      rw [mem_siblingCandidates hwf]
      constructor
      · rintro ⟨s, hfs, hx⟩
        refine ⟨n, s, Or.inl rfl, fun y hy hny => ?_, hfs, hx⟩
        obtain ⟨q, hq, -⟩ := hy.cases_parent
        rw [hp] at hq; cases hq
      · rintro ⟨a, s, ha, -, hfs, hx⟩
        rcases ha with rfl | ha
        · exact ⟨s, hfs, hx⟩
        · obtain ⟨q, hq, -⟩ := ha.cases_parent
          rw [hp] at hq; cases hq
    | some p =>
      rw [ancestors_eq_cons hwf hp] at hlen ⊢
      simp only [List.length_cons] at hlen
      simp only [sibLevels, List.mem_append]
      rw [mem_siblingCandidates hwf]
      have hrec := ih p (by omega)
      constructor
      · rintro (⟨s, hfs, hx⟩ | hx)
        · refine ⟨n, s, Or.inl rfl, fun y hy hny => ?_, hfs, hx⟩
          exfalso
          rcases hny with rfl | h
          · exact ancestor_irrefl hwf _ hy
          · exact ancestor_asymm hwf h hy
        · split at hx
          · simp at hx
          · next hstop =>
            obtain ⟨a, s, ha, hcl, hfs, hxs⟩ := hrec.mp hx
            refine ⟨a, s, Or.inr (Ancestor.of_parent_inclusive hp ha), fun y hy hay => ?_, hfs, hxs⟩
            obtain ⟨q, hq, hcase⟩ := hy.cases_parent
            rw [hp] at hq; cases hq
            rcases hcase with rfl | hyp
            · have := (not_congr (stop_iff w y)).mp hstop
              exact ⟨fun he => this (Or.inl he), fun ha' => this (Or.inr ha')⟩
            · exact hcl y hyp hay
      · rintro ⟨a, s, ha, hcl, hfs, hxs⟩
        rcases ha with rfl | ha
        · exact Or.inl ⟨s, hfs, hxs⟩
        · right
          have hap : InclusiveAncestor t a p := inclusiveAncestor_of_ancestor_parent ha hp
          have hpn : Ancestor t p n := Ancestor.step hp
          have hstop : ¬ (p == w.root || walkerAccepts t w p) = true := by
            rw [stop_iff]
            obtain ⟨h1, h2⟩ := hcl p hpn hap
            rintro (h | h)
            · exact h1 h
            · exact h2 h
          rw [if_neg hstop]
          refine hrec.mpr ⟨a, s, hap, fun y hy hay => hcl y (hy.trans_ancestor hpn) hay, hfs, hxs⟩

/-! ## 列は tree order に整列している -/

theorem pairwise_of_split {α : Type} {R : α → α → Prop} :
    ∀ (l : List α), (∀ L₁ a L₂ b, l = L₁ ++ a :: L₂ → b ∈ L₂ → R a b) → l.Pairwise R
  | [], _ => .nil
  | x :: xs, h => .cons (fun b hb => h [] x xs b rfl hb)
      (pairwise_of_split xs fun L₁ a L₂ b he hb => h (x :: L₁) a L₂ b (by rw [he]; rfl) hb)

theorem followingSiblings_pairwise (hwf : WellFormed t) (n : NodeId) :
    (followingSiblings t n).Pairwise (FollowingSibling t) := by
  unfold followingSiblings
  cases hp : parentOf t n with
  | none => exact .nil
  | some p =>
  simp only []
  have hmem : n ∈ childrenOf t p := (mem_childrenOf_iff hwf n p).mp hp
  obtain ⟨A, B, hsp⟩ := ListUtil.exists_splitAt?_of_mem hmem
  have hAB := ListUtil.splitAt?_eq_some hsp
  rw [hsp]
  simp only []
  refine pairwise_of_split B fun L₁ a L₂ b he hb => ?_
  have hL : childrenOf t p = (A ++ n :: L₁) ++ a :: L₂ := by rw [hAB, he]; simp
  have hnd := childrenOf_nodup hwf p
  rw [hL] at hnd
  have hna : a ∉ A ++ n :: L₁ := fun hm =>
    (List.nodup_append.mp hnd).2.2 a hm a (List.mem_cons_self ..) rfl
  have hap : parentOf t a = some p := (mem_childrenOf_iff hwf a p).mpr (by rw [hL]; simp)
  have hbp : parentOf t b = some p := (mem_childrenOf_iff hwf b p).mpr (by rw [hL]; simp [hb])
  obtain ⟨i, j, hi, hj, hij⟩ := index_lt_of_mem_right hwf hL hna hb hap hbp
  exact ⟨p, i, j, hap, hbp, hi, hj, hij⟩

/-- 前の兄弟の部分木にいる node は、後ろの兄弟の部分木にいる node に先行する。 -/
theorem precedesStruct_of_followingSibling {a s x y : NodeId} (hfs : FollowingSibling t a s)
    (hx : InclusiveAncestor t a x) (hy : InclusiveAncestor t s y) : PrecedesStruct t x y := by
  obtain ⟨p, i, j, hap, hsp, hi, hj, hij⟩ := hfs
  exact Or.inr ⟨p, a, s, i, j, hap, hsp, hi, hj, hij, hx, hy⟩

theorem siblingCandidates_pairwise (hwf : WellFormed t) (n : NodeId) :
    (siblingCandidates t n true).Pairwise (PrecedesStruct t) := by
  simp only [siblingCandidates, if_true]
  refine List.pairwise_flatMap.mpr ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨p, -, -, -, hsp, -⟩ := (mem_followingSiblings hwf n s).mp hs
    obtain ⟨sd, hsd, -⟩ := parentOf_eq_some hsp
    exact (treeOrderList_preorder hwf hsd).2
  · refine (followingSiblings_pairwise hwf n).imp_of_mem fun {s₁ s₂} hs₁ hs₂ hfs x hx y hy => ?_
    obtain ⟨p₁, -, -, -, hsp₁, -⟩ := (mem_followingSiblings hwf n s₁).mp hs₁
    obtain ⟨p₂, -, -, -, hsp₂, -⟩ := (mem_followingSiblings hwf n s₂).mp hs₂
    obtain ⟨sd₁, hsd₁, -⟩ := parentOf_eq_some hsp₁
    obtain ⟨sd₂, hsd₂, -⟩ := parentOf_eq_some hsp₂
    exact precedesStruct_of_followingSibling hfs ((mem_preorder_iff hwf hsd₁ x).mp hx)
      ((mem_preorder_iff hwf hsd₂ y).mp hy)

theorem sibLevels_pairwise (hwf : WellFormed t) (w : WalkerState) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k →
      (sibLevels t w (n :: ancestors t n)).Pairwise (PrecedesStruct t) := by
  intro k
  induction k with
  | zero =>
    intro n hlen
    have hnil : ancestors t n = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil]
    exact siblingCandidates_pairwise hwf n
  | succ k ih =>
    intro n hlen
    cases hp : parentOf t n with
    | none =>
      have hnil : ancestors t n = [] := by
        unfold ancestors
        cases t.size with
        | zero => rfl
        | succ f => exact ancestorChain_succ_none hp
      rw [hnil]
      exact siblingCandidates_pairwise hwf n
    | some p =>
      rw [ancestors_eq_cons hwf hp] at hlen ⊢
      simp only [List.length_cons] at hlen
      simp only [sibLevels]
      refine List.pairwise_append.mpr ⟨siblingCandidates_pairwise hwf n, ?_, ?_⟩
      · split
        · exact .nil
        · exact ih p (by omega)
      · intro x hx y hy
        split at hy
        · simp at hy
        · obtain ⟨s, hfs, hxs⟩ := (mem_siblingCandidates hwf n x).mp hx
          obtain ⟨a, s', hap, -, hfs', hys'⟩ := (mem_sibLevels hwf w y k p (by omega)).mp hy
          -- a は p の inclusive ancestor で、p は s の parent なので、a は x の ancestor である。
          have hfs₀ := hfs
          obtain ⟨q, -, -, hnq, hsq, -⟩ := hfs₀
          have hqp : q = p := by rw [hp] at hnq; exact (Option.some.inj hnq).symm
          subst hqp
          have hpx : Ancestor t q x := by
            rcases hxs with rfl | h
            · exact Ancestor.step hsq
            · exact (Ancestor.step hsq).trans_ancestor h
          have hax : InclusiveAncestor t a x := by
            rcases hap with rfl | h
            · exact Or.inr hpx
            · exact Or.inr (h.trans_ancestor hpx)
          exact precedesStruct_of_followingSibling hfs' hax hys'

/-! ## `nextSibling()` -/

theorem candFrom_iff {w : WalkerState} {x : NodeId} :
    (w.current ≠ w.root ∧ CandFrom t w w.current x) ↔ WalkerNextSiblingCandidate t w x := by
  unfold CandFrom WalkerNextSiblingCandidate SiblingClimb
  constructor
  · rintro ⟨hne, a, s, ha, hcl, hfs, hx⟩; exact ⟨hne, a, s, ⟨ha, hcl⟩, hfs, hx⟩
  · rintro ⟨hne, a, s, ⟨ha, hcl⟩, hfs, hx⟩; exact ⟨hne, a, s, ha, hcl, hfs, hx⟩

/-- **`nextSibling()` は関係を満たす。** -/
theorem walkerNextSibling_result_sound (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerNextSiblingResult t w (walkerSibling t w true) := by
  obtain ⟨-, ⟨cd, hcd⟩⟩ := hw
  unfold walkerSibling
  by_cases hcr : w.current = w.root
  · rw [if_pos (by simp [hcr])]
    exact Or.inr ⟨rfl, fun m hm => absurd hcr hm.1⟩
  rw [if_neg (by simpa using hcr), walkerSiblingSearch_eq]
  have hiff : ∀ x, x ∈ sibLevels t w (w.current :: ancestors t w.current) ↔
      WalkerNextSiblingCandidate t w x := by
    intro x
    rw [mem_sibLevels hwf w x _ w.current (Nat.le_refl _), ← candFrom_iff]
    exact ⟨fun h => ⟨hcr, h⟩, fun h => h.2⟩
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hcd
  have hmem : ∀ x ∈ sibLevels t w (w.current :: ancestors t w.current),
      InclusiveDescendant t x (root t w.current) := by
    intro x hx
    obtain ⟨-, a, s, ⟨ha, -⟩, ⟨q, -, -, haq, hsq, -⟩, hxs⟩ := (hiff x).mp hx
    have hqx : Ancestor t q x := by
      rcases hxs with rfl | h
      · exact Ancestor.step hsq
      · exact (Ancestor.step hsq).trans_ancestor h
    have hqc : Ancestor t q w.current := by
      rcases ha with rfl | h
      · exact Ancestor.step haq
      · exact (Ancestor.step haq).trans_ancestor h
    have e : root t x = root t w.current := by
      rw [root_eq_of_ancestor hwf hqx, root_eq_of_ancestor hwf hqc]
    rw [← e]
    exact root_inclusive_ancestor t x
  obtain ⟨hirr, hasym⟩ := precedesStruct_order_on hwf hrd hmem
  have := result_of_sorted (t := t) (ws := w.whatToShow) hiff hirr hasym
    (sibLevels_pairwise hwf w _ w.current (Nat.le_refl _))
  unfold WalkerNextSiblingResult FirstIn
  rcases this with ⟨n, hf, hn, hfirst⟩ | ⟨hf, hnone⟩
  · exact Or.inl ⟨n, by rw [← hf]; rfl, hn, hfirst⟩
  · exact Or.inr ⟨by rw [← hf]; rfl, hnone⟩

/-! ## `previousSibling()`：反転した木の `nextSibling()` -/

theorem ancestors_mirrorTree (n : NodeId) : ancestors (mirrorTree t) n = ancestors t n := by
  unfold ancestors
  rw [size_mirrorTree]
  generalize t.size = f
  induction f generalizing n with
  | zero => rfl
  | succ f ih =>
    simp only [ancestorChain, parentOf_mirrorTree]
    split
    · rfl
    · rw [ih]

theorem followingSiblings_mirrorTree (hwf : WellFormed t) (n : NodeId) :
    followingSiblings (mirrorTree t) n = precedingSiblings t n := by
  unfold followingSiblings precedingSiblings
  rw [parentOf_mirrorTree]
  cases hp : parentOf t n with
  | none => rfl
  | some p =>
    simp only []
    have hmem : n ∈ childrenOf t p := (mem_childrenOf_iff hwf n p).mp hp
    obtain ⟨A, B, hsp⟩ := ListUtil.exists_splitAt?_of_mem hmem
    have hAB := ListUtil.splitAt?_eq_some hsp
    have hm : childrenOf (mirrorTree t) p = B.reverse ++ n :: A.reverse := by
      rw [childrenOf_mirrorTree, hAB]; simp
    rw [hsp, splitAt?_childrenOf_of_split (wellFormed_mirrorTree hwf) hm]

theorem siblingCandidates_mirrorTree (hwf : WellFormed t) (n : NodeId) :
    siblingCandidates (mirrorTree t) n true = siblingCandidates t n false := by
  simp only [siblingCandidates, if_true, Bool.false_eq_true, if_false,
    followingSiblings_mirrorTree hwf, preorder_mirrorTree]

theorem walkerSiblingSearch_mirrorTree (hwf : WellFormed t) (w : WalkerState) :
    ∀ l : List NodeId, walkerSiblingSearch (mirrorTree t) w true l = walkerSiblingSearch t w false l
  | [] => rfl
  | [n] => by
    simp only [walkerSiblingSearch, siblingCandidates_mirrorTree hwf]
    congr 1; funext x; rw [walkerAccepts_mirrorTree]
  | n :: p :: rest => by
    have hacc : walkerAccepts (mirrorTree t) w = walkerAccepts t w := by
      funext x; rw [walkerAccepts_mirrorTree]
    simp only [walkerSiblingSearch, siblingCandidates_mirrorTree hwf, hacc]
    rw [walkerSiblingSearch_mirrorTree hwf w (p :: rest)]

theorem walkerPreviousSibling_eq (hwf : WellFormed t) (w : WalkerState) :
    walkerSibling t w false = walkerSibling (mirrorTree t) w true := by
  unfold walkerSibling
  rw [ancestors_mirrorTree, walkerSiblingSearch_mirrorTree hwf]

theorem followingSibling_mirrorTree_iff (hwf : WellFormed t) {a s : NodeId} :
    FollowingSibling (mirrorTree t) a s ↔ PrecedingSibling t a s := by
  unfold FollowingSibling PrecedingSibling
  constructor
  · rintro ⟨p, i, j, hap, hsp, hi, hj, hij⟩
    rw [parentOf_mirrorTree] at hap hsp
    obtain ⟨i₀, hi₀⟩ := index_isSome hwf hap
    obtain ⟨j₀, hj₀⟩ := index_isSome hwf hsp
    have := index_lt_children_length hap hi₀
    have := index_lt_children_length hsp hj₀
    rw [index_mirrorTree hwf hap hi₀] at hi
    rw [index_mirrorTree hwf hsp hj₀] at hj
    cases hi; cases hj
    exact ⟨p, i₀, j₀, hap, hsp, hi₀, hj₀, by omega⟩
  · rintro ⟨p, i, j, hap, hsp, hi, hj, hji⟩
    have := index_lt_children_length hap hi
    have := index_lt_children_length hsp hj
    exact ⟨p, _, _, by simpa using hap, by simpa using hsp, index_mirrorTree hwf hap hi,
      index_mirrorTree hwf hsp hj, by omega⟩

theorem nextSiblingCandidate_mirrorTree_iff (hwf : WellFormed t) {w : WalkerState} {x : NodeId} :
    WalkerNextSiblingCandidate (mirrorTree t) w x ↔ WalkerPreviousSiblingCandidate t w x := by
  unfold WalkerNextSiblingCandidate WalkerPreviousSiblingCandidate SiblingClimb
  simp only [inclusiveAncestor_mirrorTree_iff, ancestor_mirrorTree_iff, accepts_mirrorTree_iff,
    followingSibling_mirrorTree_iff hwf]

/-- **`previousSibling()` は関係を満たす。** `nextSibling()` を、子の列を反転した木で走らせたものである。 -/
theorem walkerPreviousSibling_result_sound (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerPreviousSiblingResult t w (walkerSibling t w false) := by
  have h := walkerNextSibling_result_sound (wellFormed_mirrorTree hwf) (validWalker_mirrorTree hw)
  rw [← walkerPreviousSibling_eq hwf] at h
  unfold WalkerNextSiblingResult FirstIn at h
  unfold WalkerPreviousSiblingResult MirrorFirstIn
  simp only [nextSiblingCandidate_mirrorTree_iff hwf, accepts_mirrorTree_iff,
    precedesStruct_mirrorTree_iff hwf] at h
  exact h

end Dom.Spec
