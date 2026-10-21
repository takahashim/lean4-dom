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
* inner loop は兄弟の次の兄弟が無いところで抜け、parent へ上がる（step 3.3）。parent が null か root なら null、
  parent が accept されれば null（step 3.4-3.5）。兄弟の部分木の中から上がるときも同じ検査を通るが、そこで
  上がる先は SKIP された node なので、効くのは step 3.4 の「root なら null」だけである。

だから候補は「current から上がれる inclusive ancestor `a`（`SiblingClimb`）の後ろ（前）の兄弟の inclusive
descendant」で、ただし root がそのような兄弟 `s` の部分木の中にあって children を持つなら、root の最後の
inclusive descendant（鏡像なら鏡像の順序で最後のもの）より後ろは候補でない（root へ親として上がって止まる）。
結果はそのうち accept されるもので tree order（鏡像の tree order）で最初のものである。

`previousNode()` の soundness も、前の兄弟の列の補題（`mem_precedingSiblings`）を使うのでここに置く。
-/

namespace Dom.Spec

open Dom

/--
step 3.3-3.5：current から `a` まで上がれる。current と `a` の間（current を除き `a` を含む）の node は
どれも root でなく、accept されない。
-/
def SiblingClimb (t : Tree) (w : WalkerState) (a : NodeId) : Prop :=
  InclusiveAncestor t a w.current ∧
    ∀ y, Ancestor t y w.current → InclusiveAncestor t a y →
      y ≠ w.root ∧ ¬ Accepts t w.whatToShow y

/--
`nextSibling()` の候補。current が root なら無い（step 2）。上がれる `a` の後ろの兄弟 `s` の部分木にあり、
root が兄弟 `s` の部分木の中にあって children を持つなら、root の最後の inclusive descendant `L` より後ろでない
（`L` を見終えて root へ親として上がると step 3.4 で null）。
-/
def WalkerNextSiblingCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  w.current ≠ w.root ∧
    (∃ a s, SiblingClimb t w a ∧ FollowingSibling t a s ∧ InclusiveAncestor t s x) ∧
    ∀ a s L, SiblingClimb t w a → FollowingSibling t a s → InclusiveAncestor t s w.root →
      LastDescendantOf t w.root L → Ancestor t w.root L → ¬ PrecedesStruct t L x

/-- `previousSibling()` の候補。`nextSibling()` の鏡像。 -/
def WalkerPreviousSiblingCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  w.current ≠ w.root ∧
    (∃ a s, SiblingClimb t w a ∧ PrecedingSibling t a s ∧ InclusiveAncestor t s x) ∧
    ∀ a s L, SiblingClimb t w a → PrecedingSibling t a s → InclusiveAncestor t s w.root →
      MirrorLastDescendantOf t w.root L → Ancestor t w.root L → ¬ MirrorPrecedes t L x

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

/-- `n` から上がっていく段の候補。 -/
def CandFrom (t : Tree) (w : WalkerState) (n x : NodeId) : Prop :=
  ∃ a s, InclusiveAncestor t a n ∧
    (∀ y, Ancestor t y n → InclusiveAncestor t a y → y ≠ w.root ∧ ¬ Accepts t w.whatToShow y) ∧
    FollowingSibling t a s ∧ InclusiveAncestor t s x

theorem stop_iff (w : WalkerState) (p : NodeId) :
    (p == w.root || walkerAccepts t w p) = true ↔ (p = w.root ∨ Accepts t w.whatToShow p) := by
  rw [Bool.or_eq_true, beq_iff_eq, walkerAccepts_eq, showsNode_iff]

theorem mem_siblingLevels (hwf : WellFormed t) (w : WalkerState) (x : NodeId) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k →
      (x ∈ siblingLevels t w true (n :: ancestors t n) ↔ CandFrom t w n x) := by
  intro k
  induction k with
  | zero =>
    intro n hlen
    have hnil : ancestors t n = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil]
    simp only [siblingLevels]
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
      simp only [siblingLevels]
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
      simp only [siblingLevels, List.mem_append]
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

theorem siblingLevels_pairwise (hwf : WellFormed t) (w : WalkerState) :
    ∀ (k : Nat) (n : NodeId), (ancestors t n).length ≤ k →
      (siblingLevels t w true (n :: ancestors t n)).Pairwise (PrecedesStruct t) := by
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
      simp only [siblingLevels]
      refine List.pairwise_append.mpr ⟨siblingCandidates_pairwise hwf n, ?_, ?_⟩
      · split
        · exact .nil
        · exact ih p (by omega)
      · intro x hx y hy
        split at hy
        · simp at hy
        · obtain ⟨s, hfs, hxs⟩ := (mem_siblingCandidates hwf n x).mp hx
          obtain ⟨a, s', hap, -, hfs', hys'⟩ := (mem_siblingLevels hwf w y k p (by omega)).mp hy
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

/-- 段ごとの列の要素は、上がれる `a` の後ろの兄弟の部分木にあるもの。 -/
theorem mem_siblingLevels_current (hwf : WellFormed t) (w : WalkerState) (x : NodeId) :
    x ∈ siblingLevels t w true (w.current :: ancestors t w.current) ↔
      ∃ a s, SiblingClimb t w a ∧ FollowingSibling t a s ∧ InclusiveAncestor t s x := by
  rw [mem_siblingLevels hwf w x _ w.current (Nat.le_refl _)]
  unfold CandFrom SiblingClimb
  constructor
  · rintro ⟨a, s, ha, hcl, hfs, hx⟩; exact ⟨a, s, ⟨ha, hcl⟩, hfs, hx⟩
  · rintro ⟨a, s, ⟨ha, hcl⟩, hfs, hx⟩; exact ⟨a, s, ha, hcl, hfs, hx⟩

/--
root が上がれる `a` の兄弟 `s` より上にあるなら、段ごとの列の node はどれも root の子孫である。
（root は current の ancestor で、上がる途中で root に当たれば止まるので、`a'` はどれも root の下にある。）
-/
theorem ancestor_root_of_climb {w : WalkerState} {a s x : NodeId}
    (hcl : SiblingClimb t w a) (hfs : FollowingSibling t a s) (hrs : Ancestor t w.root s)
    (hx : ∃ a' s', SiblingClimb t w a' ∧ FollowingSibling t a' s' ∧ InclusiveAncestor t s' x) :
    Ancestor t w.root x := by
  obtain ⟨p, -, -, hap, hsp, -⟩ := hfs
  have hrp : InclusiveAncestor t w.root p := inclusiveAncestor_of_ancestor_parent hrs hsp
  have hra : Ancestor t w.root a := Ancestor.of_parent_inclusive hap hrp
  have hrc : Ancestor t w.root w.current := by
    rcases hcl.1 with heq | h
    · exact heq ▸ hra
    · exact hra.trans_ancestor h
  obtain ⟨a', s', hcl', ⟨p', -, -, hap', hsp', -⟩, hxs'⟩ := hx
  have hra' : Ancestor t w.root a' := by
    rcases inclusive_ancestor_linear hcl'.1 (Or.inr hrc) with h | h
    · exact absurd rfl (hcl'.2 w.root hrc h).1
    · rcases h with heq | h
      · exact absurd rfl (hcl'.2 w.root hrc (Or.inl heq.symm)).1
      · exact h
  have hrs' : Ancestor t w.root s' :=
    Ancestor.of_parent_inclusive hsp' (inclusiveAncestor_of_ancestor_parent hra' hap')
  rcases hxs' with rfl | h
  · exact hrs'
  · exact hrs'.trans_ancestor h

/-- **`nextSibling()` は関係を満たす。** -/
theorem walkerNextSibling_result_sound (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerNextSiblingResult t w (walkerSibling t w true) := by
  obtain ⟨⟨rootd, hrootd⟩, ⟨cd, hcd⟩⟩ := hw
  unfold walkerSibling
  by_cases hcr : w.current = w.root
  · rw [if_pos (by simp [hcr])]
    exact Or.inr ⟨rfl, fun m hm => absurd hcr hm.1⟩
  rw [if_neg (by simpa using hcr)]
  simp only [↓reduceIte]
  have hseq := mem_siblingLevels_current hwf w
  have hLd := lastDescendantOf_lastDescendant hwf hrootd
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hcd
  have hmem : ∀ x ∈ siblingLevels t w true (w.current :: ancestors t w.current),
      InclusiveDescendant t x (root t w.current) := by
    intro x hx
    obtain ⟨a, s, ⟨ha, -⟩, ⟨q, -, -, haq, hsq, -⟩, hxs⟩ := (hseq x).mp hx
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
  have hsorted := siblingLevels_pairwise hwf w _ w.current (Nat.le_refl _)
  have hiff : ∀ x, x ∈ cutAtRootExit w.root (lastDescendant t w.root)
      (siblingLevels t w true (w.current :: ancestors t w.current)) ↔
      WalkerNextSiblingCandidate t w x := by
    intro x
    rw [mem_cutAtRootExit_iff hirr hasym hsorted]
    unfold WalkerNextSiblingCandidate
    constructor
    · rintro ⟨hx, hcut⟩
      refine ⟨hcr, (hseq x).mp hx, fun a s L hcl hfs hsr hL hrL => ?_⟩
      rw [lastDescendantOf_unique hwf hrootd hL hLd] at hrL ⊢
      refine hcut (fun he => ?_) ((hseq _).mpr ⟨a, s, hcl, hfs, ?_⟩)
      · rw [he] at hrL
        exact ancestor_irrefl hwf _ hrL
      · rcases hsr with heq | h
        · exact Or.inr (heq ▸ hrL)
        · exact Or.inr (h.trans_ancestor hrL)
    · rintro ⟨-, hx, hstop⟩
      refine ⟨(hseq x).mpr hx, fun hne hLs => ?_⟩
      -- root に children がある（`L` が root でない）ので、root は `L` の ancestor である。
      have hrL : Ancestor t w.root (lastDescendant t w.root) := by
        rcases hLd.1 with h | h
        · exact absurd h.symm hne
        · exact h
      obtain ⟨a, s, hcl, hfs, hsL⟩ := (hseq _).mp hLs
      -- `s` と root はどちらも `L` の inclusive ancestor なので比べられる。
      rcases inclusive_ancestor_linear hsL (Or.inr hrL) with hsr | hrs
      · exact hstop a s _ hcl hfs hsr hLd hrL
      · rcases hrs with heq | hrs
        · exact hstop a s _ hcl hfs (Or.inl heq.symm) hLd hrL
        · exact hLd.2 x (Or.inr (ancestor_root_of_climb hcl hfs hrs hx))
  have hsub := cutAtRootExit_sublist w.root (lastDescendant t w.root)
    (siblingLevels t w true (w.current :: ancestors t w.current))
  have hmem' : ∀ x ∈ cutAtRootExit w.root (lastDescendant t w.root)
      (siblingLevels t w true (w.current :: ancestors t w.current)),
      InclusiveDescendant t x (root t w.current) := fun x hx => hmem x (hsub.subset hx)
  obtain ⟨hirr', hasym'⟩ := precedesStruct_order_on hwf hrd hmem'
  have := result_of_sorted (t := t) (ws := w.whatToShow) hiff hirr' hasym' (hsorted.sublist hsub)
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

theorem siblingLevels_mirrorTree (hwf : WellFormed t) (w : WalkerState) :
    ∀ l : List NodeId, siblingLevels (mirrorTree t) w true l = siblingLevels t w false l
  | [] => rfl
  | [n] => by simp only [siblingLevels, siblingCandidates_mirrorTree hwf]
  | n :: p :: rest => by
    have hacc : walkerAccepts (mirrorTree t) w = walkerAccepts t w := by
      funext x; rw [walkerAccepts_mirrorTree]
    simp only [siblingLevels, siblingCandidates_mirrorTree hwf, hacc,
      siblingLevels_mirrorTree hwf w (p :: rest)]

theorem walkerPreviousSibling_eq (hwf : WellFormed t) (w : WalkerState) :
    walkerSibling t w false = walkerSibling (mirrorTree t) w true := by
  have hacc : walkerAccepts (mirrorTree t) w = walkerAccepts t w := by
    funext x; rw [walkerAccepts_mirrorTree]
  unfold walkerSibling
  simp only [ancestors_mirrorTree, siblingLevels_mirrorTree hwf, lastDescendant_mirrorTree, hacc,
    ↓reduceIte, Bool.false_eq_true]

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
    followingSibling_mirrorTree_iff hwf, lastDescendantOf_mirrorTree_iff hwf,
    precedesStruct_mirrorTree_iff hwf]

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

/-! ## `previousNode()` -/

theorem mem_precedingSiblings (hwf : WellFormed t) (n s : NodeId) :
    s ∈ precedingSiblings t n ↔ PrecedingSibling t n s := by
  rw [← followingSiblings_mirrorTree hwf, mem_followingSiblings (wellFormed_mirrorTree hwf),
    followingSibling_mirrorTree_iff hwf]

/-- `previousStopsAtRoot` は `PreviousStopsAtRoot` を決定する。 -/
theorem previousStopsAtRoot_iff (hwf : WellFormed t) (r : NodeId) :
    previousStopsAtRoot t r = true ↔ PreviousStopsAtRoot t r := by
  unfold previousStopsAtRoot PreviousStopsAtRoot
  cases hc : childrenOf t r with
  | cons y ys =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_or, true_iff]
    exact Or.inl ⟨y, (mem_childrenOf_iff hwf y r).mpr (by rw [hc]; simp)⟩
  | nil =>
    have hno : ¬ ∃ y, parentOf t y = some r := fun ⟨y, hy⟩ => by
      have := (mem_childrenOf_iff hwf y r).mp hy
      rw [hc] at this
      simp at this
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, hno, false_or]
    cases hp : precedingSiblings t r with
    | nil =>
      simp only [List.isEmpty_nil, true_iff]
      rintro ⟨s, hs⟩
      have := (mem_precedingSiblings hwf r s).mpr hs
      rw [hp] at this
      simp at this
    | cons s ss =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, false_iff]
      exact fun h => h ⟨s, (mem_precedingSiblings hwf r s).mp (by rw [hp]; simp)⟩

/-- **`previousNode()` は関係を満たす。** -/
theorem walkerPreviousNode_result_sound (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerPreviousNodeResult t w (walkerPreviousNode t w) := by
  obtain ⟨⟨rootd, hrootd⟩, ⟨cd, hcd⟩⟩ := hw
  obtain ⟨rtd, hrtd⟩ := exists_data_root hwf hcd
  have hl := treeOrderList_preorder hwf hrtd
  have hc : w.current ∈ preorder t (root t w.current) :=
    (hl.1 _).mpr (root_inclusive_ancestor t w.current)
  unfold walkerPreviousNode
  split
  · next heq =>
    have heq' : w.current = w.root := by simpa using heq
    exact Or.inr ⟨rfl, fun m hm _ => hm.1 heq'⟩
  · next hne =>
    have hne' : w.current ≠ w.root := by simpa using hne
    unfold treeOrder
    obtain ⟨X, after, hsp⟩ := ListUtil.exists_splitAt?_of_mem hc
    have hsplit := ListUtil.splitAt?_eq_some hsp
    rw [hsp]
    simp only
    have hX : ∀ x, x ∈ X.reverse ↔ PrecedesStruct t x w.current := by
      intro x
      rw [List.mem_reverse, mem_left_of_split hwf hrtd hl hsplit x]
      exact ⟨fun h => h.2, fun h => ⟨(hl.1 x).mpr (precedesStruct_root_left hwf h), h⟩⟩
    have hXmem : ∀ x ∈ X.reverse, InclusiveDescendant t x (root t w.current) := fun x hx =>
      (hl.1 x).mp (by rw [hsplit]; simp [List.mem_reverse.mp hx])
    have hXsorted : X.reverse.Pairwise (fun a b => PrecedesStruct t b a) := by
      have hp := hl.2
      rw [hsplit, List.pairwise_append] at hp
      exact List.pairwise_reverse.mpr hp.1
    obtain ⟨hirr, hasym⟩ := precedesStruct_order_on hwf hrtd hXmem
    -- 候補の列：root で止まるなら root までで切り、止まらなければ切らない。
    obtain ⟨C, hC, hiff, hsub⟩ : ∃ C, (if previousStopsAtRoot t w.root = true then
        takeUntilIncl (· == w.root) X.reverse else X.reverse) = C ∧
        (∀ x, x ∈ C ↔ WalkerPreviousCandidate t w x) ∧ C.Sublist X.reverse := by
      by_cases hs : previousStopsAtRoot t w.root = true
      · refine ⟨_, if_pos hs, fun x => ?_, takeUntilIncl_sublist _⟩
        have hs' := (previousStopsAtRoot_iff hwf _).mp hs
        rw [mem_takeUntilIncl_iff (R := fun a b => PrecedesStruct t b a) hirr
          (fun a ha b hb h => hasym b hb a ha h) hXsorted, hX, hX]
        unfold WalkerPreviousCandidate
        exact ⟨fun ⟨h1, h2⟩ => ⟨hne', h1, fun h _ => h2 h⟩,
          fun ⟨_, h1, h2⟩ => ⟨h1, fun h => h2 h hs'⟩⟩
      · refine ⟨_, if_neg hs, fun x => ?_, List.Sublist.refl _⟩
        have hs' : ¬ PreviousStopsAtRoot t w.root := fun h =>
          hs ((previousStopsAtRoot_iff hwf _).mpr h)
        rw [hX]
        unfold WalkerPreviousCandidate
        exact ⟨fun h => ⟨hne', h, fun _ h' => absurd h' hs'⟩, fun h => h.2.1⟩
    rw [hC]
    have hmem' : ∀ x ∈ C, InclusiveDescendant t x (root t w.current) := fun x hx =>
      hXmem x (hsub.subset hx)
    obtain ⟨hirr', hasym'⟩ := precedesStruct_order_on hwf hrtd hmem'
    have := result_of_sorted (t := t) (ws := w.whatToShow) (R := fun a b => PrecedesStruct t b a) hiff
      hirr' (fun a ha b hb h => hasym' b hb a ha h) (hXsorted.sublist hsub)
    unfold WalkerPreviousNodeResult LastIn
    rcases this with ⟨n, hf, hn, hlast⟩ | ⟨hf, hnone⟩
    · exact Or.inl ⟨n, by rw [← hf]; rfl, hn, hlast⟩
    · exact Or.inr ⟨by rw [← hf]; rfl, hnone⟩

end Dom.Spec
