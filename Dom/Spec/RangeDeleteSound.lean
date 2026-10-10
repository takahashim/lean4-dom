import Dom.Spec.RangeDelete
import Dom.Properties.RangeDelete
import Dom.Validity.RangeApi
import Dom.Validity.Derived
import Dom.Spec.NormalizeResult
import Dom.Spec.RangePassive

/-!
# `deleteContents` は `DeleteContentsResult` を満たす

語彙の対応（contained・nodes to remove・新しい boundary point）を示してから、
実行関数の step を順に関係へ移す。

## step 10 の boundary point は妥当である

実行関数は step 10 で、新しい boundary point が最終状態で妥当かを実行時に検査し、
妥当でなければ live range の調整が残した端点を使う。ここでその検査が必ず通ることを示す
（`deleteContentsNewBP_valid`）。芯は「new node の、new offset より前の子は
original start の before にあるので contained でなく、外されない」である。
-/

namespace Dom.Spec

open Dom

variable {t : Tree} {r : RangeState}

/-! ## contained -/

/-- 木に無い node の root はその node 自身なので、木にある node と root を共有すれば木にある。 -/
theorem exists_get?_of_root_eq (hwf : WellFormed t) {n m : NodeId} {md : NodeData}
    (hm : t.get? m = some md) (hr : root t n = root t m) : ∃ d, t.get? n = some d := by
  cases hn : t.get? n with
  | some d => exact ⟨d, rfl⟩
  | none =>
    exfalso
    have hrn : root t n = n :=
      root_eq_self_of_parent_none (by rw [parentOf_eq, hn]; rfl)
    obtain ⟨rd, hrd⟩ := exists_data_root hwf hm
    rw [← hr, hrn, hn] at hrd
    cases hrd

/-- **実行側の `containedInRange` は §5.5 の contained ちょうどである。** -/
theorem containedInRange_iff (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hroot : root t r.start.node = root t r.«end».node) (n : NodeId) :
    containedInRange t r n = true ↔ Contained t r n := by
  unfold containedInRange Contained
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨hr, hgt⟩, hlt⟩
    obtain ⟨d, hd⟩ := exists_get?_of_root_eq hwf hs hr
    refine ⟨⟨d, hd⟩, hr, ?_, ?_⟩
    · exact (bpPosition_eq_gt_iff (a := ⟨n, 0⟩) hwf hd hs hr).mp hgt
    · exact (bpPosition_eq_lt_iff (a := ⟨n, lengthOf t n⟩) hwf hd he (hr.trans hroot)).mp hlt
  · rintro ⟨⟨d, hd⟩, hr, hgt, hlt⟩
    exact ⟨⟨hr, (bpPosition_eq_gt_iff (a := ⟨n, 0⟩) hwf hd hs hr).mpr hgt⟩,
      (bpPosition_eq_lt_iff (a := ⟨n, lengthOf t n⟩) hwf hd he (hr.trans hroot)).mpr hlt⟩

/-! ## step 4 -/

/-- 重複の無い列は、自分の中での先行関係で並んでいる。 -/
theorem pairwise_precedesIn : ∀ {l : List NodeId}, l.Nodup →
    l.Pairwise (fun x y => precedesIn l x y = true)
  | [], _ => List.Pairwise.nil
  | a :: rest, hnd => by
    have ha : a ∉ rest := (List.nodup_cons.mp hnd).1
    refine List.Pairwise.cons (fun b hb => by simp [precedesIn, hb]) ?_
    refine (pairwise_precedesIn (List.nodup_cons.mp hnd).2).imp_of_mem ?_
    intro x y hx hy hxy
    have hax : a ≠ x := fun he => ha (he ▸ hx)
    have hay : a ≠ y := fun he => ha (he ▸ hy)
    simp [precedesIn, hax, hay, hxy]

/-- **実行側の `nodesToRemove` は step 4 の関係を満たす。** -/
theorem nodesToRemove_spec (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hroot : root t r.start.node = root t r.«end».node) :
    NodesToRemove t r (nodesToRemove t r) := by
  have hc := containedInRange_iff hwf hs he hroot
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hs
  refine ⟨fun n => ?_, ?_⟩
  · rw [mem_nodesToRemove_iff]
    constructor
    · rintro ⟨-, hcn, hp⟩
      refine ⟨(hc n).mp hcn, fun p hpp hcp => ?_⟩
      have := hp p hpp
      rw [(hc p).mpr hcp] at this
      cases this
    · rintro ⟨hcn, hp⟩
      refine ⟨?_, (hc n).mpr hcn, fun p hpp => ?_⟩
      · obtain ⟨-, hr, -⟩ := hcn
        unfold treeOrder
        refine (mem_preorder_iff hwf hrd n).mpr ?_
        rw [← hr]
        exact root_inclusive_ancestor t n
      · cases hq : containedInRange t r p with
        | false => rfl
        | true => exact absurd ((hc p).mp hq) (hp p hpp)
  · -- tree order：`treeOrder` は preorder なので、そこでの先行は構造的な tree order である
    unfold nodesToRemove
    refine List.Pairwise.filter _ ?_
    have hnd := treeOrder_nodup hwf r.start.node
    refine ((pairwise_precedesIn hnd).and hnd).imp_of_mem ?_
    intro x y hx hy ⟨hxy, hne⟩
    unfold treeOrder at hx hy hxy
    exact (precedesIn_preorder_iff_struct hwf hrd ((mem_preorder_iff hwf hrd x).mp hx)
      ((mem_preorder_iff hwf hrd y).mp hy) hne).mp hxy

/-! ## step 5-6 -/

/-- step 6 の loop の判定。 -/
private def stopAt (t : Tree) (en : NodeId) (x : NodeId) : Bool :=
  match parentOf t x with
  | none => true
  | some p => isInclusiveAncestorOf t p en

/--
**step 6 の loop は、parent が end node の inclusive ancestor である所で止まる。**

`x` が end node の inclusive ancestor でなく、同じ木にあれば、`x` から上る列のうち
最初に止まる node は、parent を持ち、その parent が end node の inclusive ancestor である。
-/
theorem find_stop (hwf : WellFormed t) {en : NodeId} :
    ∀ (k : Nat) (x : NodeId), (ancestors t x).length ≤ k → ¬ InclusiveAncestor t x en →
      root t x = root t en →
      ∃ ref p, (x :: ancestors t x).find? (stopAt t en) = some ref ∧
        InclusiveAncestor t ref x ∧ ¬ InclusiveAncestor t ref en ∧
        parentOf t ref = some p ∧ InclusiveAncestor t p en := by
  intro k
  induction k with
  | zero =>
    intro x hlen hx hroot
    exfalso
    cases hp : parentOf t x with
    | none =>
      have := root_inclusive_ancestor t en
      rw [← hroot, root_eq_self_of_parent_none hp] at this
      exact hx this
    | some p =>
      rw [ancestors_eq_cons hwf hp] at hlen
      simp at hlen
  | succ k ih =>
    intro x hlen hx hroot
    cases hp : parentOf t x with
    | none =>
      exfalso
      have := root_inclusive_ancestor t en
      rw [← hroot, root_eq_self_of_parent_none hp] at this
      exact hx this
    | some p =>
      by_cases hpe : InclusiveAncestor t p en
      · refine ⟨x, p, List.find?_cons_of_pos ?_, Or.inl rfl, hx, hp, hpe⟩
        simp only [stopAt, hp]
        exact (isInclusiveAncestorOf_iff hwf p en).mpr hpe
      · have hcons := ancestors_eq_cons hwf hp
        rw [hcons] at hlen ⊢
        rw [List.find?_cons_of_neg (by
          simp only [stopAt, hp]
          intro h
          exact hpe ((isInclusiveAncestorOf_iff hwf p en).mp h))]
        simp only [List.length_cons] at hlen
        obtain ⟨ref, q, hf, hrp, hre, hq, hqe⟩ := ih p (by omega) hpe
          (by rw [← root_eq_of_parentOf hwf hp]; exact hroot)
        exact ⟨ref, q, hf, hrp.trans_inclusive (Or.inr (Ancestor.step hp)), hre, hq, hqe⟩

/-- **実行側の `deleteContentsNewBP` は step 5-6 の関係を満たす。** -/
theorem deleteContentsNewBP_spec (hwf : WellFormed t)
    (hroot : root t r.start.node = root t r.«end».node) :
    DeleteNewBP t r (deleteContentsNewBP t r) := by
  unfold deleteContentsNewBP
  by_cases h : isInclusiveAncestorOf t r.start.node r.«end».node = true
  · rw [if_pos h]
    exact Or.inl ⟨(isInclusiveAncestorOf_iff hwf _ _).mp h, rfl⟩
  · rw [if_neg h]
    have hn : ¬ InclusiveAncestor t r.start.node r.«end».node :=
      fun h' => h ((isInclusiveAncestorOf_iff hwf _ _).mpr h')
    obtain ⟨ref, p, hf, hrs, hre, hp, hpe⟩ :=
      find_stop hwf _ r.start.node (Nat.le_refl _) hn hroot
    obtain ⟨i, hi⟩ := index_isSome hwf hp
    show DeleteNewBP t r
      (match parentOf t ((List.find? (stopAt t r.«end».node)
          (r.start.node :: ancestors t r.start.node)).getD r.start.node),
        index t ((List.find? (stopAt t r.«end».node)
          (r.start.node :: ancestors t r.start.node)).getD r.start.node) with
       | some p, some idx => ({ node := p, offset := idx + 1 } : BoundaryPoint)
       | _, _ => r.start)
    rw [hf]
    simp only [Option.getD_some, hp, hi]
    exact Or.inr ⟨hn, ref, p, i, hrs, hre, hp, hpe, hi, rfl⟩

/-! ## boundary point の前後の補題 -/

/-- 同じ木の二つの boundary point が互いに before であることはない。 -/
theorem bpBefore_asymm (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hroot : root t a.node = root t b.node)
    (h₁ : BPBefore t a b) (h₂ : BPBefore t b a) : False := by
  have e₁ := (bpPosition_eq_lt_iff hwf ha hb hroot).mpr h₁
  have e₂ := (bpPosition_eq_gt_iff hwf ha hb hroot).mpr h₂
  rw [e₁] at e₂
  cases e₂

section Order

variable (hwf : WellFormed t) {sd : NodeData} (hs : t.get? r.start.node = some sd)
include hwf hs

/-- start node の inclusive ancestor `x` について、(x, 0) は start の after ではない。 -/
theorem not_start_before_of_inclusiveAncestor {x : NodeId}
    (hx : InclusiveAncestor t x r.start.node) : ¬ BPBefore t r.start ⟨x, 0⟩ := by
  intro h
  rcases hx with rfl | hanc
  · have e := (bpPosition_eq_lt_iff (b := ⟨r.start.node, 0⟩) hwf hs hs rfl).mpr h
    unfold bpPosition at e
    rw [if_pos rfl] at e
    simp [compare, compareOfLessAndEq] at e
    split at e <;> simp_all
  · obtain ⟨c, hcp, hcs⟩ := hanc.exists_child
    obtain ⟨i, hi⟩ := index_isSome hwf hcp
    obtain ⟨xd, hxd⟩ := exists_data_of_parentOf hwf hcp
    have hb : BPBefore t ⟨x, 0⟩ r.start := Or.inr (Or.inl ⟨c, i, hcp, hi, hcs, Nat.zero_le _⟩)
    exact bpBefore_asymm hwf hxd hs (root_eq_of_ancestor hwf hanc).symm hb h

/-- (c, 0) が start の before なら、`c` は contained でない。 -/
theorem not_contained_of_before {c : NodeId} {cd : NodeData} (hc : t.get? c = some cd)
    (hroot : root t c = root t r.start.node) (h : BPBefore t ⟨c, 0⟩ r.start) :
    ¬ Contained t r c :=
  fun hcn => bpBefore_asymm hwf hc hs hroot h hcn.2.2.1

/-- start node の inclusive ancestor は contained でない。 -/
theorem not_contained_of_inclusiveAncestor {x : NodeId}
    (hx : InclusiveAncestor t x r.start.node) : ¬ Contained t r x :=
  fun hcn => not_start_before_of_inclusiveAncestor hwf hs hx hcn.2.2.1

/-- contained な node は parent を持つ（root は start node の inclusive ancestor なので）。 -/
theorem parentOf_isSome_of_contained {n : NodeId} (h : Contained t r n) :
    ∃ p, parentOf t n = some p := by
  cases hp : parentOf t n with
  | some p => exact ⟨p, rfl⟩
  | none =>
    exfalso
    have hr := h.2.1
    have hx : InclusiveAncestor t n r.start.node := by
      have := root_inclusive_ancestor t r.start.node
      rw [← hr, root_eq_self_of_parent_none hp] at this
      exact this
    exact not_contained_of_inclusiveAncestor hwf hs hx h

end Order

/-! ## step 8 は失敗しない -/

/-- 列のどれもが parent を持ち、重複が無ければ、`removeEach` は成功する。 -/
theorem removeEach_isOk_of_parents {b : Bool} : ∀ (ns : List NodeId) {s : DOMState},
    WellFormed s.tree → ns.Nodup → (∀ n ∈ ns, ∃ p, parentOf s.tree n = some p) →
    ∃ s', removeEach s ns b = .ok s'
  | [], s, _, _, _ => ⟨s, rfl⟩
  | n :: rest, s, hwf, hnd, hp => by
    obtain ⟨p, hpn⟩ := hp n (by simp)
    obtain ⟨s₁, hr⟩ := (remove_succeeds_iff hwf (n := n) (b := b)).mpr (by rw [hpn]; rfl)
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨o, ho⟩ := removeEach_isOk_of_parents rest (remove_preserves_wellformed hwf hr)
      hnd'.2 (fun m hm => by
        rw [parentOf_detach (remove_ok hr).2, if_neg (fun he : m = n => hnd'.1 (he ▸ hm))]
        exact hp m (by simp [hm]))
    exact ⟨o, by rw [removeEach, hr]; exact ho⟩

/-- `removeEach` は live range の数を変えない。 -/
theorem removeEach_ranges_length {b : Bool} : ∀ (ns : List NodeId) {s s' : DOMState},
    removeEach s ns b = .ok s' → s'.ranges.length = s.ranges.length
  | [], s, s', h => by rw [removeEach] at h; cases h; rfl
  | n :: rest, s, s', h => by
    rw [removeEach] at h
    split at h
    · cases h
    · next s₁ hr =>
      obtain ⟨⟨p, hp⟩, -⟩ := remove_ok hr
      rw [removeEach_ranges_length rest h, remove_ranges hp hr, List.length_map]

/-! ## step 10 の boundary point は妥当である -/

/-- children の先頭 `k` 個の中の node は、`k` より小さい index を持つ。 -/
theorem index_lt_of_mem_take (hwf : WellFormed t) {p c : NodeId} {k : Nat}
    (hc : c ∈ (childrenOf t p).take k) :
    parentOf t c = some p ∧ ∃ j, j < k ∧ index t c = some j := by
  obtain ⟨j, hj, hjc⟩ := List.mem_take_iff_getElem.mp hc
  have hjl : j < (childrenOf t p).length := by omega
  have hmem : c ∈ childrenOf t p := by rw [← hjc]; exact List.getElem_mem hjl
  have hcp := (mem_childrenOf_iff hwf c p).mpr hmem
  refine ⟨hcp, j, by omega, (index_eq_some_iff_split hcp).mpr ⟨(childrenOf t p).take j,
    (childrenOf t p).drop (j + 1), ?_, by simp; omega, ?_⟩⟩
  · rw [← hjc]; simp
  · intro hm
    have hnd := childrenOf_nodup hwf p
    rw [show childrenOf t p = (childrenOf t p).take j ++ c :: (childrenOf t p).drop (j + 1) from by
      rw [← hjc]; simp] at hnd
    exact (List.nodup_append.mp hnd).2.2 c hm c (by simp) rfl

/--
**new node の new offset より前の子が残れば、step 10 の boundary point は妥当である。**

`P` の children の先頭 `k` 個が最終状態でも `P` の子のまま残り、`P` の length が children の
数で数えられるなら、(P, k) は妥当である。
-/
theorem validBP_of_kept {s s₃ : DOMState} {P : NodeId} {k : Nat} (hwf : WellFormed s.tree)
    (hwf₃ : WellFormed s₃.tree) (hsp : ShapePreserving s.tree s₃.tree)
    (hcck : ChildCountKind s.tree P) (hk : k ≤ (childrenOf s.tree P).length)
    {pd : NodeData} (hpd : s.tree.get? P = some pd)
    (hkeep : ∀ c ∈ (childrenOf s.tree P).take k, parentOf s₃.tree c = some P) :
    checkValidBoundaryPoint s₃.tree ⟨P, k⟩ = true := by
  rw [checkValidBoundaryPoint_iff]
  obtain ⟨pd₃, hpd₃, hk₃⟩ := kind_of_shapePreserving hsp hpd
  have hcck₃ : ChildCountKind s₃.tree P := by
    intro d hd
    rw [hpd₃] at hd
    cases hd
    obtain ⟨h1, h2⟩ := hcck pd hpd
    rw [hk₃]
    exact ⟨h1, h2⟩
  refine ⟨pd₃, hpd₃, ?_⟩
  have hlen := lengthOf_eq_children hcck₃
  unfold lengthOf at hlen
  rw [hpd₃] at hlen
  dsimp only at hlen
  show k ≤ pd₃.length
  rw [hlen]
  have hsub : (childrenOf s.tree P).take k ⊆ childrenOf s₃.tree P :=
    fun c hc => (mem_childrenOf_iff hwf₃ c P).mp (hkeep c hc)
  have := List.Nodup.length_le_of_subset ((childrenOf_nodup hwf P).sublist (List.take_sublist _ _))
    hsub
  rw [List.length_take] at this
  omega

/--
**step 10 の boundary point は、step 7-9 の後の木で妥当である。**

step 7-9 は kind を変えず、外す node 以外の parent を変えない（`hsp`・`hpar`）。
-/
theorem deleteContentsNewBP_valid {s s₃ : DOMState} (h : AdmissibleDOMState s)
    (hrv : RangeValid s.tree r)
    (hn3 : ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node))
    (hwf₃ : WellFormed s₃.tree) (hsp : ShapePreserving s.tree s₃.tree)
    (hpar : ∀ x, x ∉ nodesToRemove s.tree r → parentOf s₃.tree x = parentOf s.tree x) :
    checkValidBoundaryPoint s₃.tree (deleteContentsNewBP s.tree r) = true := by
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, hso⟩, ⟨ed, he, heo⟩, hroot, -⟩ := hrv
  have hc := containedInRange_iff hwf hs he hroot
  -- 外されない子は親のまま残る
  have keep : ∀ {P : NodeId} {k : Nat}, (∀ c j, parentOf s.tree c = some P → index s.tree c = some j →
      j < k → ¬ Contained s.tree r c) →
      ∀ c ∈ (childrenOf s.tree P).take k, parentOf s₃.tree c = some P := by
    intro P k hnot c hcm
    obtain ⟨hcp, j, hjk, hj⟩ := index_lt_of_mem_take hwf hcm
    rw [hpar c (fun hm => hnot c j hcp hj hjk ((hc c).mp ((mem_nodesToRemove_iff c).mp hm).2.1))]
    exact hcp
  rcases deleteContentsNewBP_spec hwf hroot with ⟨hia, hbp⟩ | ⟨-, ref, p, i, hrs, hre, hp, -, hi, hbp⟩
  · -- step 5：original start
    rw [hbp]
    by_cases h0 : r.start.offset = 0
    · rw [checkValidBoundaryPoint_iff]
      obtain ⟨sd₃, hsd₃, -⟩ := kind_of_shapePreserving hsp hs
      exact ⟨sd₃, hsd₃, by rw [h0]; exact Nat.zero_le _⟩
    · have hcck : ChildCountKind s.tree r.start.node := by
        rcases hia with heq | hanc
        · intro d hd
          rw [hs] at hd
          cases hd
          refine ⟨?_, ?_⟩
          · cases hk : sd.kind.isCharacterData with
            | false => rfl
            | true => exact absurd ⟨heq, sd, hs, hk⟩ hn3
          · intro hk
            have : sd.length = 0 := by simp [NodeData.length, hk, NodeKind.isCharacterData]
            omega
        · obtain ⟨c, hcp, -⟩ := hanc.exists_child
          exact h.childCountKind hcp
      have hlen := lengthOf_eq_children hcck
      unfold lengthOf at hlen
      rw [hs] at hlen
      dsimp only at hlen
      rw [show r.start = ⟨r.start.node, r.start.offset⟩ from rfl]
      refine validBP_of_kept hwf hwf₃ hsp hcck (by rw [← hlen]; exact hso) hs (keep ?_)
      intro c j hcp hj hjk
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hcp
      exact not_contained_of_before hwf hs hcd (root_eq_of_parentOf hwf hcp)
        (Or.inr (Or.inr (Or.inl ⟨c, j, hcp, hj, Or.inl rfl, hjk⟩)))
  · -- step 6：reference node の次
    rw [hbp]
    have hcck : ChildCountKind s.tree p := h.childCountKind hp
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
    refine validBP_of_kept hwf hwf₃ hsp hcck (index_lt_children_length hp hi) hpd (keep ?_)
    intro c j hcp hj hjk
    by_cases hcr : c = ref
    · subst hcr
      exact not_contained_of_inclusiveAncestor hwf hs hrs
    · have hji : j < i := by
        have := index_ne_of_ne hcp hp hj hi hcr
        omega
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hcp
      have hrc : root s.tree c = root s.tree r.start.node := by
        rw [root_eq_of_parentOf hwf hcp, ← root_eq_of_parentOf hwf hp]
        rcases hrs with he' | ha'
        · rw [he']
        · exact (root_eq_of_ancestor hwf ha').symm
      exact not_contained_of_before hwf hs hcd hrc
        (Or.inr (Or.inr (Or.inr ⟨p, c, ref, j, i, hcp, hp, hj, hi, hji, Or.inl rfl, hrs⟩)))

/-! ## step 8 の点は step 9-11 で動かない

固定版の本文は step 8 で `this` を (newNode, newOffset) に置いてから、step 9-11 の replace data と
remove を走らせる。実行関数は step 9-11 を先に走らせてから点を置く。二つが同じになるのは、
step 9-11 の live range の調整がこの点を動かさないからである。

* replace data（step 9・11）は、対象の node を指す点しか動かさない。新しい点の node は
  original start node でも original end node でもない（それらが CharacterData のとき）。
* remove（step 10）は、外す node の中を指す点と、外す node の parent を指し offset が index より大きい点
  しか動かさない。新しい点の node は start node の inclusive ancestor なので contained な node の中にない。
  また new node の、new offset より前の子は contained でないので外されず、外す子の index は
  どの時点でも new offset 以上である。
-/

section Fixed

variable {s : DOMState}

/-- 新しい点は、step 6 なら original start、step 7 なら reference node の parent の (index + 1)。 -/
theorem newBP_cases (hwf : WellFormed s.tree)
    (hroot : root s.tree r.start.node = root s.tree r.«end».node) :
    (deleteContentsNewBP s.tree r = r.start ∧ InclusiveAncestor s.tree r.start.node r.«end».node) ∨
    (∃ ref i, parentOf s.tree ref = some (deleteContentsNewBP s.tree r).node ∧
      InclusiveAncestor s.tree ref r.start.node ∧ index s.tree ref = some i ∧
      (deleteContentsNewBP s.tree r).offset = i + 1) := by
  rcases deleteContentsNewBP_spec hwf hroot with ⟨hia, hbp⟩ | ⟨-, ref, p, i, hrs, -, hp, -, hi, hbp⟩
  · exact Or.inl ⟨hbp, hia⟩
  · refine Or.inr ⟨ref, i, ?_, hrs, hi, ?_⟩ <;> rw [hbp]
    exact hp

/-- 新しい点の node は original start node の inclusive ancestor である。 -/
theorem newBP_inclusiveAncestor_start (hwf : WellFormed s.tree)
    (hroot : root s.tree r.start.node = root s.tree r.«end».node) :
    InclusiveAncestor s.tree (deleteContentsNewBP s.tree r).node r.start.node := by
  rcases newBP_cases hwf hroot with ⟨hbp, -⟩ | ⟨ref, i, hp, hrs, -, -⟩
  · rw [hbp]; exact Or.inl rfl
  · exact InclusiveAncestor.trans_inclusive (Or.inr (Ancestor.step hp)) hrs

/-- original start node が CharacterData なら、新しい点の node はそれではない（step 9 が点を動かさない）。 -/
theorem newBP_ne_start (h : AdmissibleDOMState s)
    (hroot : root s.tree r.start.node = root s.tree r.«end».node)
    (hn3 : ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node))
    (hcd : IsCharacterData s.tree r.start.node) :
    (deleteContentsNewBP s.tree r).node ≠ r.start.node := by
  intro heq
  obtain ⟨d, hd, hk⟩ := hcd
  rcases newBP_cases h.wellFormed hroot with ⟨-, hia⟩ | ⟨ref, i, hp, -, -, -⟩
  · rcases hia with he | hanc
    · exact hn3 ⟨he, d, hd, hk⟩
    · obtain ⟨c, hcp, -⟩ := hanc.exists_child
      have := (h.childCountKind hcp d hd).1
      rw [hk] at this
      cases this
  · rw [heq] at hp
    have := (h.childCountKind hp d hd).1
    rw [hk] at this
    cases this

/-- original end node が CharacterData なら、新しい点の node はそれではない（step 11 が点を動かさない）。 -/
theorem newBP_ne_end (h : AdmissibleDOMState s)
    (hroot : root s.tree r.start.node = root s.tree r.«end».node)
    (hn3 : ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node))
    (hcd : IsCharacterData s.tree r.«end».node) :
    (deleteContentsNewBP s.tree r).node ≠ r.«end».node := by
  intro heq
  obtain ⟨d, hd, hk⟩ := hcd
  rcases newBP_cases h.wellFormed hroot with ⟨hbp, -⟩ | ⟨ref, i, hp, -, -, -⟩
  · rw [hbp] at heq
    exact hn3 ⟨heq, d, by rw [heq]; exact hd, hk⟩
  · rw [heq] at hp
    have := (h.childCountKind hp d hd).1
    rw [hk] at this
    cases this

/-- new node の、new offset より前の子は contained でない。 -/
theorem not_contained_before_newBP (h : AdmissibleDOMState s) (hrv : RangeValid s.tree r)
    {c : NodeId} {j : Nat} (hcp : parentOf s.tree c = some (deleteContentsNewBP s.tree r).node)
    (hj : index s.tree c = some j) (hjk : j < (deleteContentsNewBP s.tree r).offset) :
    ¬ Contained s.tree r c := by
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, -⟩, -, hroot, -⟩ := id hrv
  rcases newBP_cases hwf hroot with ⟨hbp, -⟩ | ⟨ref, i, hp, hrs, hi, hoff⟩
  · rw [hbp] at hcp hjk
    obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hcp
    exact not_contained_of_before hwf hs hcd (root_eq_of_parentOf hwf hcp)
      (Or.inr (Or.inr (Or.inl ⟨c, j, hcp, hj, Or.inl rfl, hjk⟩)))
  · rw [hoff] at hjk
    by_cases hcr : c = ref
    · subst hcr
      exact not_contained_of_inclusiveAncestor hwf hs hrs
    · have hji : j < i := by
        have := index_ne_of_ne hcp hp hj hi hcr
        omega
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hcp
      have hrc : root s.tree c = root s.tree r.start.node := by
        rw [root_eq_of_parentOf hwf hcp, ← root_eq_of_parentOf hwf hp]
        rcases hrs with he' | ha'
        · rw [he']
        · exact (root_eq_of_ancestor hwf ha').symm
      exact not_contained_of_before hwf hs hcd hrc
        (Or.inr (Or.inr (Or.inr ⟨_, c, ref, j, i, hcp, hp, hj, hi, hji, Or.inl rfl, hrs⟩)))

/-- new node が子を持つなら、new offset は子の数以下である。 -/
theorem newBP_offset_le (h : AdmissibleDOMState s) (hrv : RangeValid s.tree r) {c : NodeId}
    (hc : parentOf s.tree c = some (deleteContentsNewBP s.tree r).node) :
    (deleteContentsNewBP s.tree r).offset ≤
      (childrenOf s.tree (deleteContentsNewBP s.tree r).node).length := by
  obtain ⟨⟨sd, hs, hso⟩, -, hroot, -⟩ := id hrv
  rcases newBP_cases h.wellFormed hroot with ⟨hbp, -⟩ | ⟨ref, i, hp, -, hi, hoff⟩
  · rw [hbp] at hc ⊢
    have hlen := lengthOf_eq_children (h.childCountKind hc)
    unfold lengthOf at hlen
    rw [hs] at hlen
    dsimp only at hlen
    rw [← hlen]
    exact hso
  · rw [hoff]
    have := index_lt_children_length hp hi
    omega

/-- 列の先頭 `A` に入らない要素は、`A` の長さ以上の位置にある。 -/
theorem mem_of_append_eq {α : Type} {A B u v : List α} {m : α} (h : A ++ B = u ++ m :: v)
    (hl : u.length < A.length) : m ∈ A := by
  have h1 : (u ++ m :: v)[u.length]? = some m := by simp
  rw [← h, List.getElem?_append_left hl, List.getElem?_eq_some_iff] at h1
  obtain ⟨hlt, heq⟩ := h1
  rw [← heq]
  exact List.getElem_mem hlt

/--
**remove を続けても、`A` にも `P` にも当たらない node しか外さなければ、`P` の children は `A` で始まったままである。**
-/
theorem removeEach_children_prefix {P : NodeId} {A : List NodeId} {b : Bool} :
    ∀ (ns : List NodeId) {s₀ s' : DOMState}, WellFormed s₀.tree → removeEach s₀ ns b = .ok s' →
      (∀ m ∈ ns, m ∉ A ∧ m ≠ P) → ∀ {B : List NodeId}, childrenOf s₀.tree P = A ++ B →
      ∃ B', childrenOf s'.tree P = A ++ B'
  | [], s₀, s', _, h, _, B, hB => by
    rw [removeEach] at h
    cases h
    exact ⟨B, hB⟩
  | m :: rest, s₀, s', hwf, h, hns, B, hB => by
    rw [removeEach] at h
    split at h
    · cases h
    · rename_i s₁ hr
      have hwf₁ := remove_preserves_wellformed hwf hr
      have hd := (remove_ok hr).2
      obtain ⟨hmA, -⟩ := hns m (by simp)
      have hc₁ : ∃ B₁, childrenOf s₁.tree P = A ++ B₁ := by
        rcases detach_ok_cases hd with ⟨d, -, -, ht⟩ | ⟨d, p, pd, hdd, hdp, hpd, ht⟩
        · exact ⟨B, by rw [ht, hB]⟩
        · have hpm : parentOf s₀.tree m = some p := by rw [parentOf_eq, hdd]; exact hdp
          have hpn : p ≠ m := fun he => ancestor_irrefl hwf m (Ancestor.step (he ▸ hpm))
          rw [ht, childrenOf_detachFrom hdd hpd hpn]
          split
          · rename_i hPp
            refine ⟨Dom.ListUtil.removeAll B m, ?_⟩
            rw [← hPp, hB]
            unfold Dom.ListUtil.removeAll
            rw [List.filter_append]
            congr 1
            exact List.filter_eq_self.mpr (fun x hx => decide_eq_true (fun he => hmA (he ▸ hx)))
          · exact ⟨B, hB⟩
      obtain ⟨B₁, hB₁⟩ := hc₁
      exact removeEach_children_prefix rest hwf₁ h (fun x hx => hns x (by simp [hx])) hB₁

/--
**step 10 の各 remove は、step 8 で置いた点を動かさない。**

`s₁` は step 9 の後の状態で、木の形は `s` と同じである（replace data は data しか変えない）。
-/
theorem newBP_fixed_removeEach (h : AdmissibleDOMState s) (hrv : RangeValid s.tree r)
    {s₁ : DOMState} (hwf₁ : WellFormed s₁.tree)
    (hpar₁ : ∀ x, parentOf s₁.tree x = parentOf s.tree x)
    (hch₁ : ∀ x, childrenOf s₁.tree x = childrenOf s.tree x) :
    ∀ pre m post s', nodesToRemove s.tree r = pre ++ m :: post → removeEach s₁ pre false = .ok s' →
      PreRemoveFixes s'.tree m ⟨deleteContentsNewBP s.tree r, deleteContentsNewBP s.tree r⟩ := by
  intro pre m post s' hsplit hpre p hp
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, -⟩, ⟨ed, he, -⟩, hroot, -⟩ := id hrv
  have hc := containedInRange_iff hwf hs he hroot
  have hwf' := removeEach_preserves_wellformed pre hwf₁ hpre
  have hnd := nodesToRemove_nodup (r := r) hwf
  rw [hsplit] at hnd
  have hmpre : m ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 m hm m (by simp) rfl
  have contained_of_mem : ∀ x ∈ nodesToRemove s.tree r, Contained s.tree r x :=
    fun x hx => (hc x).mp ((mem_nodesToRemove_iff x).mp hx).2.1
  have hmC : Contained s.tree r m := contained_of_mem m (by rw [hsplit]; simp)
  have hpm : parentOf s.tree m = some p := by
    rw [← hpar₁, ← parentOf_removeEach_of_not_mem pre hpre hmpre]
    exact hp
  have hanc : ∀ {a x : NodeId}, Ancestor s'.tree a x → Ancestor s.tree a x := fun ha =>
    ancestor_of_parentOf_subset (fun x y hxy => by rw [← hpar₁]; exact hxy)
      (ancestor_of_removeEach pre hpre ha)
  have hstart := newBP_inclusiveAncestor_start hwf hroot
  -- A：new node の、new offset より前の子。contained でないので外されない。
  have notA : ∀ x, Contained s.tree r x →
      x ∉ (childrenOf s.tree (deleteContentsNewBP s.tree r).node).take
        (deleteContentsNewBP s.tree r).offset := by
    intro x hxC hxA
    obtain ⟨hxp, j, hjk, hj⟩ := index_lt_of_mem_take hwf hxA
    exact not_contained_before_newBP h hrv hxp hj hjk hxC
  have key : liveRangePreRemoveBP s'.tree m p ((index s'.tree m).getD 0)
      (deleteContentsNewBP s.tree r) = deleteContentsNewBP s.tree r := by
    rw [liveRangePreRemoveBP_neg]
    · unfold rangeShiftAfterRemove
      rw [if_neg]
      rintro ⟨hP, hlt⟩
      subst hP
      obtain ⟨j', hj'⟩ := index_isSome hwf' hp
      rw [hj', Option.getD_some] at hlt
      obtain ⟨B', hB'⟩ := removeEach_children_prefix pre hwf₁ hpre
        (fun x hx => ⟨notA x (contained_of_mem x (by rw [hsplit]; simp [hx])),
          fun hxe => not_contained_of_inclusiveAncestor hwf hs (hxe ▸ hstart)
            (contained_of_mem x (by rw [hsplit]; simp [hx]))⟩)
        (B := (childrenOf s.tree (deleteContentsNewBP s.tree r).node).drop
          (deleteContentsNewBP s.tree r).offset)
        (by rw [hch₁]; exact (List.take_append_drop _ _).symm)
      obtain ⟨u, v, huv, hul, -⟩ := (index_eq_some_iff_split hp).mp hj'
      rw [hB'] at huv
      have hle := newBP_offset_le h hrv hpm
      apply notA m hmC
      refine mem_of_append_eq huv ?_
      rw [List.length_take]
      omega
    · cases hia : isInclusiveAncestorOf s'.tree m (deleteContentsNewBP s.tree r).node with
      | false => rfl
      | true =>
        exfalso
        have h1 := (isInclusiveAncestorOf_iff hwf' m _).mp hia
        have h2 : InclusiveAncestor s.tree m (deleteContentsNewBP s.tree r).node :=
          h1.imp id hanc
        exact not_contained_of_inclusiveAncestor hwf hs (h2.trans_inclusive hstart) hmC
  unfold liveRangePreRemoveRange
  simp only [key]

end Fixed

/-! ## 全体 -/

/-- 実行関数の step 10-11 と、step 8 の点を置く所。 -/
private def deleteTail (s₁ : DOMState) (i : Nat) (toRemove : List NodeId) (en : NodeId)
    (eo : Nat) (deChar : Bool) (newBP : BoundaryPoint) : Except DOMException DOMState :=
  match removeEach s₁ toRemove with
  | .error e => .error e
  | .ok s₂ =>
    match (if deChar then replaceData s₂ en 0 eo "" else .ok s₂) with
    | .error e => .error e
    | .ok s₃ =>
      match s₃.ranges[i]? with
      | none => .error .notFoundError
      | some r₃ =>
        let bp := if checkValidBoundaryPoint s₃.tree newBP then newBP else r₃.start
        .ok (withRange s₃ i { start := bp, «end» := bp })

/-- replace data は kind を変えず、parent も children も変えず、live range の数を変えない。 -/
theorem replaceData_frame {s s' : DOMState} {n : NodeId} {offset count : Nat} {data : String}
    (hwf : WellFormed s.tree) (h : replaceData s n offset count data = .ok s') :
    WellFormed s'.tree ∧ ShapePreserving s.tree s'.tree ∧
      (∀ x, parentOf s'.tree x = parentOf s.tree x) ∧ s'.ranges.length = s.ranges.length ∧
      (∀ x, childrenOf s'.tree x = childrenOf s.tree x) := by
  obtain ⟨d, sp, hd, -, -, -, ht, hrg, -⟩ := replaceData_ok h
  refine ⟨replaceData_preserves_wellformed hwf h, shapePreserving_replaceData h,
    fun x => by rw [ht, parentOf_withData hd], by rw [hrg, List.length_map],
    fun x => by rw [ht, childrenOf_withData hd]⟩

/--
step 10-11。step 9 の後の状態 `s₁`（実行関数の側）が木の形と range の数を保っていれば、
step 8 で点を置いた状態から本文の順に進めたものが関係を満たし、実行関数の結果と一致する。
-/
private theorem deleteTail_spec {s s₁ : DOMState} {i : Nat} {r : RangeState} {ed : NodeData}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r)
    (hn3 : ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node))
    (he : s.tree.get? r.«end».node = some ed)
    (hwf₁ : WellFormed s₁.tree) (hsp₁ : ShapePreserving s.tree s₁.tree)
    (hpar₁ : ∀ x, parentOf s₁.tree x = parentOf s.tree x)
    (hlen₁ : s₁.ranges.length = s.ranges.length)
    (hch₁ : ∀ x, childrenOf s₁.tree x = childrenOf s.tree x) :
    ∃ s₂, RemoveEachSpec (withRange s₁ i ⟨deleteContentsNewBP s.tree r, deleteContentsNewBP s.tree r⟩)
        (nodesToRemove s.tree r) false s₂ ∧
      AndThen (ReplaceDataIfCharacterData s₂ r.«end».node 0 r.«end».offset)
        (fun s₃ res₃ => res₃ = .ok s₃)
        (deleteTail s₁ i (nodesToRemove s.tree r) r.«end».node r.«end».offset
          ed.kind.isCharacterData (deleteContentsNewBP s.tree r)) := by
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, -⟩, -, hroot, -⟩ := id hrv
  have hc := containedInRange_iff hwf hs he hroot
  -- step 8 の点
  let x : RangeState := ⟨deleteContentsNewBP s.tree r, deleteContentsNewBP s.tree r⟩
  -- step 10 は失敗しない
  obtain ⟨s₂, hre⟩ := removeEach_isOk_of_parents (b := false) (nodesToRemove s.tree r) hwf₁
    (nodesToRemove_nodup hwf) (fun n hn => by
      obtain ⟨p, hp⟩ := parentOf_isSome_of_contained hwf hs
        ((hc n).mp ((mem_nodesToRemove_iff n).mp hn).2.1)
      exact ⟨p, by rw [hpar₁]; exact hp⟩)
  have hre' : removeEach (withRange s₁ i x) (nodesToRemove s.tree r) false = .ok (withRange s₂ i x) := by
    rw [removeEach_withRange _ _ (newBP_fixed_removeEach h hrv hwf₁ hpar₁ hch₁), hre]
    rfl
  have hwf₂ := removeEach_preserves_wellformed _ hwf₁ hre
  have hsp₂ := hsp₁.trans (shapePreserving_removeEach _ hre)
  have hpar₂ : ∀ x, x ∉ nodesToRemove s.tree r → parentOf s₂.tree x = parentOf s.tree x :=
    fun x hx => by rw [parentOf_removeEach_of_not_mem _ hre hx, hpar₁]
  have hlen₂ : s₂.ranges.length = s.ranges.length := by
    rw [removeEach_ranges_length _ hre, hlen₁]
  -- 実行関数の最後：点は最終の木でも妥当なので、そのまま置かれる
  have final : ∀ s₃ : DOMState, WellFormed s₃.tree → ShapePreserving s.tree s₃.tree →
      (∀ x, x ∉ nodesToRemove s.tree r → parentOf s₃.tree x = parentOf s.tree x) →
      s₃.ranges.length = s.ranges.length →
      (match s₃.ranges[i]? with
        | none => (Except.error DOMException.notFoundError : Except DOMException DOMState)
        | some r₃ =>
          let bp := if checkValidBoundaryPoint s₃.tree (deleteContentsNewBP s.tree r)
            then deleteContentsNewBP s.tree r else r₃.start
          (.ok (withRange s₃ i { start := bp, «end» := bp }) : Except DOMException DOMState)) =
        .ok (withRange s₃ i x) := by
    intro s₃ hwf₃ hsp₃ hpar₃ hlen₃
    have hi : i < s₃.ranges.length := by
      rw [hlen₃]; exact (List.getElem?_eq_some_iff.mp hr).1
    rw [List.getElem?_eq_getElem hi]
    simp only []
    rw [if_pos (deleteContentsNewBP_valid h hrv hn3 hwf₃ hsp₃ hpar₃)]
  refine ⟨withRange s₂ i x, removeEach_sound _ hwf₁ hre', ?_⟩
  unfold deleteTail
  rw [hre]
  simp only []
  obtain ⟨ed₂, hed₂, hk₂⟩ := kind_of_shapePreserving hsp₂ he
  by_cases hk : ed.kind.isCharacterData = true
  · rw [if_pos hk]
    have hch : IsCharacterData s₂.tree r.«end».node := ⟨ed₂, hed₂, by rw [hk₂]; exact hk⟩
    have hne := newBP_ne_end h hroot hn3 ⟨ed, he, hk⟩
    have hsound := replaceData_result_sound (s := withRange s₂ i x) hwf₂ r.«end».node 0
      r.«end».offset ""
    rw [replaceData_withRange hne hne] at hsound
    cases h11 : replaceData s₂ r.«end».node 0 r.«end».offset "" with
    | error e =>
      rw [h11] at hsound
      exact Or.inl ⟨e, Or.inr ⟨hch, hsound⟩, rfl⟩
    | ok s₃ =>
      rw [h11] at hsound
      obtain ⟨hwf₃, hsp₃, hpar₃, hlen₃, -⟩ := replaceData_frame hwf₂ h11
      refine Or.inr ⟨withRange s₃ i x, Or.inr ⟨hch, hsound⟩, ?_⟩
      exact final s₃ hwf₃ (hsp₂.trans hsp₃) (fun x hx => by rw [hpar₃, hpar₂ x hx])
        (by rw [hlen₃, hlen₂])
  · rw [if_neg hk]
    have hch : ¬ IsCharacterData s₂.tree r.«end».node := by
      rintro ⟨d, hd, hdk⟩
      rw [hed₂] at hd
      cases hd
      rw [hk₂] at hdk
      exact hk hdk
    exact Or.inr ⟨withRange s₂ i x, Or.inl ⟨hch, rfl⟩, final s₂ hwf₂ hsp₂ hpar₂ hlen₂⟩

/--
**`deleteContents` の結果は、成否によらず関係を満たす。**

関係は固定版の本文の順（step 8 で点を置いてから step 9-11）で書いてある。実行関数は点を最後に置くが、
step 9-11 の調整が点を動かさないので同じ結果になる。

`this` が live range として妥当（`RangeValid`）であることを仮定する。仕様の live range が
常に満たしている前提である。
-/
theorem rangeDeleteContents_result_sound {s : DOMState} {i : Nat} {r : RangeState}
    (h : AdmissibleDOMState s) (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r) :
    DeleteContentsResult s i r (rangeDeleteContents s i) := by
  have hwf := h.wellFormed
  obtain ⟨⟨sd, hs, hso⟩, ⟨ed, he, -⟩, hroot, -⟩ := id hrv
  unfold rangeDeleteContents
  rw [hr]
  simp only []
  -- step 1
  by_cases hcol : r.start = r.«end»
  · rw [if_pos (by simp [hcol])]
    exact Or.inl ⟨hcol, rfl⟩
  rw [if_neg (by simpa using hcol)]
  simp only [hs, he]
  -- step 3
  by_cases h3 : (r.start.node == r.«end».node && sd.kind.isCharacterData) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    exact Or.inr (Or.inl ⟨hcol, h3.1, ⟨sd, hs, h3.2⟩, replaceData_result_sound hwf _ _ _ _⟩)
  rw [if_neg h3]
  have hn3 : ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node) := by
    rintro ⟨heq, d, hd, hdk⟩
    rw [hs] at hd
    cases hd
    exact h3 (by simp [heq, hdk])
  refine Or.inr (Or.inr ⟨hcol, hn3, _, _, nodesToRemove_spec hwf hs he hroot,
    deleteContentsNewBP_spec hwf hroot, ?_⟩)
  -- step 8 で置く点
  let x : RangeState := ⟨deleteContentsNewBP s.tree r, deleteContentsNewBP s.tree r⟩
  show AndThen (ReplaceDataIfCharacterData (withRange s i x) _ _ _) _ _
  -- step 9
  rw [lengthOf_of_get? hs]
  by_cases hk9 : sd.kind.isCharacterData = true
  · rw [if_pos hk9]
    have hne := newBP_ne_start h hroot hn3 ⟨sd, hs, hk9⟩
    have hsound := replaceData_result_sound (s := withRange s i x) hwf r.start.node r.start.offset
      (sd.length - r.start.offset) ""
    rw [replaceData_withRange hne hne] at hsound
    cases h9 : replaceData s r.start.node r.start.offset (sd.length - r.start.offset) "" with
    | error e =>
      rw [h9] at hsound
      exact Or.inl ⟨e, Or.inr ⟨⟨sd, hs, hk9⟩, hsound⟩, rfl⟩
    | ok s₁ =>
      rw [h9] at hsound
      obtain ⟨hwf₁, hsp₁, hpar₁, hlen₁, hch₁⟩ := replaceData_frame hwf h9
      exact Or.inr ⟨withRange s₁ i x, Or.inr ⟨⟨sd, hs, hk9⟩, hsound⟩,
        deleteTail_spec h hr hrv hn3 he hwf₁ hsp₁ hpar₁ hlen₁ hch₁⟩
  · rw [if_neg hk9]
    have hch : ¬ IsCharacterData s.tree r.start.node := by
      rintro ⟨d, hd, hdk⟩
      rw [hs] at hd
      cases hd
      exact hk9 hdk
    exact Or.inr ⟨withRange s i x, Or.inl ⟨hch, rfl⟩,
      deleteTail_spec h hr hrv hn3 he hwf (ShapePreserving.refl _) (fun _ => rfl) rfl (fun _ => rfl)⟩

end Dom.Spec
