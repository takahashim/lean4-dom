import Dom.Spec.Walker
import Dom.Properties.Mutation
import Dom.Properties.Range

/-!
# 子の列を反転した木

§6.2 の `lastChild()`・`previousSibling()` は `firstChild()`・`nextSibling()` の鏡像で、子を後ろから見る。
その順序（`MirrorPrecedes`）は、各 node の children を反転した木（`mirrorTree`）の上の tree order である。
`mirrorTree` は証明の道具で、関係は `MirrorPrecedes`（ancestor であるか、共通の parent の下で index の
**大きい**子の側にいる）で書く。
-/

namespace Dom.Spec

open Dom

/-- 各 node の children を反転した木。 -/
def mirrorTree (t : Tree) : Tree :=
  ⟨t.nodes.mapValues fun _ d => { d with children := d.children.reverse }⟩

/-- 鏡像の tree order：ancestor であるか、共通の parent の下で index の大きい子の側にいる。 -/
def MirrorPrecedes (t : Tree) (x y : NodeId) : Prop :=
  Ancestor t x y ∨
    ∃ p cx cy i j, parentOf t cx = some p ∧ parentOf t cy = some p ∧
      index t cx = some i ∧ index t cy = some j ∧ j < i ∧
      InclusiveAncestor t cx x ∧ InclusiveAncestor t cy y

/-- `P` を満たす node のうち、鏡像の tree order で最初のもの。 -/
def MirrorFirstIn (t : Tree) (P : NodeId → Prop) (n : NodeId) : Prop :=
  P n ∧ ∀ m, P m → ¬ MirrorPrecedes t m n

variable {t : Tree}

@[simp] theorem get?_mirrorTree (n : NodeId) :
    (mirrorTree t).get? n = (t.get? n).map fun d => { d with children := d.children.reverse } := by
  show (t.nodes.mapValues _).get? n = _
  rw [NodeStore.get?_mapValues]
  rfl

@[simp] theorem parentOf_mirrorTree (n : NodeId) : parentOf (mirrorTree t) n = parentOf t n := by
  simp only [parentOf_eq, get?_mirrorTree]
  cases t.get? n <;> rfl

@[simp] theorem childrenOf_mirrorTree (n : NodeId) :
    childrenOf (mirrorTree t) n = (childrenOf t n).reverse := by
  unfold childrenOf
  rw [get?_mirrorTree]
  cases t.get? n <;> rfl

@[simp] theorem contains_mirrorTree (n : NodeId) : (mirrorTree t).contains n = t.contains n := by
  show ((mirrorTree t).get? n).isSome = (t.get? n).isSome
  rw [get?_mirrorTree]
  cases t.get? n <;> rfl

@[simp] theorem size_mirrorTree : (mirrorTree t).size = t.size := by
  show (t.nodes.mapValues _).entries.length = t.nodes.entries.length
  simp [NodeStore.mapValues]

@[simp] theorem kindOf_mirrorTree (n : NodeId) : kindOf (mirrorTree t) n = kindOf t n := by
  unfold kindOf
  rw [get?_mirrorTree]
  cases t.get? n <;> rfl

theorem ancestor_mirrorTree_iff {a n : NodeId} : Ancestor (mirrorTree t) a n ↔ Ancestor t a n := by
  constructor
  · intro h
    induction h with
    | step hp => exact Ancestor.step (by simpa using hp)
    | trans hp _ ih => exact Ancestor.trans (by simpa using hp) ih
  · intro h
    induction h with
    | step hp => exact Ancestor.step (by simpa using hp)
    | trans hp _ ih => exact Ancestor.trans (by simpa using hp) ih

theorem inclusiveAncestor_mirrorTree_iff {a n : NodeId} :
    InclusiveAncestor (mirrorTree t) a n ↔ InclusiveAncestor t a n := by
  unfold InclusiveAncestor
  rw [ancestor_mirrorTree_iff]

theorem wellFormed_mirrorTree (hwf : WellFormed t) : WellFormed (mirrorTree t) where
  parent_child p pd hpd c hc := by
    rw [get?_mirrorTree] at hpd
    obtain ⟨pd₀, hpd₀, rfl⟩ := Option.map_eq_some_iff.mp hpd
    obtain ⟨cd, hcd, hcp⟩ := hwf.parent_child p pd₀ hpd₀ c (by simpa using hc)
    exact ⟨{ cd with children := cd.children.reverse }, by rw [get?_mirrorTree, hcd]; rfl, hcp⟩
  child_parent c cd p hcd hcp := by
    rw [get?_mirrorTree] at hcd
    obtain ⟨cd₀, hcd₀, rfl⟩ := Option.map_eq_some_iff.mp hcd
    obtain ⟨pd, hpd, hmem⟩ := hwf.child_parent c cd₀ p hcd₀ hcp
    exact ⟨{ pd with children := pd.children.reverse }, by rw [get?_mirrorTree, hpd]; rfl,
      by simpa using hmem⟩
  children_nodup n d hd := by
    rw [get?_mirrorTree] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp hd
    exact (List.reverse_perm _).nodup_iff.mpr (hwf.children_nodup n d₀ hd₀)
  acyclic n h := hwf.acyclic n (ancestor_mirrorTree_iff.mp h)
  ownerDocument_is_document n d hd := by
    rw [get?_mirrorTree] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨dd, hdd, hk⟩ := hwf.ownerDocument_is_document n d₀ hd₀
    exact ⟨{ dd with children := dd.children.reverse }, by rw [get?_mirrorTree, hdd]; rfl, hk⟩

theorem preorderFuel_mirrorTree : ∀ (f : Nat) (n : NodeId),
    preorderFuel (mirrorTree t) f n = mirrorPreorderFuel t f n
  | 0, _ => rfl
  | f + 1, n => by
    simp only [preorderFuel, mirrorPreorderFuel, contains_mirrorTree, childrenOf_mirrorTree]
    split
    · rw [show preorderFuel (mirrorTree t) f = mirrorPreorderFuel t f from
        funext (preorderFuel_mirrorTree f)]
    · rfl

@[simp] theorem preorder_mirrorTree (n : NodeId) : preorder (mirrorTree t) n = mirrorPreorder t n := by
  unfold preorder mirrorPreorder
  rw [size_mirrorTree, preorderFuel_mirrorTree]

@[simp] theorem lastDescendant_mirrorTree (n : NodeId) :
    lastDescendant (mirrorTree t) n = mirrorLastDescendant t n := by
  unfold lastDescendant mirrorLastDescendant
  rw [preorder_mirrorTree]

@[simp] theorem showsNode_mirrorTree (ws : Nat) (n : NodeId) :
    showsNode (mirrorTree t) ws n = showsNode t ws n := by
  unfold showsNode
  rw [kindOf_mirrorTree]

@[simp] theorem walkerAccepts_mirrorTree (w : WalkerState) (n : NodeId) :
    walkerAccepts (mirrorTree t) w n = walkerAccepts t w n := by
  unfold walkerAccepts
  rw [showsNode_mirrorTree]

theorem accepts_mirrorTree_iff {ws : Nat} {n : NodeId} : Accepts (mirrorTree t) ws n ↔ Accepts t ws n := by
  rw [← showsNode_iff, ← showsNode_iff, showsNode_mirrorTree]

theorem validWalker_mirrorTree {w : WalkerState} (h : ValidWalker t w) : ValidWalker (mirrorTree t) w := by
  obtain ⟨⟨rd, hrd⟩, ⟨cd, hcd⟩⟩ := h
  exact ⟨⟨_, by rw [get?_mirrorTree, hrd]; rfl⟩, ⟨_, by rw [get?_mirrorTree, hcd]; rfl⟩⟩

/-- 反転した木の index は、後ろから数えた index である。 -/
theorem index_mirrorTree (hwf : WellFormed t) {c p : NodeId} {i : Nat}
    (hp : parentOf t c = some p) (hi : index t c = some i) :
    index (mirrorTree t) c = some ((childrenOf t p).length - 1 - i) := by
  obtain ⟨u, v, huv, hul, hcu⟩ := (index_eq_some_iff_split hp).mp hi
  have hp' : parentOf (mirrorTree t) c = some p := by simpa using hp
  have hnd := childrenOf_nodup hwf p
  rw [huv] at hnd
  refine (index_eq_some_iff_split hp').mpr ⟨v.reverse, u.reverse, ?_, ?_, ?_⟩
  · rw [childrenOf_mirrorTree, huv]; simp
  · rw [huv]; simp; omega
  · intro hm
    have hcv : c ∈ v := List.mem_reverse.mp hm
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hcv

/-- **反転した木の tree order は、鏡像の tree order である。** -/
theorem precedesStruct_mirrorTree_iff (hwf : WellFormed t) {x y : NodeId} :
    PrecedesStruct (mirrorTree t) x y ↔ MirrorPrecedes t x y := by
  unfold PrecedesStruct MirrorPrecedes
  rw [ancestor_mirrorTree_iff]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hx, hy⟩
    rw [parentOf_mirrorTree] at hcx hcy
    obtain ⟨i₀, hi₀⟩ := index_isSome hwf hcx
    obtain ⟨j₀, hj₀⟩ := index_isSome hwf hcy
    have hlx := index_lt_children_length hcx hi₀
    have hly := index_lt_children_length hcy hj₀
    rw [index_mirrorTree hwf hcx hi₀] at hi
    rw [index_mirrorTree hwf hcy hj₀] at hj
    cases hi; cases hj
    exact ⟨p, cx, cy, i₀, j₀, hcx, hcy, hi₀, hj₀, by omega,
      inclusiveAncestor_mirrorTree_iff.mp hx, inclusiveAncestor_mirrorTree_iff.mp hy⟩
  · rintro ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hji, hx, hy⟩
    have hlx := index_lt_children_length hcx hi
    have hly := index_lt_children_length hcy hj
    refine ⟨p, cx, cy, _, _, by simpa using hcx, by simpa using hcy,
      index_mirrorTree hwf hcx hi, index_mirrorTree hwf hcy hj, by omega,
      inclusiveAncestor_mirrorTree_iff.mpr hx, inclusiveAncestor_mirrorTree_iff.mpr hy⟩

/-! ## `lastChild()` -/

/-- `L` が `r` の inclusive descendant のうち、鏡像の tree order で最後のもの。 -/
def MirrorLastDescendantOf (t : Tree) (r L : NodeId) : Prop :=
  InclusiveDescendant t L r ∧ ∀ x, InclusiveDescendant t x r → ¬ MirrorPrecedes t L x

/--
"traverse children"（last）の候補：current の子孫。親へ上がったときにそれが root か current なら止まる
（step 3.4.4）ので、root が current の子孫なら、root の鏡像の最後の inclusive descendant より後ろは候補でない。
-/
def WalkerLastChildCandidate (t : Tree) (w : WalkerState) (x : NodeId) : Prop :=
  Ancestor t w.current x ∧
    ∀ L, MirrorLastDescendantOf t w.root L → Ancestor t w.current w.root → ¬ MirrorPrecedes t L x

/--
**§6.2 `lastChild()` の関係。** filter は null。候補のうち accept されるもので、鏡像の tree order
（子を後ろから見て、降りるときも最後の子へ降りる順）で最初のもの。
-/
def WalkerLastChildResult (t : Tree) (w : WalkerState) (r : Option NodeId) : Prop :=
  (∃ n, r = some n ∧
      MirrorFirstIn t (fun x => WalkerLastChildCandidate t w x ∧ Accepts t w.whatToShow x) n) ∨
  (r = none ∧ ∀ m, WalkerLastChildCandidate t w m → ¬ Accepts t w.whatToShow m)

theorem walkerLastChild_eq (w : WalkerState) :
    walkerLastChild t w = walkerFirstChild (mirrorTree t) w := by
  unfold walkerLastChild walkerFirstChild
  rw [preorder_mirrorTree, lastDescendant_mirrorTree]
  congr 1
  funext n
  rw [walkerAccepts_mirrorTree]

theorem lastDescendantOf_mirrorTree_iff (hwf : WellFormed t) {r L : NodeId} :
    LastDescendantOf (mirrorTree t) r L ↔ MirrorLastDescendantOf t r L := by
  unfold LastDescendantOf MirrorLastDescendantOf InclusiveDescendant
  simp only [inclusiveAncestor_mirrorTree_iff, precedesStruct_mirrorTree_iff hwf]

theorem walkerChildCandidate_mirrorTree_iff (hwf : WellFormed t) {w : WalkerState} {x : NodeId} :
    WalkerChildCandidate (mirrorTree t) w x ↔ WalkerLastChildCandidate t w x := by
  unfold WalkerChildCandidate WalkerLastChildCandidate
  simp only [ancestor_mirrorTree_iff, lastDescendantOf_mirrorTree_iff hwf,
    precedesStruct_mirrorTree_iff hwf]

/-- **`lastChild()` は関係を満たす。** `firstChild()` を、子の列を反転した木で走らせたものである。 -/
theorem walkerLastChild_result_sound (hwf : WellFormed t) {w : WalkerState}
    (hw : ValidWalker t w) : WalkerLastChildResult t w (walkerLastChild t w) := by
  have h := walkerFirstChild_result_sound (wellFormed_mirrorTree hwf) (validWalker_mirrorTree hw)
  rw [← walkerLastChild_eq] at h
  unfold WalkerFirstChildResult FirstIn at h
  unfold WalkerLastChildResult MirrorFirstIn
  simp only [walkerChildCandidate_mirrorTree_iff hwf, accepts_mirrorTree_iff,
    precedesStruct_mirrorTree_iff hwf] at h
  exact h

end Dom.Spec
