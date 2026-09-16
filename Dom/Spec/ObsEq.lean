import Dom.Basic.State
import Dom.Properties.TreeOrder

/-!
# 観測が等しいこと

関係意味論を繋いだもの（`insert` のように `remove` や `adopt` を途中に持つもの）の
一意性を言うには、「途中の状態が観測として等しければ、その先も観測として等しい」
という congruence が要る。その土台として、観測の等しさをここで定義する。

木については `get?` が各 node で一致すること（`TreeObsEq`）である。
store は association list なので、同じ `get?` を持つ表現は複数ある。
観測に出るものはすべて `get?` から決まる——ただし `root` と `precedes` だけは
`t.size` を fuel に使うので、well-formed であることを使って別に示す。
-/

namespace Dom.Spec

open Dom

/-- 木の観測が等しいこと。 -/
def TreeObsEq (t t' : Tree) : Prop := ∀ m, t'.get? m = t.get? m

namespace TreeObsEq

variable {t t' : Tree}

theorem refl (t : Tree) : TreeObsEq t t := fun _ => rfl

theorem symm (h : TreeObsEq t t') : TreeObsEq t' t := fun m => (h m).symm

theorem parentOf (h : TreeObsEq t t') (m : NodeId) : Dom.parentOf t' m = Dom.parentOf t m := by
  exact Dom.parentOf_congr (h m)

theorem childrenOf (h : TreeObsEq t t') (m : NodeId) : Dom.childrenOf t' m = Dom.childrenOf t m := by
  unfold Dom.childrenOf; rw [h m]

theorem ownerDocumentOf (h : TreeObsEq t t') (m : NodeId) :
    Dom.ownerDocumentOf t' m = Dom.ownerDocumentOf t m := by
  unfold Dom.ownerDocumentOf; rw [h m]

theorem lengthOf (h : TreeObsEq t t') (m : NodeId) : Dom.lengthOf t' m = Dom.lengthOf t m := by
  unfold Dom.lengthOf; rw [h m]

theorem ancestor (h : TreeObsEq t t') {a n : NodeId} (ha : Ancestor t a n) : Ancestor t' a n := by
  induction ha with
  | step hp => exact Ancestor.step (by rw [h.parentOf]; exact hp)
  | trans hp _ ih => exact Ancestor.trans (by rw [h.parentOf]; exact hp) ih

theorem ancestor_iff (h : TreeObsEq t t') {a n : NodeId} : Ancestor t' a n ↔ Ancestor t a n :=
  ⟨fun ha => h.symm.ancestor ha, fun ha => h.ancestor ha⟩

theorem inclusiveAncestor_iff (h : TreeObsEq t t') {a n : NodeId} :
    InclusiveAncestor t' a n ↔ InclusiveAncestor t a n := by
  unfold InclusiveAncestor
  rw [h.ancestor_iff]

theorem index (h : TreeObsEq t t') (m : NodeId) : Dom.index t' m = Dom.index t m := by
  unfold Dom.index
  rw [h.parentOf]
  cases Dom.parentOf t m with
  | none => rfl
  | some p => simp only [Option.bind_some, h.childrenOf]

theorem previousSibling (h : TreeObsEq t t') (m : NodeId) :
    Dom.previousSibling t' m = Dom.previousSibling t m := by
  unfold Dom.previousSibling
  rw [h.parentOf]
  cases Dom.parentOf t m with
  | none => rfl
  | some p => simp only [h.childrenOf]

theorem nextSibling (h : TreeObsEq t t') (m : NodeId) :
    Dom.nextSibling t' m = Dom.nextSibling t m := by
  unfold Dom.nextSibling
  rw [h.parentOf]
  cases Dom.parentOf t m with
  | none => rfl
  | some p => simp only [h.childrenOf]

/-- `root` は fuel を使うが、well-formed なら一意なので観測から決まる。 -/
theorem root (h : TreeObsEq t t') (hwf : WellFormed t) (hwf' : WellFormed t') (n : NodeId) :
    Dom.root t' n = Dom.root t n :=
  root_unique hwf' (h.inclusiveAncestor_iff.mpr (root_inclusive_ancestor t n))
    (by rw [h.parentOf]; exact root_parent_eq_none hwf n)

theorem precedesStruct_iff (h : TreeObsEq t t') {x y : NodeId} :
    PrecedesStruct t' x y ↔ PrecedesStruct t x y := by
  unfold PrecedesStruct
  constructor
  · rintro (ha | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxcx, hycy⟩)
    · exact Or.inl (h.symm.ancestor ha)
    · refine Or.inr ⟨p, cx, cy, i, j, ?_, ?_, ?_, ?_, hij, ?_, ?_⟩
      · rw [← h.parentOf]; exact hcx
      · rw [← h.parentOf]; exact hcy
      · rw [← h.index]; exact hi
      · rw [← h.index]; exact hj
      · exact h.inclusiveAncestor_iff.mp hxcx
      · exact h.inclusiveAncestor_iff.mp hycy
  · rintro (ha | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxcx, hycy⟩)
    · exact Or.inl (h.ancestor ha)
    · refine Or.inr ⟨p, cx, cy, i, j, ?_, ?_, ?_, ?_, hij, ?_, ?_⟩
      · rw [h.parentOf]; exact hcx
      · rw [h.parentOf]; exact hcy
      · rw [h.index]; exact hi
      · rw [h.index]; exact hj
      · exact h.inclusiveAncestor_iff.mpr hxcx
      · exact h.inclusiveAncestor_iff.mpr hycy

/-- 木に無い node は誰にも先行しない。 -/
theorem preorder_eq_nil_of_none {t : Tree} {n : NodeId} (h : t.get? n = none) :
    preorder t n = [] := by
  unfold preorder
  cases t.size with
  | zero => rfl
  | succ f => exact preorderFuel_succ_neg h f

/-- `x` の木の外にある node へは先行しない。 -/
theorem precedes_eq_false_of_not_descendant {t : Tree} (hwf : WellFormed t) {x y : NodeId}
    {rd : NodeData} (hrd : t.get? (Dom.root t x) = some rd)
    (hy : ¬ InclusiveDescendant t y (Dom.root t x)) : Dom.precedes t x y = false := by
  cases hq : Dom.precedes t x y with
  | false => rfl
  | true =>
    exfalso
    exact hy ((mem_preorder_iff hwf hrd y).mp (mem_of_precedesIn (treeOrder t x) hq))

/--
`precedes` も観測から決まる。

列そのもの（`preorder`）の一致は言わずに、
「tree order の前後は木の構造だけで決まる」（`precedesIn_preorder_iff_struct`）を経由する。
-/
theorem precedes (h : TreeObsEq t t') (hwf : WellFormed t) (hwf' : WellFormed t') (x y : NodeId) :
    Dom.precedes t' x y = Dom.precedes t x y := by
  by_cases hxy : x = y
  · subst hxy
    show precedesIn (treeOrder t' x) x x = precedesIn (treeOrder t x) x x
    rw [precedesIn_self _ _ (treeOrder_nodup hwf' x), precedesIn_self _ _ (treeOrder_nodup hwf x)]
  · cases hxd : t.get? x with
    | none =>
      -- 木に無いので、どちらの側でも列が空である。
      have hp : Dom.parentOf t x = none := Dom.parentOf_eq_none_of_get?_eq_none hxd
      have hr : Dom.root t x = x := root_unique hwf (Or.inl rfl) hp
      have hr' : Dom.root t' x = x := by rw [h.root hwf hwf' x, hr]
      show precedesIn (preorder t' (Dom.root t' x)) x y
          = precedesIn (preorder t (Dom.root t x)) x y
      rw [hr, hr', preorder_eq_nil_of_none hxd, preorder_eq_nil_of_none (by rw [h]; exact hxd)]
    | some xd =>
      have hroot : Dom.root t' x = Dom.root t x := h.root hwf hwf' x
      obtain ⟨rd, hrd⟩ : ∃ rd, t.get? (Dom.root t x) = some rd :=
        exists_data_of_inclusiveAncestor hwf (root_inclusive_ancestor t x) hxd
      by_cases hy : InclusiveDescendant t y (Dom.root t x)
      · have hx : InclusiveDescendant t x (Dom.root t x) := root_inclusive_ancestor t x
        have h1 : Dom.precedes t x y = true ↔ PrecedesStruct t x y :=
          precedesIn_preorder_iff_struct hwf hrd hx hy hxy
        have h2 : Dom.precedes t' x y = true ↔ PrecedesStruct t' x y := by
          show precedesIn (preorder t' (Dom.root t' x)) x y = true ↔ _
          rw [hroot]
          exact precedesIn_preorder_iff_struct hwf' (by rw [h]; exact hrd)
            (h.inclusiveAncestor_iff.mpr hx) (h.inclusiveAncestor_iff.mpr hy) hxy
        cases hb : Dom.precedes t x y <;> cases hb' : Dom.precedes t' x y
        · rfl
        · exact absurd (h1.mpr (h.precedesStruct_iff.mp (h2.mp hb'))) (by simp [hb])
        · exact absurd (h2.mpr (h.precedesStruct_iff.mpr (h1.mp hb))) (by simp [hb'])
        · rfl
      · have hfalse : Dom.precedes t x y = false :=
          precedes_eq_false_of_not_descendant hwf hrd hy
        have hfalse' : Dom.precedes t' x y = false := by
          refine precedes_eq_false_of_not_descendant hwf' (x := x) (y := y)
            (rd := rd) (by rw [hroot, h]; exact hrd) ?_
          rw [hroot]
          intro hc
          exact hy (h.inclusiveAncestor_iff.mp hc)
        rw [hfalse, hfalse']


/-- `WellFormed` は `get?` だけで書かれているので、観測が等しければ移る。 -/
theorem wellFormed (h : TreeObsEq t t') (hwf : WellFormed t) : WellFormed t' where
  parent_child := by
    intro p pd hp c hc
    obtain ⟨cd, hcd, hcp⟩ := hwf.parent_child p pd (by rw [← h]; exact hp) c hc
    exact ⟨cd, by rw [h]; exact hcd, hcp⟩
  child_parent := by
    intro c cd p hc hcp
    obtain ⟨pd, hpd, hmem⟩ := hwf.child_parent c cd p (by rw [← h]; exact hc) hcp
    exact ⟨pd, by rw [h]; exact hpd, hmem⟩
  children_nodup := by
    intro n d hn
    exact hwf.children_nodup n d (by rw [← h]; exact hn)
  acyclic := by
    intro n hn
    exact hwf.acyclic n (h.symm.ancestor hn)
  ownerDocument_is_document := by
    intro n d hn
    obtain ⟨dd, hdd, hkind⟩ := hwf.ownerDocument_is_document n d (by rw [← h]; exact hn)
    exact ⟨dd, by rw [h]; exact hdd, hkind⟩

end TreeObsEq

/-! ## 状態の観測 -/

/--
**状態の観測が等しいこと。**

`Dom/Observation.lean` の `Observation` が見るものの一致である。
木は表現ではなく `get?` で、registered observer list は順序を決めていないので所属で、
observer は record queue だけで比べる（`ObserverState.nodeList` は観測に出ない）。
-/
structure ObsEq (s s' : DOMState) : Prop where
  tree : TreeObsEq s.tree s'.tree
  ranges : s'.ranges = s.ranges
  iterators : s'.iterators = s.iterators
  registrations : ∀ r, r ∈ s'.registrations ↔ r ∈ s.registrations
  records : ∀ mo : Nat, (s'.observers[mo]?).map (·.records) = (s.observers[mo]?).map (·.records)
  pendingObservers : ∀ mo : Nat, mo ∈ s'.pendingObservers ↔ mo ∈ s.pendingObservers
  microtaskQueued : s'.microtaskQueued = s.microtaskQueued

namespace ObsEq

variable {s s' s'' : DOMState}

theorem refl (s : DOMState) : ObsEq s s where
  tree := TreeObsEq.refl s.tree
  ranges := rfl
  iterators := rfl
  registrations := fun _ => Iff.rfl
  records := fun _ => rfl
  pendingObservers := fun _ => Iff.rfl
  microtaskQueued := rfl

theorem symm (h : ObsEq s s') : ObsEq s' s where
  tree := h.tree.symm
  ranges := h.ranges.symm
  iterators := h.iterators.symm
  registrations := fun r => (h.registrations r).symm
  records := fun mo => (h.records mo).symm
  pendingObservers := fun mo => (h.pendingObservers mo).symm
  microtaskQueued := h.microtaskQueued.symm

theorem trans (h : ObsEq s s') (h' : ObsEq s' s'') : ObsEq s s'' where
  tree := fun m => (h'.tree m).trans (h.tree m)
  ranges := h'.ranges.trans h.ranges
  iterators := h'.iterators.trans h.iterators
  registrations := fun r => (h'.registrations r).trans (h.registrations r)
  records := fun mo => (h'.records mo).trans (h.records mo)
  pendingObservers := fun mo => (h'.pendingObservers mo).trans (h.pendingObservers mo)
  microtaskQueued := h'.microtaskQueued.trans h.microtaskQueued

/-- record queue が一致すれば、observer が居るかどうかも一致する。 -/
theorem observers_isSome (h : ObsEq s s') (mo : Nat) :
    (s'.observers[mo]?).isSome = (s.observers[mo]?).isSome := by
  have hr := h.records mo
  cases h1 : s'.observers[mo]? with
  | none =>
    cases h2 : s.observers[mo]? with
    | none => rfl
    | some o => rw [h1, h2] at hr; simp at hr
  | some o' =>
    cases h2 : s.observers[mo]? with
    | none => rw [h1, h2] at hr; simp at hr
    | some o => rfl

/-- したがって observer list の長さも一致する。 -/
theorem observers_length (h : ObsEq s s') : s'.observers.length = s.observers.length := by
  refine Nat.le_antisymm (Nat.not_lt.mp fun hlt => ?_) (Nat.not_lt.mp fun hlt => ?_)
  · have h1 : (s'.observers[s.observers.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem hlt]; rfl
    have h2 : (s.observers[s.observers.length]?) = none :=
      List.getElem?_eq_none (Nat.le_refl _)
    rw [h.observers_isSome, h2] at h1
    exact Bool.noConfusion h1
  · have h1 : (s.observers[s'.observers.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem hlt]; rfl
    have h2 : (s'.observers[s'.observers.length]?) = none :=
      List.getElem?_eq_none (Nat.le_refl _)
    rw [← h.observers_isSome, h2] at h1
    exact Bool.noConfusion h1

/-- 同じ添字の observer の record queue を取り出す。 -/
theorem records_of (h : ObsEq s s') {mo : Nat} {o o' : ObserverState}
    (ho : s.observers[mo]? = some o) (ho' : s'.observers[mo]? = some o') :
    o'.records = o.records := by
  have hr := h.records mo
  rw [ho, ho'] at hr
  exact Option.some.inj hr

/-- observer が片方に居れば、もう片方の同じ添字にも居る。 -/
theorem exists_observer (h : ObsEq s s') {mo : Nat} {o : ObserverState}
    (ho : s.observers[mo]? = some o) :
    ∃ o', s'.observers[mo]? = some o' ∧ o'.records = o.records := by
  have hs := h.observers_isSome mo
  rw [ho] at hs
  cases ho' : s'.observers[mo]? with
  | none => rw [ho'] at hs; exact Bool.noConfusion hs
  | some o' => exact ⟨o', rfl, h.records_of ho ho'⟩

end ObsEq

end Dom.Spec
