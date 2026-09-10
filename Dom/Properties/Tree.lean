import Dom.Basic.WellFormed

/-!
# Phase 1 の theorem

PLAN §4.2 に挙げた性質を証明する。

1. `WellFormed` から parent の一意性が導ける（`unique_parent`）
2. `root` は fuel が store の要素数以上なら停止して結果を返す（`rootFuel_parent_eq_none`）
3. `root t n` は `n` の inclusive ancestor であり、parent を持たない
4. `Ancestor` は well-formed な木で推移的かつ非反射的である
5. `preorder` は重複を持たず、`n` の inclusive descendant をちょうど列挙する
6. `precedes` は `preorder` の順序と一致する
7. `checkWellFormed` の健全性と完全性
-/

namespace Dom

variable {t : Tree}

/-! ## 定義の展開 -/

@[simp] theorem rootFuel_zero (t : Tree) (n : NodeId) : rootFuel t 0 n = n := rfl

theorem rootFuel_succ_none {t : Tree} {f : Nat} {n : NodeId} (h : parentOf t n = none) :
    rootFuel t (f + 1) n = n := by simp [rootFuel, h]

theorem rootFuel_succ_some {t : Tree} {f : Nat} {n p : NodeId} (h : parentOf t n = some p) :
    rootFuel t (f + 1) n = rootFuel t f p := by simp [rootFuel, h]

theorem rootFuel_of_parent_none {t : Tree} {f : Nat} {n : NodeId} (h : parentOf t n = none) :
    rootFuel t f n = n := by
  cases f with
  | zero => rfl
  | succ f => exact rootFuel_succ_none h

@[simp] theorem ancestorChain_zero (t : Tree) (n : NodeId) : ancestorChain t 0 n = [] := rfl

theorem ancestorChain_succ_none {t : Tree} {f : Nat} {n : NodeId} (h : parentOf t n = none) :
    ancestorChain t (f + 1) n = [] := by simp [ancestorChain, h]

theorem ancestorChain_succ_some {t : Tree} {f : Nat} {n p : NodeId} (h : parentOf t n = some p) :
    ancestorChain t (f + 1) n = p :: ancestorChain t f p := by simp [ancestorChain, h]

theorem contains_eq_true {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    t.contains n = true := by
  show (t.nodes.get? n).isSome = true
  rw [show t.nodes.get? n = some d from h]; rfl

theorem contains_eq_false {t : Tree} {n : NodeId} (h : t.get? n = none) :
    t.contains n = false := by
  show (t.nodes.get? n).isSome = false
  rw [show t.nodes.get? n = none from h]; rfl

@[simp] theorem preorderFuel_zero (t : Tree) (n : NodeId) : preorderFuel t 0 n = [] := rfl

theorem preorderFuel_succ_pos {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d)
    (f : Nat) :
    preorderFuel t (f + 1) n = n :: (childrenOf t n).flatMap (preorderFuel t f) := by
  simp [preorderFuel, contains_eq_true h]

theorem preorderFuel_succ_neg {t : Tree} {n : NodeId} (h : t.get? n = none) (f : Nat) :
    preorderFuel t (f + 1) n = [] := by
  simp [preorderFuel, contains_eq_false h]

/-! ## parent の一意性 -/

/--
PLAN §3.3。`WellFormed` に `uniqueParent` を独立した条件として置かなくてよいことの根拠。

同じ node が二つの node の children に現れることはない。
-/
theorem unique_parent (hwf : WellFormed t) {c p q : NodeId} {pd qd : NodeData}
    (hp : t.get? p = some pd) (hq : t.get? q = some qd)
    (hcp : c ∈ pd.children) (hcq : c ∈ qd.children) : p = q := by
  obtain ⟨cd, hcd, hcdp⟩ := hwf.parent_child p pd hp c hcp
  obtain ⟨cd', hcd', hcdq⟩ := hwf.parent_child q qd hq c hcq
  rw [hcd] at hcd'
  have hcc : cd = cd' := Option.some.inj hcd'
  subst hcc
  rw [hcdp] at hcdq
  exact Option.some.inj hcdq

/-- parent 関係と children 関係の対応（`WellFormed.child_parent` の言い換え）。 -/
theorem mem_childrenOf_of_parentOf (hwf : WellFormed t) {c p : NodeId}
    (h : parentOf t c = some p) : c ∈ childrenOf t p := by
  obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some h
  obtain ⟨pd, hpd, hmem⟩ := hwf.child_parent c cd p hcd hcdp
  rw [childrenOf_eq hpd]; exact hmem

theorem exists_data_of_mem_childrenOf {t : Tree} {c p : NodeId} (h : c ∈ childrenOf t p) :
    ∃ pd, t.get? p = some pd ∧ c ∈ pd.children := by
  cases hpd : t.get? p with
  | none => rw [childrenOf_eq_nil_of_get?_eq_none hpd] at h; simp at h
  | some pd => exact ⟨pd, rfl, by rwa [childrenOf_eq hpd] at h⟩

/-- parent 関係と children 関係の対応（`WellFormed.parent_child` の言い換え）。 -/
theorem parentOf_of_mem_childrenOf (hwf : WellFormed t) {c p : NodeId}
    (h : c ∈ childrenOf t p) : parentOf t c = some p := by
  obtain ⟨pd, hpd, hmem⟩ := exists_data_of_mem_childrenOf h
  obtain ⟨cd, hcd, hcdp⟩ := hwf.parent_child p pd hpd c hmem
  simp [parentOf, hcd, hcdp]

theorem exists_data_of_mem_childrenOf' (hwf : WellFormed t) {c p : NodeId}
    (h : c ∈ childrenOf t p) : ∃ cd, t.get? c = some cd := by
  obtain ⟨cd, hcd, _⟩ := parentOf_eq_some (parentOf_of_mem_childrenOf hwf h)
  exact ⟨cd, hcd⟩

/-! ## ancestor 関係の基本性質 -/

/-- `Ancestor` は well-formed な木で非反射的である。 -/
theorem ancestor_irrefl (hwf : WellFormed t) (n : NodeId) : ¬ Ancestor t n n := hwf.acyclic n

/-- `Ancestor` は非対称である。 -/
theorem ancestor_asymm (hwf : WellFormed t) {a b : NodeId}
    (h₁ : Ancestor t a b) (h₂ : Ancestor t b a) : False :=
  hwf.acyclic a (h₁.trans_ancestor h₂)

theorem ancestor_ne (hwf : WellFormed t) {a b : NodeId} (h : Ancestor t a b) : a ≠ b := by
  rintro rfl; exact hwf.acyclic _ h

/-- ancestor 関係を上端で分解する。preorder の走査は上から下へ進むのでこの向きが要る。 -/
theorem Ancestor.exists_child {t : Tree} {n x : NodeId} (h : Ancestor t n x) :
    ∃ c, parentOf t c = some n ∧ InclusiveAncestor t c x := by
  induction h with
  | @step m hp => exact ⟨m, hp, Or.inl rfl⟩
  | @trans m b hp _ ih =>
    obtain ⟨c, hc, hcb⟩ := ih
    exact ⟨c, hc, Or.inr (Ancestor.of_parent_inclusive hp hcb)⟩

/--
祖先の線形性。同じ node の二つの ancestor は、一方が他方の ancestor である。

parent が `Option` で一意なことから従う。部分木の互いの素性の証明で使う。
-/
theorem ancestor_linear {t : Tree} {a x : NodeId} (hax : Ancestor t a x) :
    ∀ (b : NodeId), InclusiveAncestor t b x → InclusiveAncestor t a b ∨ Ancestor t b a := by
  induction hax with
  | @step m hp =>
    intro b hb
    rcases hb with rfl | hb
    · exact Or.inl (Or.inr (Ancestor.step hp))
    · obtain ⟨p, hp', hcase⟩ := hb.cases_parent
      rw [hp] at hp'
      have hpa : p = a := (Option.some.inj hp').symm
      subst hpa
      rcases hcase with rfl | h
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h
  | @trans m c hp hprev ih =>
    intro b hb
    rcases hb with rfl | hb
    · exact Or.inl (Or.inr (Ancestor.trans hp hprev))
    · obtain ⟨p, hp', hcase⟩ := hb.cases_parent
      rw [hp] at hp'
      have hpm : p = m := (Option.some.inj hp').symm
      subst hpm
      refine ih b ?_
      rcases hcase with rfl | h
      · exact Or.inl rfl
      · exact Or.inr h

theorem inclusive_ancestor_linear {t : Tree} {a b x : NodeId}
    (hax : InclusiveAncestor t a x) (hbx : InclusiveAncestor t b x) :
    InclusiveAncestor t a b ∨ InclusiveAncestor t b a := by
  rcases hax with rfl | hax
  · exact Or.inr hbx
  · rcases ancestor_linear hax b hbx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- 相異なる兄弟の部分木は交わらない。 -/
theorem sibling_subtrees_disjoint (hwf : WellFormed t) {n c₁ c₂ x : NodeId}
    (h₁ : parentOf t c₁ = some n) (h₂ : parentOf t c₂ = some n) (hne : c₁ ≠ c₂)
    (hx₁ : InclusiveAncestor t c₁ x) (hx₂ : InclusiveAncestor t c₂ x) : False := by
  have key : ∀ (a b : NodeId), parentOf t a = some n → parentOf t b = some n →
      Ancestor t a b → False := by
    intro a b ha hb hab
    obtain ⟨p, hp, hcase⟩ := hab.cases_parent
    rw [hb] at hp
    have : p = n := (Option.some.inj hp).symm
    subst this
    rcases hcase with rfl | h
    · exact hwf.acyclic _ (Ancestor.step ha)
    · exact hwf.acyclic _ ((Ancestor.step ha).trans_ancestor h)
  rcases inclusive_ancestor_linear hx₁ hx₂ with h | h
  · rcases h with rfl | h
    · exact hne rfl
    · exact key c₁ c₂ h₁ h₂ h
  · rcases h with rfl | h
    · exact hne rfl
    · exact key c₂ c₁ h₂ h₁ h

/-! ## 祖先の連鎖と fuel の充足性 -/

theorem mem_ancestorChain_ancestor {t : Tree} :
    ∀ (f : Nat) (n a : NodeId), a ∈ ancestorChain t f n → Ancestor t a n := by
  intro f
  induction f with
  | zero => intro n a h; simp at h
  | succ f ih =>
    intro n a h
    cases hp : parentOf t n with
    | none => rw [ancestorChain_succ_none hp] at h; simp at h
    | some p =>
      rw [ancestorChain_succ_some hp] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Ancestor.step hp
      · exact Ancestor.trans hp (ih p a h)

theorem ancestorChain_length_le_fuel {t : Tree} :
    ∀ (f : Nat) (n : NodeId), (ancestorChain t f n).length ≤ f := by
  intro f
  induction f with
  | zero => intro n; simp
  | succ f ih =>
    intro n
    cases hp : parentOf t n with
    | none => rw [ancestorChain_succ_none hp]; simp
    | some p => rw [ancestorChain_succ_some hp]; simpa using Nat.succ_le_succ (ih p)

theorem ancestorChain_nodup (hwf : WellFormed t) :
    ∀ (f : Nat) (n : NodeId), (ancestorChain t f n).Nodup := by
  intro f
  induction f with
  | zero => intro n; simp
  | succ f ih =>
    intro n
    cases hp : parentOf t n with
    | none => rw [ancestorChain_succ_none hp]; simp
    | some p =>
      rw [ancestorChain_succ_some hp]
      refine List.nodup_cons.mpr ⟨?_, ih p⟩
      intro hmem
      exact hwf.acyclic p (mem_ancestorChain_ancestor f p p hmem)

theorem ancestorChain_subset_keys (hwf : WellFormed t) :
    ∀ (f : Nat) (n : NodeId), ancestorChain t f n ⊆ t.nodes.keys := by
  intro f
  induction f with
  | zero => intro n; simp [List.subset_def]
  | succ f ih =>
    intro n
    cases hp : parentOf t n with
    | none => rw [ancestorChain_succ_none hp]; simp [List.subset_def]
    | some p =>
      rw [ancestorChain_succ_some hp]
      obtain ⟨nd, hnd, hndp⟩ := parentOf_eq_some hp
      obtain ⟨pd, hpd, _⟩ := hwf.child_parent n nd p hnd hndp
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact NodeStore.mem_keys_of_get?_eq_some hpd
      · exact ih p hx

/-- 木に含まれる node の祖先の連鎖は、store の要素数より短い。 -/
theorem ancestorChain_length_lt_size (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (f : Nat) : (ancestorChain t f n).length < t.size := by
  have hnd : (n :: ancestorChain t f n).Nodup :=
    List.nodup_cons.mpr
      ⟨fun h => hwf.acyclic n (mem_ancestorChain_ancestor f n n h), ancestorChain_nodup hwf f n⟩
  have hsub : (n :: ancestorChain t f n) ⊆ t.nodes.keys := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact NodeStore.mem_keys_of_get?_eq_some hn
    · exact ancestorChain_subset_keys hwf f n hx
  have hle := Dom.ListUtil.length_le_of_nodup_subset hnd hsub
  rw [NodeStore.length_keys] at hle
  simp only [List.length_cons] at hle
  show _ < t.nodes.size
  omega

/-! ## root -/

theorem rootFuel_inclusive_ancestor (t : Tree) :
    ∀ (f : Nat) (n : NodeId), InclusiveAncestor t (rootFuel t f n) n := by
  intro f
  induction f with
  | zero => intro n; exact Or.inl rfl
  | succ f ih =>
    intro n
    cases hp : parentOf t n with
    | none => rw [rootFuel_succ_none hp]; exact Or.inl rfl
    | some p =>
      rw [rootFuel_succ_some hp]
      exact Or.inr (Ancestor.of_parent_inclusive hp (ih p))

/-- fuel を使い切ったなら、祖先の連鎖はちょうど fuel の長さである。 -/
theorem ancestorChain_length_eq_of_not_root {t : Tree} :
    ∀ (f : Nat) (n : NodeId), parentOf t (rootFuel t f n) ≠ none →
      (ancestorChain t f n).length = f := by
  intro f
  induction f with
  | zero => intro n _; simp
  | succ f ih =>
    intro n h
    cases hp : parentOf t n with
    | none => rw [rootFuel_of_parent_none hp] at h; exact absurd hp h
    | some p =>
      rw [rootFuel_succ_some hp] at h
      rw [ancestorChain_succ_some hp]
      simp [ih p h]

/--
PLAN §4.2。fuel が store の要素数以上なら、`rootFuel` は parent を持たない node で止まる。

`memo.md` の言う「fuel が尽きない」ことの形式化である。
-/
theorem rootFuel_parent_eq_none (hwf : WellFormed t) {f : Nat} (hf : t.size ≤ f) (n : NodeId) :
    parentOf t (rootFuel t f n) = none := by
  cases hr : parentOf t (rootFuel t f n) with
  | none => rfl
  | some p =>
    exfalso
    have h : parentOf t (rootFuel t f n) ≠ none := by rw [hr]; simp
    cases hn : t.get? n with
    | none =>
      rw [rootFuel_of_parent_none (parentOf_eq_none_of_get?_eq_none hn)] at h
      exact h (parentOf_eq_none_of_get?_eq_none hn)
    | some d =>
      have hlen := ancestorChain_length_eq_of_not_root f n h
      have hlt := ancestorChain_length_lt_size hwf hn f
      omega

/-- PLAN §4.2。`root t n` は parent を持たない。 -/
theorem root_parent_eq_none (hwf : WellFormed t) (n : NodeId) : parentOf t (root t n) = none :=
  rootFuel_parent_eq_none hwf (Nat.le_refl _) n

/-- PLAN §4.2。`root t n` は `n` の inclusive ancestor である。 -/
theorem root_inclusive_ancestor (t : Tree) (n : NodeId) : InclusiveAncestor t (root t n) n :=
  rootFuel_inclusive_ancestor t _ n

/-- parent を持たない inclusive ancestor は一意であり、それが root である。 -/
theorem root_unique (hwf : WellFormed t) {n r : NodeId}
    (hr : InclusiveAncestor t r n) (hrp : parentOf t r = none) : root t n = r := by
  rcases inclusive_ancestor_linear (root_inclusive_ancestor t n) hr with h | h
  · rcases h with h | h
    · exact h
    · exact absurd (h.parent_isSome) (by simp [hrp])
  · rcases h with h | h
    · exact h.symm
    · exact absurd (h.parent_isSome) (by simp [root_parent_eq_none hwf n])

/-- 同じ木に属する node は同じ root を持つ。 -/
theorem root_eq_of_ancestor (hwf : WellFormed t) {a b : NodeId} (h : Ancestor t a b) :
    root t b = root t a := by
  refine root_unique hwf ?_ (root_parent_eq_none hwf a)
  rcases root_inclusive_ancestor t a with hr | hr
  · exact Or.inr (by rw [hr]; exact h)
  · exact Or.inr (hr.trans_ancestor h)

/-! ## 深さ -/

theorem ancestorChain_succ_eq_of_length_lt {t : Tree} :
    ∀ (f : Nat) (n : NodeId), (ancestorChain t f n).length < f →
      ancestorChain t (f + 1) n = ancestorChain t f n := by
  intro f
  induction f with
  | zero => intro n h; simp at h
  | succ f ih =>
    intro n h
    cases hp : parentOf t n with
    | none => rw [ancestorChain_succ_none hp, ancestorChain_succ_none hp]
    | some p =>
      rw [ancestorChain_succ_some hp] at h ⊢
      simp only [List.length_cons] at h
      rw [ancestorChain_succ_some hp, ih p (by omega)]

theorem ancestorChain_eq_of_length_lt {t : Tree} {f : Nat} {n : NodeId}
    (h : (ancestorChain t f n).length < f) :
    ∀ (g : Nat), f ≤ g → ancestorChain t g n = ancestorChain t f n := by
  intro g
  induction g with
  | zero =>
    intro hg
    have hf : f = 0 := Nat.le_zero.mp hg
    subst hf; rfl
  | succ g ih =>
    intro hg
    rcases Nat.lt_or_ge g f with hlt | hge
    · have hf : f = g + 1 := by omega
      subst hf; rfl
    · have heq := ih hge
      have hlt' : (ancestorChain t g n).length < g := by rw [heq]; omega
      rw [ancestorChain_succ_eq_of_length_lt g n hlt', heq]

/-- 木に含まれる node の深さは store の要素数より小さい。 -/
theorem depth_lt_size (hwf : WellFormed t) {n : NodeId} {d : NodeData} (hn : t.get? n = some d) :
    depth t n < t.size :=
  ancestorChain_length_lt_size hwf hn t.size

/-- 深さは parent から一段ずつ増える。`preorder` の正しさの証明で減少量として使う。 -/
theorem depth_parent (hwf : WellFormed t) {c n : NodeId} (hp : parentOf t c = some n) :
    depth t c = depth t n + 1 := by
  obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
  obtain ⟨m, hm⟩ : ∃ m, t.size = m + 1 := by
    have := ancestorChain_length_lt_size hwf hcd 0
    exact ⟨t.size - 1, by omega⟩
  have hchain : (ancestorChain t m n).length < m := by
    rcases Nat.lt_or_ge (ancestorChain t m n).length m with hlt | hge
    · exact hlt
    · exfalso
      have hle := ancestorChain_length_le_fuel (t := t) m n
      have heq : (ancestorChain t m n).length = m := by omega
      have hbig : (ancestorChain t (m + 1) c).length = m + 1 := by
        rw [ancestorChain_succ_some hp]; simp [heq]
      have := ancestorChain_length_lt_size hwf hcd (m + 1)
      omega
  have hstable : ancestorChain t (m + 1) n = ancestorChain t m n :=
    ancestorChain_eq_of_length_lt hchain (m + 1) (Nat.le_succ m)
  show (ancestors t c).length = (ancestors t n).length + 1
  unfold ancestors
  rw [hm, ancestorChain_succ_some hp, hstable]
  simp

/-! ## preorder -/

theorem preorderFuel_mono {t : Tree} :
    ∀ (f g : Nat), f ≤ g → ∀ (n x : NodeId), x ∈ preorderFuel t f n → x ∈ preorderFuel t g n := by
  intro f
  induction f with
  | zero => intro g _ n x h; simp at h
  | succ f ih =>
    intro g hg n x h
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn] at h; simp at h
    | some d =>
      rw [preorderFuel_succ_pos hn] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp h
        exact List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨c, hc, ih g (by omega) c x hxc⟩)

/-- `preorder` が列挙するのは inclusive descendant だけである。 -/
theorem inclusive_descendant_of_mem_preorderFuel (hwf : WellFormed t) :
    ∀ (f : Nat) (n x : NodeId), x ∈ preorderFuel t f n → InclusiveDescendant t x n := by
  intro f
  induction f with
  | zero => intro n x h; simp at h
  | succ f ih =>
    intro n x h
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn] at h; simp at h
    | some d =>
      rw [preorderFuel_succ_pos hn] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp h
        have hcp : parentOf t c = some n := parentOf_of_mem_childrenOf hwf hc
        have hnc : Ancestor t n c := Ancestor.step hcp
        rcases (ih c x hxc : InclusiveAncestor t c x) with rfl | hcx
        · exact Or.inr hnc
        · exact Or.inr (hnc.trans_ancestor hcx)

theorem exists_data_of_mem_preorderFuel {t : Tree} :
    ∀ (f : Nat) (n x : NodeId), x ∈ preorderFuel t f n → ∃ d, t.get? x = some d := by
  intro f
  induction f with
  | zero => intro n x h; simp at h
  | succ f ih =>
    intro n x h
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn] at h; simp at h
    | some d =>
      rw [preorderFuel_succ_pos hn] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨d, hn⟩
      · obtain ⟨c, _, hxc⟩ := List.mem_flatMap.mp h
        exact ih c x hxc

/-- fuel が「store の要素数 − 深さ」以上なら、inclusive descendant はすべて列挙される。 -/
theorem mem_preorderFuel_of_inclusive_descendant (hwf : WellFormed t) :
    ∀ (k : Nat) (n : NodeId) (d : NodeData), t.get? n = some d → t.size - depth t n ≤ k →
      ∀ (x : NodeId), InclusiveDescendant t x n → x ∈ preorderFuel t k n := by
  intro k
  induction k with
  | zero =>
    intro n d hn hk _ _
    exfalso
    have := depth_lt_size hwf hn
    omega
  | succ k ih =>
    intro n d hn hk x hx
    rw [preorderFuel_succ_pos hn]
    rcases hx with rfl | hx
    · exact List.mem_cons_self ..
    · obtain ⟨c, hcp, hcx⟩ := hx.exists_child
      obtain ⟨cd, hcd, _⟩ := parentOf_eq_some hcp
      have hmem : c ∈ childrenOf t n := mem_childrenOf_of_parentOf hwf hcp
      have hdepth : depth t c = depth t n + 1 := depth_parent hwf hcp
      refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hmem, ?_⟩)
      exact ih c cd hcd (by omega) x hcx

/-- PLAN §4.2。`preorder t n` は `n` の inclusive descendant をちょうど列挙する。 -/
theorem mem_preorder_iff (hwf : WellFormed t) {n : NodeId} {d : NodeData} (hn : t.get? n = some d)
    (x : NodeId) : x ∈ preorder t n ↔ InclusiveDescendant t x n := by
  constructor
  · exact inclusive_descendant_of_mem_preorderFuel hwf t.size n x
  · exact mem_preorderFuel_of_inclusive_descendant hwf t.size n d hn (Nat.sub_le _ _) x

/-- PLAN §4.2。`preorder` の結果は重複を持たない。 -/
theorem preorderFuel_nodup (hwf : WellFormed t) :
    ∀ (f : Nat) (n : NodeId), (preorderFuel t f n).Nodup := by
  intro f
  induction f with
  | zero => intro n; simp
  | succ f ih =>
    intro n
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn]; simp
    | some d =>
      rw [preorderFuel_succ_pos hn]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        obtain ⟨c, hc, hnc⟩ := List.mem_flatMap.mp hmem
        have hcp : parentOf t c = some n := parentOf_of_mem_childrenOf hwf hc
        have : InclusiveDescendant t n c := inclusive_descendant_of_mem_preorderFuel hwf f c n hnc
        rcases this with rfl | h
        · exact hwf.acyclic _ (Ancestor.step hcp)
        · exact hwf.acyclic _ ((Ancestor.step hcp).trans_ancestor h)
      · refine Dom.ListUtil.nodup_flatMap ?_ (fun c _ => ih c) ?_
        · rw [childrenOf_eq hn]; exact hwf.children_nodup n d hn
        · intro c₁ h₁ c₂ h₂ hne x hx₁ hx₂
          exact sibling_subtrees_disjoint hwf
            (parentOf_of_mem_childrenOf hwf h₁) (parentOf_of_mem_childrenOf hwf h₂) hne
            (inclusive_descendant_of_mem_preorderFuel hwf f c₁ x hx₁)
            (inclusive_descendant_of_mem_preorderFuel hwf f c₂ x hx₂)

theorem preorder_nodup (hwf : WellFormed t) (n : NodeId) : (preorder t n).Nodup :=
  preorderFuel_nodup hwf t.size n

theorem treeOrder_nodup (hwf : WellFormed t) (n : NodeId) : (treeOrder t n).Nodup :=
  preorder_nodup hwf _

/-- 木に含まれる node の root もまた木に含まれる。 -/
theorem exists_data_root (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : ∃ rd, t.get? (root t n) = some rd := by
  rcases root_inclusive_ancestor t n with heq | hanc
  · exact ⟨d, by rw [heq]; exact hn⟩
  · obtain ⟨c, hc, _⟩ := hanc.exists_child
    obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hc
    obtain ⟨pd, hpd, _⟩ := hwf.child_parent c cd _ hcd hcdp
    exact ⟨pd, hpd⟩

/-- 木に含まれる node は自分の属する木の tree order に現れる。 -/
theorem mem_treeOrder_self (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : n ∈ treeOrder t n := by
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hn
  exact (mem_preorder_iff hwf hrd n).mpr (root_inclusive_ancestor t n)

/-- 木に含まれる node の parent もまた木に含まれる。 -/
theorem exists_data_of_parentOf (hwf : WellFormed t) {n p : NodeId}
    (h : parentOf t n = some p) : ∃ pd, t.get? p = some pd := by
  obtain ⟨nd, hnd, hndp⟩ := parentOf_eq_some h
  obtain ⟨pd, hpd, _⟩ := hwf.child_parent n nd p hnd hndp
  exact ⟨pd, hpd⟩

/-! ## tree order での先行関係 -/

@[simp] theorem precedesIn_nil (a b : NodeId) : precedesIn [] a b = false := rfl

theorem precedesIn_cons_self (a b : NodeId) (l : List NodeId) :
    precedesIn (a :: l) a b = decide (b ∈ l) := by simp [precedesIn]

theorem precedesIn_cons_target {x a b : NodeId} (hxa : x ≠ a) (hxb : x = b) (l : List NodeId) :
    precedesIn (x :: l) a b = false := by
  subst hxb
  simp [precedesIn, hxa]

theorem precedesIn_cons_ne {x a b : NodeId} (hxa : x ≠ a) (hxb : x ≠ b) (l : List NodeId) :
    precedesIn (x :: l) a b = precedesIn l a b := by simp [precedesIn, hxa, hxb]

/--
PLAN §4.2。`precedes` は列挙における出現位置の比較と一致する。

`precedesIn` が「最初の出現位置の比較」であることを述べたもので、
`precedes` が `preorder`（tree order）の順序そのものであることを意味する。
-/
theorem precedesIn_iff_idx {a b : NodeId} (hab : a ≠ b) :
    ∀ (l : List NodeId), a ∈ l → b ∈ l →
      (precedesIn l a b = true ↔ Dom.ListUtil.idx l a < Dom.ListUtil.idx l b) := by
  intro l
  induction l with
  | nil => intro ha; simp at ha
  | cons x rest ih =>
    intro ha hb
    by_cases hxa : x = a
    · subst hxa
      have hb' : b ∈ rest := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm hab
        · exact h
      rw [precedesIn_cons_self, Dom.ListUtil.idx_cons_self, Dom.ListUtil.idx_cons_ne hab]
      simp [hb']
    · by_cases hxb : x = b
      · subst hxb
        have ha' : a ∈ rest := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hxa
          · exact h
        rw [precedesIn_cons_target hxa rfl, Dom.ListUtil.idx_cons_self,
          Dom.ListUtil.idx_cons_ne (Ne.symm hab)]
        simp
      · have ha' : a ∈ rest := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hxa
          · exact h
        have hb' : b ∈ rest := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h.symm hxb
          · exact h
        rw [precedesIn_cons_ne hxa hxb, Dom.ListUtil.idx_cons_ne hxa, Dom.ListUtil.idx_cons_ne hxb]
        simpa using ih ha' hb'

/-- `precedes` は tree order の列挙における出現順序と一致する。 -/
theorem precedes_iff_idx (t : Tree) {a b : NodeId} (hab : a ≠ b)
    (ha : a ∈ treeOrder t a) (hb : b ∈ treeOrder t a) :
    precedes t a b = true ↔
      Dom.ListUtil.idx (treeOrder t a) a < Dom.ListUtil.idx (treeOrder t a) b :=
  precedesIn_iff_idx hab (treeOrder t a) ha hb

theorem precedesIn_append_of_not_mem {a b : NodeId} :
    ∀ (l₁ l₂ : List NodeId), a ∉ l₁ → b ∉ l₁ →
      precedesIn (l₁ ++ l₂) a b = precedesIn l₂ a b := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _; simp
  | cons x rest ih =>
    intro l₂ ha hb
    have hxa : x ≠ a := fun h => ha (h ▸ List.mem_cons_self ..)
    have hxb : x ≠ b := fun h => hb (h ▸ List.mem_cons_self ..)
    rw [List.cons_append, precedesIn_cons_ne hxa hxb]
    exact ih l₂ (fun h => ha (List.mem_cons_of_mem _ h)) (fun h => hb (List.mem_cons_of_mem _ h))

theorem precedesIn_append_left {a b : NodeId} :
    ∀ (l₁ l₂ : List NodeId), precedesIn l₁ a b = true → precedesIn (l₁ ++ l₂) a b = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; simp at h
  | cons x rest ih =>
    intro l₂ h
    by_cases hxa : x = a
    · subst hxa
      rw [precedesIn_cons_self] at h
      rw [List.cons_append, precedesIn_cons_self]
      simp only [decide_eq_true_eq] at h ⊢
      exact List.mem_append_left _ h
    · by_cases hxb : x = b
      · rw [precedesIn_cons_target hxa hxb] at h; simp at h
      · rw [precedesIn_cons_ne hxa hxb] at h
        rw [List.cons_append, precedesIn_cons_ne hxa hxb]
        exact ih l₂ h

/--
tree order では ancestor が descendant に先行する。

`preorder` の構成上、node は自分の部分木の先頭に来ることの帰結である。
-/
theorem precedesIn_preorderFuel_of_ancestor (hwf : WellFormed t) :
    ∀ (k : Nat) (r : NodeId) (rd : NodeData), t.get? r = some rd → t.size - depth t r ≤ k →
      ∀ (a b : NodeId), Ancestor t a b → InclusiveDescendant t a r →
        precedesIn (preorderFuel t k r) a b = true := by
  intro k
  induction k with
  | zero =>
    intro r rd hr hk _ _ _ _
    exfalso
    have := depth_lt_size hwf hr
    omega
  | succ k ih =>
    intro r rd hr hk a b hab har
    rw [preorderFuel_succ_pos hr]
    by_cases hra : r = a
    · subst hra
      rw [precedesIn_cons_self]
      have hbmem : b ∈ preorderFuel t (k + 1) r :=
        mem_preorderFuel_of_inclusive_descendant hwf (k + 1) r rd hr hk b (Or.inr hab)
      rw [preorderFuel_succ_pos hr] at hbmem
      rcases List.mem_cons.mp hbmem with h | h
      · exact absurd (h ▸ hab) (hwf.acyclic r)
      · simp [h]
    · by_cases hrb : r = b
      · exfalso
        subst hrb
        rcases har with h | h
        · exact hra h
        · exact hwf.acyclic r (h.trans_ancestor hab)
      · rw [precedesIn_cons_ne hra hrb]
        have hanc : Ancestor t r a := by
          rcases har with h | h
          · exact absurd h hra
          · exact h
        obtain ⟨c, hcp, hca⟩ := hanc.exists_child
        obtain ⟨cd, hcd, _⟩ := parentOf_eq_some hcp
        have hcmem : c ∈ childrenOf t r := mem_childrenOf_of_parentOf hwf hcp
        have hdepth : depth t c = depth t r + 1 := depth_parent hwf hcp
        have hcb : InclusiveAncestor t c b := by
          rcases hca with rfl | h
          · exact Or.inr hab
          · exact Or.inr (h.trans_ancestor hab)
        obtain ⟨s₁, s₂, hsplit⟩ := Dom.ListUtil.mem_split hcmem
        have hnodup : (childrenOf t r).Nodup := by
          rw [childrenOf_eq hr]; exact hwf.children_nodup r rd hr
        have hcnot : c ∉ s₁ := by
          rw [hsplit] at hnodup
          intro h
          exact (List.nodup_append.mp hnodup).2.2 c h c (List.mem_cons_self ..) rfl
        have hs₁sub : ∀ c' ∈ s₁, c' ∈ childrenOf t r := by
          intro c' h; rw [hsplit]; exact List.mem_append_left _ h
        have hdisj : ∀ (y : NodeId), InclusiveAncestor t c y →
            y ∉ s₁.flatMap (preorderFuel t k) := by
          intro y hy hmem
          obtain ⟨c', hc', hyc'⟩ := List.mem_flatMap.mp hmem
          have hne : c ≠ c' := fun h => hcnot (h ▸ hc')
          exact sibling_subtrees_disjoint hwf hcp
            (parentOf_of_mem_childrenOf hwf (hs₁sub c' hc')) hne hy
            (inclusive_descendant_of_mem_preorderFuel hwf k c' y hyc')
        rw [hsplit, List.flatMap_append, List.flatMap_cons]
        rw [precedesIn_append_of_not_mem _ _ (hdisj a hca) (hdisj b hcb)]
        exact precedesIn_append_left _ _ (ih c cd hcd (by omega) a b hab hca)

/-- PLAN §4.2。ancestor は tree order で descendant に先行する。 -/
theorem precedes_of_ancestor (hwf : WellFormed t) {a b : NodeId} (h : Ancestor t a b) :
    precedes t a b = true := by
  obtain ⟨c, hc, _⟩ := h.exists_child
  obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hc
  obtain ⟨ad, had, _⟩ := hwf.child_parent c cd a hcd hcdp
  obtain ⟨rd, hrd⟩ := exists_data_root hwf had
  show precedesIn (preorderFuel t t.size (root t a)) a b = true
  exact precedesIn_preorderFuel_of_ancestor hwf t.size (root t a) rd hrd (Nat.sub_le _ _)
    a b h (root_inclusive_ancestor t a)

/-! ## `checkWellFormed` の健全性と完全性 -/

theorem NodeStore.checkAll_iff (s : NodeStore) (p : NodeId → NodeData → Bool) :
    s.checkAll p = true ↔ ∀ n d, s.get? n = some d → p n d = true := by
  simp only [NodeStore.checkAll]
  constructor
  · intro h n d hn
    have hk : n ∈ s.keys := NodeStore.mem_keys_of_get?_eq_some hn
    have := List.all_eq_true.mp h n hk
    simpa [hn] using this
  · intro h
    refine List.all_eq_true.mpr ?_
    intro k _
    cases hd : s.get? k with
    | none => simp
    | some d => simpa [hd] using h k d hd

theorem checkParentChild_iff (t : Tree) :
    t.checkParentChild = true ↔
      ∀ p pd, t.get? p = some pd →
        ∀ c ∈ pd.children, ∃ cd, t.get? c = some cd ∧ cd.parent = some p := by
  simp only [Tree.checkParentChild]
  rw [NodeStore.checkAll_iff]
  constructor
  · intro h p pd hp c hc
    have hall := List.all_eq_true.mp (h p pd hp) c hc
    cases hcd : t.get? c with
    | none => simp [hcd] at hall
    | some cd =>
      simp only [hcd] at hall
      exact ⟨cd, rfl, by simpa using hall⟩
  · intro h p pd hp
    refine List.all_eq_true.mpr ?_
    intro c hc
    obtain ⟨cd, hcd, hcdp⟩ := h p pd hp c hc
    simp [hcd, hcdp]

theorem checkChildParent_iff (t : Tree) :
    t.checkChildParent = true ↔
      ∀ c cd p, t.get? c = some cd → cd.parent = some p →
        ∃ pd, t.get? p = some pd ∧ c ∈ pd.children := by
  simp only [Tree.checkChildParent]
  rw [NodeStore.checkAll_iff]
  constructor
  · intro h c cd p hc hcp
    have hall := h c cd hc
    simp only [hcp] at hall
    cases hpd : t.get? p with
    | none => simp [hpd] at hall
    | some pd =>
      simp only [hpd] at hall
      exact ⟨pd, rfl, by simpa using hall⟩
  · intro h c cd hc
    cases hcp : cd.parent with
    | none => simp
    | some p =>
      obtain ⟨pd, hpd, hmem⟩ := h c cd p hc hcp
      simp [hpd, hmem]

theorem checkChildrenNodup_iff (t : Tree) :
    t.checkChildrenNodup = true ↔ ∀ n d, t.get? n = some d → d.children.Nodup := by
  simp only [Tree.checkChildrenNodup]
  rw [NodeStore.checkAll_iff]
  constructor
  · intro h n d hn; exact (Dom.ListUtil.nodupB_iff _).mp (h n d hn)
  · intro h n d hn; exact (Dom.ListUtil.nodupB_iff _).mpr (h n d hn)

theorem checkOwnerDocument_iff (t : Tree) :
    t.checkOwnerDocument = true ↔
      ∀ n d, t.get? n = some d →
        ∃ dd, t.get? d.ownerDocument = some dd ∧ dd.kind = .document := by
  simp only [Tree.checkOwnerDocument]
  rw [NodeStore.checkAll_iff]
  constructor
  · intro h n d hn
    have hall := h n d hn
    cases hdd : t.get? d.ownerDocument with
    | none => simp [hdd] at hall
    | some dd =>
      simp only [hdd] at hall
      exact ⟨dd, rfl, by simpa using hall⟩
  · intro h n d hn
    obtain ⟨dd, hdd, hkind⟩ := h n d hn
    simp [hdd, hkind]

/-- cycle 上にある node の inclusive ancestor は、必ず parent を持つ。 -/
theorem parent_isSome_of_ancestor_cycle {t : Tree} {r n : NodeId} (h : Ancestor t r n) :
    Ancestor t n n → ∃ p, parentOf t r = some p := by
  induction h with
  | @step m hp =>
    intro hcyc
    obtain ⟨p, hp', hcase⟩ := hcyc.cases_parent
    rw [hp] at hp'
    have hpr : p = r := (Option.some.inj hp').symm
    subst hpr
    rcases hcase with rfl | h
    · exact ⟨_, hp⟩
    · exact h.parent_isSome
  | @trans m b hp _ ih =>
    intro hcyc
    obtain ⟨p, hp', hcase⟩ := hcyc.cases_parent
    rw [hp] at hp'
    have hpm : p = m := (Option.some.inj hp').symm
    subst hpm
    refine ih ?_
    rcases hcase with rfl | h
    · exact hcyc
    · exact (Ancestor.step hp).trans_ancestor h

theorem checkAcyclic_sound (t : Tree) (h : t.checkAcyclic = true) : ∀ n, ¬ Ancestor t n n := by
  simp only [Tree.checkAcyclic] at h
  intro n hcyc
  obtain ⟨p, hp⟩ := hcyc.parent_isSome
  obtain ⟨nd, hnd, _⟩ := parentOf_eq_some hp
  have hk : n ∈ t.nodes.keys := NodeStore.mem_keys_of_get?_eq_some hnd
  have hterm : parentChainTerminates t t.size n = true :=
    List.all_eq_true.mp h n hk
  have hnone : parentOf t (rootFuel t t.size n) = none := by
    simpa [parentChainTerminates, Option.isNone_iff_eq_none] using hterm
  rcases rootFuel_inclusive_ancestor t t.size n with heq | hanc
  · rw [heq] at hnone; rw [hnone] at hp; simp at hp
  · obtain ⟨q, hq⟩ := parent_isSome_of_ancestor_cycle hanc hcyc
    rw [hnone] at hq; simp at hq

theorem checkAcyclic_complete (hwf : WellFormed t) : t.checkAcyclic = true := by
  simp only [Tree.checkAcyclic]
  refine List.all_eq_true.mpr ?_
  intro n _
  simp [parentChainTerminates, rootFuel_parent_eq_none hwf (Nat.le_refl _) n]

/--
PLAN §3.5 と §4.2。`checkWellFormed` の健全性と完全性。

これにより differential testing の各 step で model の状態が invariant を満たすことを
実行時にも確認できる。
-/
theorem checkWellFormed_iff (t : Tree) : t.checkWellFormed = true ↔ WellFormed t := by
  constructor
  · intro h
    simp only [Tree.checkWellFormed, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact
      { parent_child := (checkParentChild_iff t).mp h1
        child_parent := (checkChildParent_iff t).mp h2
        children_nodup := (checkChildrenNodup_iff t).mp h3
        acyclic := checkAcyclic_sound t h4
        ownerDocument_is_document := (checkOwnerDocument_iff t).mp h5 }
  · intro hwf
    simp only [Tree.checkWellFormed, Bool.and_eq_true]
    exact ⟨⟨⟨⟨(checkParentChild_iff t).mpr hwf.parent_child,
      (checkChildParent_iff t).mpr hwf.child_parent⟩,
      (checkChildrenNodup_iff t).mpr hwf.children_nodup⟩,
      checkAcyclic_complete hwf⟩,
      (checkOwnerDocument_iff t).mpr hwf.ownerDocument_is_document⟩

end Dom
