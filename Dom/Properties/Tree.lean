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

/-- ancestor の列は parent から一段ずつ伸びる。 -/
theorem ancestors_eq_cons (hwf : WellFormed t) {c n : NodeId} (hp : parentOf t c = some n) :
    ancestors t c = n :: ancestors t n := by
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
  unfold ancestors
  rw [hm, ancestorChain_succ_some hp, hstable]

/-- 深さは parent から一段ずつ増える。`preorder` の正しさの証明で減少量として使う。 -/
theorem depth_parent (hwf : WellFormed t) {c n : NodeId} (hp : parentOf t c = some n) :
    depth t c = depth t n + 1 := by
  show (ancestors t c).length = (ancestors t n).length + 1
  rw [ancestors_eq_cons hwf hp]
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

/-! ## 鏡像の preorder -/

theorem mirrorPreorderFuel_succ_pos {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d)
    (f : Nat) :
    mirrorPreorderFuel t (f + 1) n
      = n :: (childrenOf t n).reverse.flatMap (mirrorPreorderFuel t f) := by
  simp [mirrorPreorderFuel, contains_eq_true h]

theorem mirrorPreorderFuel_succ_neg {t : Tree} {n : NodeId} (h : t.get? n = none) (f : Nat) :
    mirrorPreorderFuel t (f + 1) n = [] := by
  simp [mirrorPreorderFuel, contains_eq_false h]

/-- 鏡像の preorder は、同じ node を並べ替えただけである。 -/
theorem mem_mirrorPreorderFuel_iff {t : Tree} :
    ∀ (f : Nat) (n x : NodeId), x ∈ mirrorPreorderFuel t f n ↔ x ∈ preorderFuel t f n := by
  intro f
  induction f with
  | zero => intro n x; simp [mirrorPreorderFuel]
  | succ f ih =>
    intro n x
    cases hn : t.get? n with
    | none => rw [mirrorPreorderFuel_succ_neg hn, preorderFuel_succ_neg hn]
    | some d =>
      rw [mirrorPreorderFuel_succ_pos hn, preorderFuel_succ_pos hn]
      simp only [List.mem_cons, List.mem_flatMap, List.mem_reverse]
      constructor
      · rintro (rfl | ⟨c, hc, hx⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨c, hc, (ih c x).mp hx⟩
      · rintro (rfl | ⟨c, hc, hx⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨c, hc, (ih c x).mpr hx⟩

theorem mem_mirrorPreorder_iff_mem_preorder {t : Tree} (n x : NodeId) :
    x ∈ mirrorPreorder t n ↔ x ∈ preorder t n :=
  mem_mirrorPreorderFuel_iff _ _ _

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

/-! ## ancestor 関係の決定可能性 -/

/-- fuel を使い切っていない祖先の連鎖は、ancestor をすべて含む。 -/
theorem mem_ancestorChain_of_ancestor {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    ∀ (f : Nat), (ancestorChain t f n).length < f → a ∈ ancestorChain t f n := by
  induction h with
  | @step m hp =>
    intro f hf
    cases f with
    | zero => simp at hf
    | succ f => rw [ancestorChain_succ_some hp]; exact List.mem_cons_self ..
  | @trans m b hp _ ih =>
    intro f hf
    cases f with
    | zero => simp at hf
    | succ f =>
      rw [ancestorChain_succ_some hp] at hf ⊢
      simp only [List.length_cons] at hf
      exact List.mem_cons_of_mem _ (ih f (by omega))

/-- `ancestors` は ancestor をちょうど列挙する。 -/
theorem mem_ancestors_iff (hwf : WellFormed t) (n a : NodeId) :
    a ∈ ancestors t n ↔ Ancestor t a n := by
  constructor
  · exact mem_ancestorChain_ancestor t.size n a
  · intro h
    obtain ⟨p, hp⟩ := h.parent_isSome
    obtain ⟨d, hd, _⟩ := parentOf_eq_some hp
    exact mem_ancestorChain_of_ancestor h t.size (ancestorChain_length_lt_size hwf hd t.size)

/-- PLAN §3.5。`isAncestorOf` の健全性と完全性。 -/
theorem isAncestorOf_iff (hwf : WellFormed t) (a n : NodeId) :
    isAncestorOf t a n = true ↔ Ancestor t a n := by
  simp only [isAncestorOf, decide_eq_true_eq]
  exact mem_ancestors_iff hwf n a

/-- `isInclusiveAncestorOf` の健全性と完全性。 -/
theorem isInclusiveAncestorOf_iff (hwf : WellFormed t) (a n : NodeId) :
    isInclusiveAncestorOf t a n = true ↔ InclusiveAncestor t a n := by
  simp only [isInclusiveAncestorOf, Bool.or_eq_true, decide_eq_true_eq, isAncestorOf_iff hwf]

/-! ## 二つの木の間で ancestor 関係を比べる -/

/-- parent が減る向きの変更では、ancestor 関係も減る。 -/
theorem ancestor_of_parentOf_subset {t t' : Tree}
    (h : ∀ x y, parentOf t' x = some y → parentOf t x = some y) {a n : NodeId}
    (ha : Ancestor t' a n) : Ancestor t a n := by
  induction ha with
  | @step m hp => exact Ancestor.step (h _ _ hp)
  | @trans m b hp _ ih => exact Ancestor.trans (h _ _ hp) ih

/--
parent の辺を一本だけ足したときの ancestor 関係。

`t'` は `t` に「`node` の parent は `parent`」という辺だけを足した木とする。
このとき `t'` の ancestor 関係は、`t` の ancestor 関係か、
足した辺を一度通る経路のどちらかである。

`insertAt` の acyclicity 保存の証明に使う。
-/
theorem ancestor_of_parentOf_insert {t t' : Tree} {node parent : NodeId}
    (hnode : parentOf t' node = some parent)
    (hother : ∀ x, x ≠ node → parentOf t' x = parentOf t x) {a b : NodeId}
    (h : Ancestor t' a b) :
    Ancestor t a b ∨ (InclusiveAncestor t node b ∧ InclusiveAncestor t a parent) := by
  induction h with
  | @step m hp =>
    by_cases hm : m = node
    · subst hm
      rw [hnode] at hp
      have : a = parent := (Option.some.inj hp).symm
      subst this
      exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inl (Ancestor.step (by rw [← hother m hm]; exact hp))
  | @trans m c hp _ ih =>
    by_cases hc : c = node
    · have hmp : m = parent := by
        rw [hc, hnode] at hp
        exact (Option.some.inj hp).symm
      subst hmp
      refine Or.inr ⟨?_, ?_⟩
      · rw [hc]; exact Or.inl rfl
      · rcases ih with hac | ⟨_, hap⟩
        · exact Or.inr hac
        · exact hap
    · have hp' : parentOf t c = some m := by rw [← hother c hc]; exact hp
      rcases ih with hac | ⟨hnm, hap⟩
      · exact Or.inl (Ancestor.trans hp' hac)
      · exact Or.inr ⟨Or.inr (Ancestor.of_parent_inclusive hp' hnm), hap⟩

theorem InclusiveAncestor.trans_inclusive {t : Tree} {a b c : NodeId}
    (hab : InclusiveAncestor t a b) (hbc : InclusiveAncestor t b c) : InclusiveAncestor t a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (hab.trans_ancestor hbc)

/-! ## 兄弟の部分木の先行関係

`precedes` を tree order の列挙から構造的な条件へ言い換えるための補題を並べる。
「前の兄弟の部分木は後の兄弟の部分木より先行する」が中心である。
-/

theorem precedesIn_append_of_mem_left {a b : NodeId} :
    ∀ (l₁ l₂ : List NodeId), a ∈ l₁ → b ∉ l₁ → b ∈ l₂ →
      precedesIn (l₁ ++ l₂) a b = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ ha; simp at ha
  | cons x rest ih =>
    intro l₂ ha hb hb2
    have hxb : x ≠ b := fun he => hb (he ▸ List.mem_cons_self ..)
    by_cases hxa : x = a
    · subst hxa
      rw [List.cons_append, precedesIn_cons_self]
      simp only [decide_eq_true_eq]
      exact List.mem_append_right _ hb2
    · rw [List.cons_append, precedesIn_cons_ne hxa hxb]
      refine ih l₂ ?_ (fun h => hb (List.mem_cons_of_mem _ h)) hb2
      rcases List.mem_cons.mp ha with he | he
      · exact absurd he.symm hxa
      · exact he

/--
`cs` の中で `cx` が `cy` より前にあり、各 node の列が互いに素なら、
`cx` の列の要素は `cy` の列の要素より先行する。
-/
theorem precedesIn_flatMap_of_split {f : NodeId → List NodeId}
    {u v : List NodeId} {cx cy x y : NodeId}
    (hcy : cy ∈ v) (hx : x ∈ f cx) (hy : y ∈ f cy)
    (hxu : ∀ c ∈ u, x ∉ f c) (hyu : ∀ c ∈ u, y ∉ f c) (hycx : y ∉ f cx) :
    precedesIn ((u ++ cx :: v).flatMap f) x y = true := by
  rw [List.flatMap_append, List.flatMap_cons]
  rw [precedesIn_append_of_not_mem _ _
    (fun h => by obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp h; exact hxu c hc hxc)
    (fun h => by obtain ⟨c, hc, hyc⟩ := List.mem_flatMap.mp h; exact hyu c hc hyc)]
  exact precedesIn_append_of_mem_left _ _ hx hycx (List.mem_flatMap.mpr ⟨cy, hcy, hy⟩)

/-! ## index と children の分割 -/

theorem index_eq_some_iff_split {t : Tree} {c p : NodeId} {i : Nat}
    (hp : parentOf t c = some p) :
    index t c = some i ↔
      ∃ u v, childrenOf t p = u ++ c :: v ∧ u.length = i ∧ c ∉ u := by
  unfold index
  rw [hp]
  simp only [Option.bind_some]
  exact Dom.ListUtil.findIdx?_eq_some_iff_split

/-- well-formed な木では、parent を持つ node の index は必ず存在する。 -/
theorem index_isSome (hwf : WellFormed t) {c p : NodeId} (hp : parentOf t c = some p) :
    ∃ i, index t c = some i := by
  have hmem : c ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hp
  unfold index
  rw [hp]
  simp only [Option.bind_some]
  cases hf : (childrenOf t p).findIdx? (fun x => decide (x = c)) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    exfalso
    rw [List.findIdx?_eq_none_iff] at hf
    have hn := hf c hmem
    simp at hn

/-- index が小さいほうの子で分割すると、index が大きいほうは後ろ側に入る。 -/
theorem index_split_lt (hwf : WellFormed t) {p cx cy : NodeId} {i j : Nat}
    (hcx : parentOf t cx = some p) (hcy : parentOf t cy = some p)
    (hi : index t cx = some i) (hj : index t cy = some j) (hij : i < j) :
    ∃ u v, childrenOf t p = u ++ cx :: v ∧ cy ∈ v := by
  obtain ⟨u, v, hsplit, hlen, hnot⟩ := (index_eq_some_iff_split hcx).mp hi
  refine ⟨u, v, hsplit, ?_⟩
  have hnd : (childrenOf t p).Nodup := by
    obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hcx
    rw [childrenOf_eq hpd]
    exact hwf.children_nodup p pd hpd
  have hmem : cy ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hcy
  rw [hsplit] at hmem hnd
  have hund : u.Nodup := (List.nodup_append.mp hnd).1
  rcases List.mem_append.mp hmem with hu | hv
  · exfalso
    obtain ⟨u₁, u₂, hu₁⟩ := Dom.ListUtil.mem_split hu
    have hsplit₂ : childrenOf t p = u₁ ++ cy :: (u₂ ++ cx :: v) := by
      rw [hsplit, hu₁]; simp
    have hnot₁ : cy ∉ u₁ := by
      rw [hu₁] at hund
      intro hm
      exact (List.nodup_append.mp hund).2.2 cy hm cy (List.mem_cons_self ..) rfl
    have heq : index t cy = some u₁.length :=
      (index_eq_some_iff_split hcy).mpr ⟨u₁, u₂ ++ cx :: v, hsplit₂, rfl, hnot₁⟩
    rw [hj] at heq
    have hju : j = u₁.length := Option.some.inj heq
    have hlt : u₁.length < u.length := by rw [hu₁]; simp
    omega
  · rcases List.mem_cons.mp hv with he | he
    · exfalso
      rw [he, hi] at hj
      have : i = j := Option.some.inj hj
      omega
    · exact he

theorem inclusiveAncestor_of_ancestor_parent {t : Tree} {r n p : NodeId}
    (h : Ancestor t r n) (hp : parentOf t n = some p) : InclusiveAncestor t r p := by
  obtain ⟨q, hq, hcase⟩ := h.cases_parent
  rw [hp] at hq
  cases hq
  rcases hcase with rfl | ha
  · exact Or.inl rfl
  · exact Or.inr ha

/-- 前の兄弟の部分木は、後の兄弟の部分木より tree order で先行する。 -/
theorem precedesIn_preorderFuel_of_sibling (hwf : WellFormed t) {k : Nat} {p cx cy x y : NodeId}
    {pd : NodeData} (hp : t.get? p = some pd) (hk : t.size - depth t p ≤ k)
    (hcx : parentOf t cx = some p) (hcy : parentOf t cy = some p)
    {i j : Nat} (hi : index t cx = some i) (hj : index t cy = some j) (hij : i < j)
    (hx : InclusiveDescendant t x cx) (hy : InclusiveDescendant t y cy) :
    precedesIn (preorderFuel t k p) x y = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    have := depth_lt_size hwf hp
    exact ⟨k - 1, by omega⟩
  -- children を cx の位置で分割する
  obtain ⟨u, v, hsplit, hcyv⟩ := index_split_lt hwf hcx hcy hi hj hij
  have hnd : (childrenOf t p).Nodup := by
    rw [childrenOf_eq hp]; exact hwf.children_nodup p pd hp
  rw [hsplit] at hnd
  have hcxu : cx ∉ u := fun hm =>
    (List.nodup_append.mp hnd).2.2 cx hm cx (List.mem_cons_self ..) rfl
  have hune : ∀ c ∈ u, c ≠ cx ∧ c ≠ cy := by
    intro c hc
    exact ⟨(List.nodup_append.mp hnd).2.2 c hc cx (List.mem_cons_self ..),
      (List.nodup_append.mp hnd).2.2 c hc cy (List.mem_cons_of_mem _ hcyv)⟩
  have hxycx : cx ≠ cy := fun he =>
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (he ▸ hcyv)
  -- 子の部分木は fuel k' で列挙できる
  obtain ⟨cxd, hcxd, _⟩ := parentOf_eq_some hcx
  obtain ⟨cyd, hcyd, _⟩ := parentOf_eq_some hcy
  have hdx : depth t cx = depth t p + 1 := depth_parent hwf hcx
  have hdy : depth t cy = depth t p + 1 := depth_parent hwf hcy
  have hmemx : x ∈ preorderFuel t k' cx :=
    mem_preorderFuel_of_inclusive_descendant hwf k' cx cxd hcxd (by omega) x hx
  have hmemy : y ∈ preorderFuel t k' cy :=
    mem_preorderFuel_of_inclusive_descendant hwf k' cy cyd hcyd (by omega) y hy
  -- 部分木は互いに素
  have hdisj : ∀ c ∈ childrenOf t p, ∀ c' ∈ childrenOf t p, c ≠ c' →
      ∀ z, z ∈ preorderFuel t k' c → z ∉ preorderFuel t k' c' := by
    intro c hc c' hc' hne z hz hz'
    exact sibling_subtrees_disjoint hwf (parentOf_of_mem_childrenOf hwf hc)
      (parentOf_of_mem_childrenOf hwf hc') hne
      (inclusive_descendant_of_mem_preorderFuel hwf k' c z hz)
      (inclusive_descendant_of_mem_preorderFuel hwf k' c' z hz')
  have hmemu : ∀ c ∈ u, c ∈ childrenOf t p := by
    intro c hc; rw [hsplit]; exact List.mem_append_left _ hc
  have hmemcx : cx ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hcx
  have hmemcy : cy ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hcy
  -- x も y も p 自身ではない
  have hxp : x ≠ p := by
    intro he
    subst he
    rcases hx with hcxx | hanc
    · exact hwf.acyclic x (Ancestor.step (hcxx ▸ hcx))
    · exact hwf.acyclic x ((Ancestor.step hcx).trans_ancestor hanc)
  have hyp : y ≠ p := by
    intro he
    subst he
    rcases hy with hcyy | hanc
    · exact hwf.acyclic y (Ancestor.step (hcyy ▸ hcy))
    · exact hwf.acyclic y ((Ancestor.step hcy).trans_ancestor hanc)
  rw [preorderFuel_succ_pos hp, precedesIn_cons_ne (fun he => hxp he.symm)
    (fun he => hyp he.symm), hsplit]
  exact precedesIn_flatMap_of_split hcyv hmemx hmemy
    (fun c hc hz => hdisj cx hmemcx c (hmemu c hc) (fun he => (hune c hc).1 he.symm) x hmemx hz)
    (fun c hc hz => hdisj cy hmemcy c (hmemu c hc) (fun he => (hune c hc).2 he.symm) y hmemy hz)
    (fun hz => hdisj cy hmemcy cx hmemcx (fun he => hxycx he.symm) y hmemy hz)

/-- 両方が前半にあるなら、連結しても判定は変わらない。 -/
theorem precedesIn_append_of_mem_both {x y : NodeId} (hxy : x ≠ y) :
    ∀ (l₁ l₂ : List NodeId), x ∈ l₁ → y ∈ l₁ →
      precedesIn (l₁ ++ l₂) x y = precedesIn l₁ x y := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ hx; simp at hx
  | cons z rest ih =>
    intro l₂ hx hy
    by_cases hzx : z = x
    · subst hzx
      have hy' : y ∈ rest := by
        rcases List.mem_cons.mp hy with he | he
        · exact absurd he.symm hxy
        · exact he
      rw [List.cons_append, precedesIn_cons_self, precedesIn_cons_self]
      simp [hy', List.mem_append_left _ hy']
    · by_cases hzy : z = y
      · rw [List.cons_append, precedesIn_cons_target hzx hzy,
          precedesIn_cons_target hzx hzy]
      · have hx' : x ∈ rest := by
          rcases List.mem_cons.mp hx with he | he
          · exact absurd he.symm hzx
          · exact he
        have hy' : y ∈ rest := by
          rcases List.mem_cons.mp hy with he | he
          · exact absurd he.symm hzy
          · exact he
        rw [List.cons_append, precedesIn_cons_ne hzx hzy, precedesIn_cons_ne hzx hzy]
        exact ih l₂ hx' hy'

/-- 同じ segment に入っている二つの要素の判定は、その segment だけで決まる。 -/
theorem precedesIn_flatMap_same {f : NodeId → List NodeId} {cs : List NodeId}
    {c x y : NodeId} (hxy : x ≠ y) (hnd : cs.Nodup) (hc : c ∈ cs)
    (hx : x ∈ f c) (hy : y ∈ f c)
    (hdisj : ∀ c' ∈ cs, c' ≠ c → x ∉ f c' ∧ y ∉ f c') :
    precedesIn (cs.flatMap f) x y = precedesIn (f c) x y := by
  obtain ⟨u, v, hu⟩ := Dom.ListUtil.mem_split hc
  subst hu
  have hcu : c ∉ u := fun hm =>
    (List.nodup_append.mp hnd).2.2 c hm c (List.mem_cons_self ..) rfl
  have hne : ∀ c' ∈ u, c' ≠ c := fun c' hc' he => hcu (he ▸ hc')
  rw [List.flatMap_append, List.flatMap_cons]
  have hxu : x ∉ u.flatMap f := by
    intro hm
    obtain ⟨c', hc', hxc'⟩ := List.mem_flatMap.mp hm
    exact (hdisj c' (List.mem_append_left _ hc') (hne c' hc')).1 hxc'
  have hyu : y ∉ u.flatMap f := by
    intro hm
    obtain ⟨c', hc', hyc'⟩ := List.mem_flatMap.mp hm
    exact (hdisj c' (List.mem_append_left _ hc') (hne c' hc')).2 hyc'
  rw [precedesIn_append_of_not_mem _ _ hxu hyu]
  exact precedesIn_append_of_mem_both hxy _ _ hx hy

/--
より深い位置の兄弟についても、前の兄弟の部分木は後の兄弟の部分木より先行する。

`r` から `p` へ降りていく帰納法で示す。
-/
theorem precedesIn_preorderFuel_of_sibling_deep (hwf : WellFormed t) :
    ∀ (k : Nat) (r x y : NodeId) (rd : NodeData), t.get? r = some rd →
      t.size - depth t r ≤ k →
      InclusiveDescendant t x r → InclusiveDescendant t y r →
      ∀ (p cx cy : NodeId) (i j : Nat), parentOf t cx = some p → parentOf t cy = some p →
        index t cx = some i → index t cy = some j → i < j →
        InclusiveAncestor t cx x → InclusiveAncestor t cy y →
      precedesIn (preorderFuel t k r) x y = true := by
  intro k
  induction k with
  | zero =>
    intro r x y rd hr hk
    exfalso
    have := depth_lt_size hwf hr
    omega
  | succ k ih =>
    intro r x y rd hr hk hxr hyr p cx cy i j hcx hcy hi hj hij hxcx hycy
    have hcxy : cx ≠ cy := by
      intro he
      rw [he, hj] at hi
      have : j = i := Option.some.inj hi
      omega
    have hxy : x ≠ y := by
      intro he
      exact sibling_subtrees_disjoint hwf hcx hcy hcxy hxcx (he ▸ hycy)
    by_cases hpr : p = r
    · subst hpr
      exact precedesIn_preorderFuel_of_sibling hwf hr hk hcx hcy hi hj hij hxcx hycy
    · -- r は p の真の ancestor
      have hrp : Ancestor t r p := by
        rcases inclusive_ancestor_linear hxr hxcx with hrc | hcr
        · rcases hrc with he | hanc
          · exfalso
            exact sibling_subtrees_disjoint hwf hcx hcy hcxy (by rw [← he]; exact hyr) hycy
          · rcases inclusiveAncestor_of_ancestor_parent hanc hcx with he | hanc'
            · exact absurd he.symm hpr
            · exact hanc'
        · exfalso
          exact sibling_subtrees_disjoint hwf hcx hcy hcxy
            (hcr.trans_inclusive hyr) hycy
      obtain ⟨c, hc, hcp⟩ := hrp.exists_child
      obtain ⟨cd, hcd, _⟩ := parentOf_eq_some hc
      have hccx : InclusiveAncestor t c cx := hcp.trans_inclusive (Or.inr (Ancestor.step hcx))
      have hccy : InclusiveAncestor t c cy := hcp.trans_inclusive (Or.inr (Ancestor.step hcy))
      have hcxx : InclusiveAncestor t c x := hccx.trans_inclusive hxcx
      have hcyy : InclusiveAncestor t c y := hccy.trans_inclusive hycy
      have hrx : Ancestor t r x := by
        rcases hcxx with he | hanc
        · rw [← he]; exact Ancestor.step hc
        · exact (Ancestor.step hc).trans_ancestor hanc
      have hry : Ancestor t r y := by
        rcases hcyy with he | hanc
        · rw [← he]; exact Ancestor.step hc
        · exact (Ancestor.step hc).trans_ancestor hanc
      have hxr' : x ≠ r := fun he => hwf.acyclic r (he ▸ hrx)
      have hyr' : y ≠ r := fun he => hwf.acyclic r (he ▸ hry)
      have hdepth : depth t c = depth t r + 1 := depth_parent hwf hc
      have hmemx : x ∈ preorderFuel t k c :=
        mem_preorderFuel_of_inclusive_descendant hwf k c cd hcd (by omega) x hcxx
      have hmemy : y ∈ preorderFuel t k c :=
        mem_preorderFuel_of_inclusive_descendant hwf k c cd hcd (by omega) y hcyy
      have hnd : (childrenOf t r).Nodup := by
        rw [childrenOf_eq hr]; exact hwf.children_nodup r rd hr
      have hmemc : c ∈ childrenOf t r := mem_childrenOf_of_parentOf hwf hc
      have hsame : precedesIn ((childrenOf t r).flatMap (preorderFuel t k)) x y
          = precedesIn (preorderFuel t k c) x y := by
        refine precedesIn_flatMap_same hxy hnd hmemc hmemx hmemy ?_
        intro c' hc' hne
        refine ⟨fun hz => ?_, fun hz => ?_⟩
        · exact sibling_subtrees_disjoint hwf (parentOf_of_mem_childrenOf hwf hc') hc hne
            (inclusive_descendant_of_mem_preorderFuel hwf k c' x hz) hcxx
        · exact sibling_subtrees_disjoint hwf (parentOf_of_mem_childrenOf hwf hc') hc hne
            (inclusive_descendant_of_mem_preorderFuel hwf k c' y hz) hcyy
      rw [preorderFuel_succ_pos hr, precedesIn_cons_ne (fun he => hxr' he.symm)
        (fun he => hyr' he.symm), hsame]
      exact ih c x y cd hcd (by omega) hcxx hcyy p cx cy i j hcx hcy hi hj hij hxcx hycy

/-! ## tree order の構造的な特徴づけ -/

/--
構造で定めた tree order の先行関係。

`x` が `y` の ancestor であるか、あるいは共通の parent を持つ二つの子 `cx`, `cy` が
あって `cx` のほうが index が小さく、`x` が `cx` の、`y` が `cy` の
inclusive descendant であるか、のいずれか。
-/
def PrecedesStruct (t : Tree) (x y : NodeId) : Prop :=
  Ancestor t x y ∨
    ∃ p cx cy i j, parentOf t cx = some p ∧ parentOf t cy = some p ∧
      index t cx = some i ∧ index t cy = some j ∧ i < j ∧
      InclusiveAncestor t cx x ∧ InclusiveAncestor t cy y

theorem precedesIn_preorder_of_struct (hwf : WellFormed t) {r x y : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) (hx : InclusiveDescendant t x r)
    (hy : InclusiveDescendant t y r) (h : PrecedesStruct t x y) :
    precedesIn (preorder t r) x y = true := by
  rcases h with hanc | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxcx, hycy⟩
  · exact precedesIn_preorderFuel_of_ancestor hwf t.size r rd hr (Nat.sub_le _ _) x y hanc hx
  · exact precedesIn_preorderFuel_of_sibling_deep hwf t.size r x y rd hr (Nat.sub_le _ _)
      hx hy p cx cy i j hcx hcy hi hj hij hxcx hycy

/-- 同じ parent の相異なる子は index も異なる。 -/
theorem index_ne_of_ne {t : Tree} {p cx cy : NodeId} {i j : Nat}
    (hcx : parentOf t cx = some p) (hcy : parentOf t cy = some p)
    (hi : index t cx = some i) (hj : index t cy = some j) (hne : cx ≠ cy) : i ≠ j := by
  intro he
  subst he
  obtain ⟨u, v, hsplit, hlen, _⟩ := (index_eq_some_iff_split hcx).mp hi
  obtain ⟨u', v', hsplit', hlen', _⟩ := (index_eq_some_iff_split hcy).mp hj
  exact hne (Dom.ListUtil.append_cons_inj (by rw [← hsplit, hsplit']) (by omega))

/-- 同じ木にある相異なる二つの node は、必ずどちらかが先行する。 -/
theorem precedesStruct_total (hwf : WellFormed t) :
    ∀ (k : Nat) (r x y : NodeId) (rd : NodeData), t.get? r = some rd →
      t.size - depth t r ≤ k → InclusiveDescendant t x r → InclusiveDescendant t y r →
      x ≠ y → PrecedesStruct t x y ∨ PrecedesStruct t y x := by
  intro k
  induction k with
  | zero =>
    intro r x y rd hr hk
    exfalso
    have := depth_lt_size hwf hr
    omega
  | succ k ih =>
    intro r x y rd hr hk hx hy hxy
    by_cases hxr : x = r
    · subst hxr
      rcases hy with he | hanc
      · exact absurd he hxy
      · exact Or.inl (Or.inl hanc)
    · by_cases hyr : y = r
      · subst hyr
        rcases hx with he | hanc
        · exact absurd he.symm hxy
        · exact Or.inr (Or.inl hanc)
      · -- どちらも r の真の descendant
        have hrx : Ancestor t r x := by
          rcases hx with he | hanc
          · exact absurd he.symm hxr
          · exact hanc
        have hry : Ancestor t r y := by
          rcases hy with he | hanc
          · exact absurd he.symm hyr
          · exact hanc
        obtain ⟨cx, hcx, hcxx⟩ := hrx.exists_child
        obtain ⟨cy, hcy, hcyy⟩ := hry.exists_child
        by_cases hcc : cx = cy
        · subst hcc
          obtain ⟨cd, hcd, _⟩ := parentOf_eq_some hcx
          have hdepth : depth t cx = depth t r + 1 := depth_parent hwf hcx
          exact ih cx x y cd hcd (by omega) hcxx hcyy hxy
        · obtain ⟨i, hi⟩ := index_isSome hwf hcx
          obtain ⟨j, hj⟩ := index_isSome hwf hcy
          rcases Nat.lt_or_ge i j with hlt | hge
          · exact Or.inl (Or.inr ⟨r, cx, cy, i, j, hcx, hcy, hi, hj, hlt, hcxx, hcyy⟩)
          · have hne := index_ne_of_ne hcx hcy hi hj hcc
            exact Or.inr (Or.inr ⟨r, cy, cx, j, i, hcy, hcx, hj, hi, by omega, hcyy, hcxx⟩)

/-- 列の中で両方が先行しあうことはない。 -/
theorem precedesIn_asymm {l : List NodeId} {x y : NodeId} (hxy : x ≠ y)
    (hx : x ∈ l) (hy : y ∈ l) (h : precedesIn l x y = true) : precedesIn l y x = false := by
  cases hb : precedesIn l y x with
  | false => rfl
  | true =>
    exfalso
    have h1 := (precedesIn_iff_idx hxy l hx hy).mp h
    have h2 := (precedesIn_iff_idx (fun he => hxy he.symm) l hy hx).mp hb
    omega

/-- PLAN §4.2 の拡張。`precedes` は構造的な条件と一致する。 -/
theorem precedesIn_preorder_iff_struct (hwf : WellFormed t) {r x y : NodeId} {rd : NodeData}
    (hr : t.get? r = some rd) (hx : InclusiveDescendant t x r)
    (hy : InclusiveDescendant t y r) (hxy : x ≠ y) :
    precedesIn (preorder t r) x y = true ↔ PrecedesStruct t x y := by
  constructor
  · intro h
    rcases precedesStruct_total hwf t.size r x y rd hr (Nat.sub_le _ _) hx hy hxy with hs | hs
    · exact hs
    · exfalso
      have hyx := precedesIn_preorder_of_struct hwf hr hy hx hs
      rw [precedesIn_asymm hxy ((mem_preorder_iff hwf hr x).mpr hx)
        ((mem_preorder_iff hwf hr y).mpr hy) h] at hyx
      simp at hyx
  · exact precedesIn_preorder_of_struct hwf hr hx hy

/-- `precedes` の構造的な特徴づけ。同じ root にある相異なる二つの node について。 -/
theorem precedes_iff_struct (hwf : WellFormed t) {a b : NodeId} {ad : NodeData}
    (ha : t.get? a = some ad) (hroot : root t a = root t b) (hab : a ≠ b) :
    precedes t a b = true ↔ PrecedesStruct t a b := by
  obtain ⟨rd, hrd⟩ := exists_data_root hwf ha
  have hxa : InclusiveDescendant t a (root t a) := root_inclusive_ancestor t a
  have hxb : InclusiveDescendant t b (root t a) := by
    rw [hroot]; exact root_inclusive_ancestor t b
  unfold precedes treeOrder
  exact precedesIn_preorder_iff_struct hwf hrd hxa hxb hab

/-- 同じ root にある相異なる二つの node は、どちらか一方だけが先行する。 -/
theorem precedes_eq_false_iff (hwf : WellFormed t) {a b : NodeId} {ad : NodeData}
    (ha : t.get? a = some ad) (hroot : root t a = root t b) (hab : a ≠ b) :
    precedes t b a = false ↔ PrecedesStruct t a b := by
  obtain ⟨rd, hrd⟩ := exists_data_root hwf ha
  have hxa : InclusiveDescendant t a (root t a) := root_inclusive_ancestor t a
  have hxb : InclusiveDescendant t b (root t a) := by
    rw [hroot]; exact root_inclusive_ancestor t b
  have hba : precedes t b a = true ↔ PrecedesStruct t b a := by
    obtain ⟨bd, hbd⟩ : ∃ bd, t.get? b = some bd :=
      exists_data_of_mem_preorderFuel t.size (root t a) b ((mem_preorder_iff hwf hrd b).mpr hxb)
    exact precedes_iff_struct hwf hbd hroot.symm (fun h => hab h.symm)
  constructor
  · intro h
    rcases precedesStruct_total hwf t.size (root t a) a b rd hrd (Nat.sub_le _ _)
      hxa hxb hab with hs | hs
    · exact hs
    · exact absurd (hba.mpr hs) (by rw [h]; simp)
  · intro hs
    cases hb : precedes t b a with
    | false => rfl
    | true =>
      exfalso
      have hs' := hba.mp hb
      have h1 := precedesIn_preorder_of_struct hwf hrd hxa hxb hs
      have h2 := precedesIn_preorder_of_struct hwf hrd hxb hxa hs'
      rw [precedesIn_asymm hab ((mem_preorder_iff hwf hrd a).mpr hxa)
        ((mem_preorder_iff hwf hrd b).mpr hxb) h1] at h2
      simp at h2

end Dom
