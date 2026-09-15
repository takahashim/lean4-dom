import Dom.Mutation.Clone
import Dom.Properties.Create

/-!
# clone した subtree の性質

roadmap §8.4 が求める二つを示す。

* **identity は違う。** copy は原本と別の `NodeId` を持つ（`cloneNode_ne`）。
* **観測できる形は同じ。** copy の subtree は原本の subtree と、kind・data・
  attribute・名前・children の並びまで一致する（`CloneOf`）。

この二つを分けて書けること自体が、node を id で表した model の効き目である。
実装では「同じ object か」と「同じ内容か」が同じ `==` の裏に隠れやすい。
-/

namespace Dom

/-! ## clone が状態にする変更 -/

/-- 木しか変えていないこと。 -/
def TreeOnly (s s' : DOMState) : Prop := s.withTree s'.tree = s'

theorem TreeOnly.refl (s : DOMState) : TreeOnly s s := rfl

theorem TreeOnly.trans {s s' s'' : DOMState} (h₁ : TreeOnly s s') (h₂ : TreeOnly s' s'') :
    TreeOnly s s'' := by
  calc s.withTree s''.tree = (s.withTree s'.tree).withTree s''.tree := rfl
    _ = s'.withTree s''.tree := by rw [h₁]
    _ = s'' := h₂

/-- 木にある id はどれも `next` より小さい。clone が取る id の新しさはこれで言う。 -/
def IdsBelow (t : Tree) (next : Nat) : Prop := ∀ m md, t.get? m = some md → m.id < next

theorem idsBelow_freshId (t : Tree) : IdsBelow t (freshId t).id := by
  intro m md hm
  have := id_le_maxId hm
  simp only [freshId]
  omega

/-! ## 「copy である」関係 -/

/--
`CloneOf t n c`：`t` の中で `c` を根とする subtree が `n` を根とする subtree の copy である。

見るのは仕様の "clone a single node" が写す部分、すなわち parent・children・
node document を除いた node data（`NodeData.shape`）と data、そして
children の並びである。`NodeId` そのものは見ない。だから `CloneOf t n n` も成り立つ。
identity が違うことは別に述べる。
-/
inductive CloneOf (t : Tree) : NodeId → NodeId → Prop where
  | mk {n c : NodeId} {d cd : NodeData} :
      t.get? n = some d → t.get? c = some cd →
      cd.shape = d.shape → cd.data = d.data →
      cd.children.length = d.children.length →
      (∀ (i : Nat) (a b : NodeId), d.children[i]? = some a → cd.children[i]? = some b →
        CloneOf t a b) →
      CloneOf t n c

/-- 列ごとの `CloneOf`。同じ長さで、同じ位置どうしが copy である。 -/
def CloneListOf (t : Tree) (l k : List NodeId) : Prop :=
  k.length = l.length ∧
    ∀ (i : Nat) (a b : NodeId), l[i]? = some a → k[i]? = some b → CloneOf t a b

theorem CloneListOf.nil (t : Tree) : CloneListOf t [] [] :=
  ⟨rfl, by intro i a b h; simp at h⟩

theorem CloneListOf.cons {t : Tree} {a b : NodeId} {l k : List NodeId}
    (h : CloneOf t a b) (hl : CloneListOf t l k) : CloneListOf t (a :: l) (b :: k) := by
  refine ⟨by simp [hl.1], ?_⟩
  intro i x y hx hy
  cases i with
  | zero => simp at hx hy; rw [← hx, ← hy]; exact h
  | succ j => simp at hx hy; exact hl.2 j x y hx hy

/-- 木に node を足しても、既にある copy 関係は壊れない。 -/
theorem CloneOf.mono {t t' : Tree} (hk : ∀ m md, t.get? m = some md → t'.get? m = some md)
    {n c : NodeId} (h : CloneOf t n c) : CloneOf t' n c := by
  induction h with
  | mk hd hcd hsh hdata hlen _ ih =>
    exact .mk (hk _ _ hd) (hk _ _ hcd) hsh hdata hlen ih

theorem CloneListOf.mono {t t' : Tree}
    (hk : ∀ m md, t.get? m = some md → t'.get? m = some md) {l k : List NodeId}
    (h : CloneListOf t l k) : CloneListOf t' l k :=
  ⟨h.1, fun i a b ha hb => (h.2 i a b ha hb).mono hk⟩


/-! ## `cloneMany` が満たすこと -/

/--
`cloneMany` の結果が満たすこと。

`newIds` と `kidsFresh` は「取った id が新しい」ことを述べる。この二つが無いと、
入れ子の呼び出しが外側の copy の id を踏まないことが言えない。
-/
structure CloneManySpec (s : DOMState) (next : Nat) (l kids : List NodeId)
    (next' : Nat) (s' : DOMState) : Prop where
  /-- 木しか変えない。 -/
  treeOnly : TreeOnly s s'
  /-- counter は戻らない。 -/
  nextLe : next ≤ next'
  /-- 使った id はすべて counter より小さい。 -/
  idsBelow : IdsBelow s'.tree next'
  /-- もとからあった node は、そのまま残る。 -/
  keep : ∀ m md, s.tree.get? m = some md → s'.tree.get? m = some md
  /-- 増えた node の id は counter 以上である。 -/
  newIds : ∀ m md, s'.tree.get? m = some md → s.tree.get? m = some md ∨ next ≤ m.id
  /-- 返した copy の id も counter 以上である。 -/
  kidsFresh : ∀ c ∈ kids, next ≤ c.id
  /-- 返した列は、渡された列の copy である。 -/
  clones : CloneListOf s'.tree l kids

theorem CloneManySpec.nil (s : DOMState) (next : Nat) (hb : IdsBelow s.tree next) :
    CloneManySpec s next [] [] next s where
  treeOnly := TreeOnly.refl s
  nextLe := Nat.le_refl _
  idsBelow := hb
  keep := fun _ _ h => h
  newIds := fun _ _ h => Or.inl h
  kidsFresh := by intro c hc; simp at hc
  clones := CloneListOf.nil _

/--
`cloneMany` の一段。children の clone と兄弟の clone が仕様を満たすなら、
その二つを copy 一つで繋いだものも満たす。

`s₃` と `cd` を等式で受け取るのは、`cloneMany` の定義に現れる項を
そのまま書かずに済ませるためである。
-/
theorem cloneManySpec_cons {s s₂ s₃ s₄ : DOMState} {next next₁ next₂ : Nat}
    {n : NodeId} {rest kids₀ siblings : List NodeId} {d cd : NodeData}
    (hb : IdsBelow s.tree next) (hd : s.tree.get? n = some d)
    (hshape : cd.shape = d.shape) (hdata : cd.data = d.data) (hkids : cd.children = kids₀)
    (hs₃ : s₃ = s₂.withTree (s₂.tree.insertNode ⟨next⟩ cd))
    (h₁ : CloneManySpec s (next + 1) d.children kids₀ next₁ s₂)
    (h₂ : CloneManySpec s₃ next₁ rest siblings next₂ s₄) :
    CloneManySpec s next (n :: rest) (⟨next⟩ :: siblings) next₂ s₄ := by
  have hs₃tree : s₃.tree = s₂.tree.insertNode ⟨next⟩ cd := by simp [hs₃]
  -- copy の id はまだ誰も使っていない。
  have hcs : s.tree.get? ⟨next⟩ = none := by
    cases hc : s.tree.get? (⟨next⟩ : NodeId) with
    | none => rfl
    | some x => exact absurd (hb ⟨next⟩ x hc) (Nat.lt_irrefl next)
  have hcs2 : s₂.tree.get? ⟨next⟩ = none := by
    cases hc : s₂.tree.get? (⟨next⟩ : NodeId) with
    | none => rfl
    | some x =>
      rcases h₁.newIds ⟨next⟩ x hc with hx | hx
      · rw [hcs] at hx; simp at hx
      · exact absurd hx (Nat.not_succ_le_self next)
  have hkeep23 : ∀ m md, s₂.tree.get? m = some md → s₃.tree.get? m = some md := by
    intro m md hm
    have hne : m ≠ ⟨next⟩ := by intro he; rw [he, hcs2] at hm; simp at hm
    rw [hs₃tree, get?_insertNode_ne _ hne]
    exact hm
  have hkeep : ∀ m md, s.tree.get? m = some md → s₄.tree.get? m = some md :=
    fun m md hm => h₂.keep m md (hkeep23 m md (h₁.keep m md hm))
  have hcopy3 : s₃.tree.get? ⟨next⟩ = some cd := by
    rw [hs₃tree]; exact get?_insertNode_self _ _ _
  refine ⟨?_, ?_, h₂.idsBelow, hkeep, ?_, ?_, ?_⟩
  · -- treeOnly
    refine (h₁.treeOnly.trans ?_).trans h₂.treeOnly
    show s₂.withTree s₃.tree = s₃
    simp [hs₃]
  · -- nextLe
    have := h₁.nextLe; have := h₂.nextLe; omega
  · -- newIds
    intro m md hm
    rcases h₂.newIds m md hm with hx | hx
    · by_cases hmn : m = ⟨next⟩
      · subst hmn; exact Or.inr (Nat.le_refl _)
      · rw [hs₃tree, get?_insertNode_ne _ hmn] at hx
        rcases h₁.newIds m md hx with hy | hy
        · exact Or.inl hy
        · exact Or.inr (by omega)
    · have := h₁.nextLe
      exact Or.inr (by omega)
  · -- kidsFresh
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Nat.le_refl _
    · have := h₁.nextLe
      have := h₂.kidsFresh c hc'
      omega
  · -- clones
    refine CloneListOf.cons ?_ h₂.clones
    refine CloneOf.mk (hkeep n d hd) (h₂.keep _ _ hcopy3) hshape hdata ?_ ?_
    · rw [hkids]; exact h₁.clones.1
    · intro i a b ha hbb
      rw [hkids] at hbb
      exact (h₁.clones.2 i a b ha hbb).mono
        (fun m md hm => h₂.keep m md (hkeep23 m md hm))

/-- **`cloneMany` の仕様。** -/
theorem cloneMany_spec (fuel : Nat) : ∀ (s : DOMState) (next : Nat) (l : List NodeId)
    (doc : NodeId) (parent : Option NodeId) (kids : List NodeId) (next' : Nat) (s' : DOMState),
    IdsBelow s.tree next → cloneMany fuel s next l doc parent = some (kids, next', s') →
    CloneManySpec s next l kids next' s' := by
  induction fuel with
  | zero =>
    intro s next l doc parent kids next' s' hb h
    cases l with
    | nil =>
      simp only [cloneMany, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact CloneManySpec.nil s next hb
    | cons n rest => simp [cloneMany] at h
  | succ fuel ih =>
    intro s next l doc parent kids next' s' hb h
    cases l with
    | nil =>
      simp only [cloneMany, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact CloneManySpec.nil s next hb
    | cons n rest =>
      simp only [cloneMany] at h
      split at h
      · simp at h
      · next d hd =>
        split at h
        · simp at h
        · next kids₀ next₁ s₂ hr =>
          split at h
          · simp at h
          · next siblings next₂ s₄ hr₂ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hb1 : IdsBelow s.tree (next + 1) := fun m md hm => by
              have := hb m md hm; omega
            have h₁ := ih s (next + 1) d.children (cloneDocumentOf d doc ⟨next⟩) (some ⟨next⟩)
              kids₀ next₁ s₂ hb1 hr
            have hb3 : IdsBelow (s₂.withTree (s₂.tree.insertNode ⟨next⟩
                (cloneData d (cloneDocumentOf d doc ⟨next⟩) parent kids₀))).tree next₁ := by
              intro m md hm
              simp only [DOMState.withTree_tree] at hm
              by_cases hmn : m = ⟨next⟩
              · subst hmn
                have := h₁.nextLe
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self next) this
              · rw [get?_insertNode_ne _ hmn] at hm
                exact h₁.idsBelow m md hm
            exact cloneManySpec_cons (kids₀ := kids₀)
              (cd := cloneData d (cloneDocumentOf d doc ⟨next⟩) parent kids₀) hb hd rfl rfl rfl rfl
              h₁ (ih _ next₁ rest doc parent siblings next₂ s₄ hb3 hr₂)


/-! ## `cloneNode` -/

/-- **deep clone がすること。** -/
theorem cloneNode_deep_spec {s s' : DOMState} {n c : NodeId}
    (h : cloneNode s n true = .ok (c, s')) :
    ∃ d, s.tree.get? n = some d ∧ TreeOnly s s' ∧
      (∀ m md, s.tree.get? m = some md → s'.tree.get? m = some md) ∧
      s.tree.get? c = none ∧ CloneOf s'.tree n c := by
  simp only [cloneNode] at h
  split at h
  · simp at h
  · next d hd =>
    rw [if_pos True.intro] at h
    split at h
    · next c₀ kids next₀ s₀ hcm =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hsp := cloneMany_spec (s.tree.size + 1) s (freshId s.tree).id [n] d.ownerDocument none
        (c₀ :: kids) next₀ s₀ (idsBelow_freshId s.tree) hcm
      refine ⟨d, hd, hsp.treeOnly, hsp.keep, ?_, ?_⟩
      · cases hc : s.tree.get? c₀ with
        | none => rfl
        | some x =>
          exact absurd (idsBelow_freshId s.tree c₀ x hc)
            (Nat.not_lt.mpr (hsp.kidsFresh c₀ (List.mem_cons_self ..)))
      · exact hsp.clones.2 0 n c₀ (by simp) (by simp)
    · simp at h


/--
**shallow clone がすること。** §4.4 "clone a single node" そのものである。
children を持たない detach された copy が一つ増える。
-/
theorem cloneNode_shallow_spec {s s' : DOMState} {n c : NodeId}
    (h : cloneNode s n false = .ok (c, s')) :
    ∃ d cd, s.tree.get? n = some d ∧ cd.shape = d.shape ∧ cd.data = d.data ∧
      cd.children = [] ∧ cd.parent = none ∧ AddsNode s.tree s'.tree c cd ∧ TreeOnly s s' := by
  simp only [cloneNode] at h
  split at h
  · simp at h
  · next d hd =>
    rw [if_neg (by simp : ¬(false = true))] at h
    have he := Except.ok.inj h
    have hc : (cloneSingle s d d.ownerDocument none).1 = c := congrArg Prod.fst he
    have hs : (cloneSingle s d d.ownerDocument none).2 = s' := congrArg Prod.snd he
    refine ⟨d, cloneData d (cloneDocumentOf d d.ownerDocument (freshId s.tree)) none [],
      hd, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rw [← hc, ← hs]
      exact withFresh_addsNode s _
    · rw [← hs]; rfl

/-- **clone の id は木にまだ無い。** -/
theorem cloneNode_fresh {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (h : cloneNode s n deep = .ok (c, s')) : s.tree.get? c = none := by
  cases deep with
  | false =>
    obtain ⟨d, cd, -, -, -, -, -, hadd, -⟩ := cloneNode_shallow_spec h
    exact hadd.fresh
  | true =>
    obtain ⟨d, -, -, -, hfr, -⟩ := cloneNode_deep_spec h
    exact hfr

/--
**clone は原本と同じ形である。**

roadmap §8.4 の「structurally equivalent」。deep clone について、copy の subtree が
原本の subtree と kind・data・attribute・名前・children の並びまで一致する。
-/
theorem cloneNode_cloneOf {s s' : DOMState} {n c : NodeId}
    (h : cloneNode s n true = .ok (c, s')) : CloneOf s'.tree n c := by
  obtain ⟨-, -, -, -, -, hcl⟩ := cloneNode_deep_spec h
  exact hcl

/--
**clone は原本とは別の node である。**

roadmap §8.4 の「identity is different」。同じ形でも `NodeId` は違う。
-/
theorem cloneNode_ne {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (h : cloneNode s n deep = .ok (c, s')) : c ≠ n := by
  intro he
  have hn : s.tree.get? n ≠ none := by
    simp only [cloneNode] at h
    split at h
    · simp at h
    · next d hd => rw [hd]; simp
  exact hn (he ▸ cloneNode_fresh h)

/-- **clone は木しか変えない。** live range も `NodeIterator` も observer も動かない。 -/
theorem cloneNode_treeOnly {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (h : cloneNode s n deep = .ok (c, s')) : TreeOnly s s' := by
  cases deep with
  | false =>
    obtain ⟨d₀, cd, -, -, -, -, -, -, ht⟩ := cloneNode_shallow_spec h
    exact ht
  | true =>
    obtain ⟨-, -, ht, -⟩ := cloneNode_deep_spec h
    exact ht

/-- **clone は木にあった node を動かさない。** 原本の subtree はそのまま残る。 -/
theorem cloneNode_keep {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (h : cloneNode s n deep = .ok (c, s')) {m : NodeId} {md : NodeData}
    (hm : s.tree.get? m = some md) : s'.tree.get? m = some md := by
  cases deep with
  | false =>
    obtain ⟨d₀, cd, -, -, -, -, -, hadd, -⟩ := cloneNode_shallow_spec h
    rw [hadd.others m (hadd.ne_of_mem hm)]
    exact hm
  | true =>
    obtain ⟨-, -, -, hk, -⟩ := cloneNode_deep_spec h
    exact hk m md hm

end Dom
