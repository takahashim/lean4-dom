import Dom.Spec.Result
import Dom.Validity.PreserveInsertAt

/-!
# §4.2.9 `ChildNode` の mutation method の、結果まで含めた関係

`before` / `after` / `replaceWith` / `remove` は、仕様が pre-insert・replace・remove への
委譲として書いている。ここでは委譲の前の手順（parent が無ければ何もしない、
viable sibling の選び方、reference child の決め方）を仕様の語彙で書き、
委譲先は `PreInsertResult` / `ReplaceResult` / `RemoveResult` をそのまま使う。

model の method は node を一つだけ取る（「convert nodes into a node」の結果を引数に取る）。
したがって仕様の `nodes` は `[node]` である。

## 独立性

viable sibling は「this の preceding（following）sibling のうち `nodes` に無い最初のもの」
を、children の分割で書く。実行側の `viablePreviousSibling` / `viableNextSibling` は使わない。
-/

namespace Dom.Spec

open Dom

/-! ## viable sibling -/

/--
**§4.2.9 before の step 3：viable previous sibling。**

this の preceding sibling のうち `nodes` に無い、this に最も近いもの。無ければ null。
this の parent を `parent`、その children を `pre ++ this :: post` と分けたとき、
`pre = a ++ v :: b` で `v ∉ nodes`、`b` は全部 `nodes` にある。
-/
def ViablePreviousSibling (t : Tree) (this : NodeId) (nodes : List NodeId) :
    Option NodeId → Prop
  | some v => ∃ parent pre post a b, parentOf t this = some parent ∧
      childrenOf t parent = pre ++ this :: post ∧ pre = a ++ v :: b ∧ v ∉ nodes ∧
      ∀ x ∈ b, x ∈ nodes
  | none => ∀ parent pre post, parentOf t this = some parent →
      childrenOf t parent = pre ++ this :: post → ∀ x ∈ pre, x ∈ nodes

/--
**§4.2.9 after / replaceWith の step 3：viable next sibling。**

this の following sibling のうち `nodes` に無い、this に最も近いもの。無ければ null。
-/
def ViableNextSibling (t : Tree) (this : NodeId) (nodes : List NodeId) :
    Option NodeId → Prop
  | some v => ∃ parent pre post a b, parentOf t this = some parent ∧
      childrenOf t parent = pre ++ this :: post ∧ post = a ++ v :: b ∧ v ∉ nodes ∧
      ∀ x ∈ a, x ∈ nodes
  | none => ∀ parent pre post, parentOf t this = some parent →
      childrenOf t parent = pre ++ this :: post → ∀ x ∈ post, x ∈ nodes

/-- parent があれば、children は this のところで一通りに分かれ、`splitAt?` はそれを返す。 -/
private theorem split_of_parent {t : Tree} (hwf : WellFormed t) {this parent : NodeId}
    (hp : parentOf t this = some parent) :
    ∃ pre post, childrenOf t parent = pre ++ this :: post ∧
      ListUtil.splitAt? (childrenOf t parent) this = some (pre, post) := by
  have hmem := mem_childrenOf_of_parentOf hwf hp
  obtain ⟨⟨pre, post⟩, hsp⟩ := Option.isSome_iff_exists.mp (ListUtil.splitAt?_isSome_of_mem hmem)
  exact ⟨pre, post, ListUtil.splitAt?_eq_some hsp, hsp⟩

/-- 関係を満たす viable previous sibling は、実行側の値と等しい。 -/
theorem viablePreviousSibling_eq_of_spec {t : Tree} (hwf : WellFormed t)
    {this parent : NodeId} {nodes : List NodeId} {v : Option NodeId}
    (hp : parentOf t this = some parent) (h : ViablePreviousSibling t this nodes v) :
    v = viablePreviousSibling t this nodes := by
  unfold viablePreviousSibling
  rw [hp]
  simp only []
  cases v with
  | none =>
    obtain ⟨pre, post, hc, hsp⟩ := split_of_parent hwf hp
    rw [hsp]
    simp only []
    symm
    rw [List.find?_eq_none]
    intro x hx
    simpa using h parent pre post hp hc x (List.mem_reverse.mp hx)
  | some v =>
    obtain ⟨parent', pre, post, a, b, hp', hc, hpre, hv, hb⟩ := h
    rw [hp] at hp'
    cases hp'
    rw [splitAt?_childrenOf_of_split hwf hc]
    simp only []
    symm
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simpa using hv, b.reverse, a.reverse, by simp [hpre], ?_⟩
    intro x hx
    simpa using hb x (List.mem_reverse.mp hx)

/-- 実行側の viable previous sibling は関係を満たす。 -/
theorem viablePreviousSibling_spec {t : Tree} (hwf : WellFormed t) (this : NodeId)
    (nodes : List NodeId) :
    ViablePreviousSibling t this nodes (viablePreviousSibling t this nodes) := by
  cases h : viablePreviousSibling t this nodes with
  | none =>
    intro parent pre post hp hc x hx
    unfold viablePreviousSibling at h
    rw [hp] at h
    simp only [] at h
    rw [splitAt?_childrenOf_of_split hwf hc] at h
    simp only [List.find?_eq_none] at h
    simpa using h x (List.mem_reverse.mpr hx)
  | some v =>
    unfold viablePreviousSibling at h
    split at h
    · cases h
    · next parent hp =>
      obtain ⟨pre, post, hc, hsp⟩ := split_of_parent hwf hp
      rw [hsp] at h
      simp only [] at h
      obtain ⟨hv, as, bs, hrev, has⟩ := List.find?_eq_some_iff_append.mp h
      refine ⟨parent, pre, post, bs.reverse, as.reverse, hp, hc, ?_, by simpa using hv, ?_⟩
      · rw [← List.reverse_reverse pre, hrev]; simp
      · intro x hx
        simpa using has x (List.mem_reverse.mp hx)

/-- 関係を満たす viable next sibling は、実行側の値と等しい。 -/
theorem viableNextSibling_eq_of_spec {t : Tree} (hwf : WellFormed t)
    {this parent : NodeId} {nodes : List NodeId} {v : Option NodeId}
    (hp : parentOf t this = some parent) (h : ViableNextSibling t this nodes v) :
    v = viableNextSibling t this nodes := by
  unfold viableNextSibling
  rw [hp]
  simp only []
  cases v with
  | none =>
    obtain ⟨pre, post, hc, hsp⟩ := split_of_parent hwf hp
    rw [hsp]
    simp only []
    symm
    rw [List.find?_eq_none]
    intro x hx
    simpa using h parent pre post hp hc x hx
  | some v =>
    obtain ⟨parent', pre, post, a, b, hp', hc, hpost, hv, ha⟩ := h
    rw [hp] at hp'
    cases hp'
    rw [splitAt?_childrenOf_of_split hwf hc]
    simp only []
    symm
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simpa using hv, a, b, hpost, ?_⟩
    intro x hx
    simpa using ha x hx

/-- 実行側の viable next sibling は関係を満たす。 -/
theorem viableNextSibling_spec {t : Tree} (hwf : WellFormed t) (this : NodeId)
    (nodes : List NodeId) :
    ViableNextSibling t this nodes (viableNextSibling t this nodes) := by
  cases h : viableNextSibling t this nodes with
  | none =>
    intro parent pre post hp hc x hx
    unfold viableNextSibling at h
    rw [hp] at h
    simp only [] at h
    rw [splitAt?_childrenOf_of_split hwf hc] at h
    simp only [List.find?_eq_none] at h
    simpa using h x hx
  | some v =>
    unfold viableNextSibling at h
    split at h
    · cases h
    · next parent hp =>
      obtain ⟨pre, post, hc, hsp⟩ := split_of_parent hwf hp
      rw [hsp] at h
      simp only [] at h
      obtain ⟨hv, as, bs, hpost, has⟩ := List.find?_eq_some_iff_append.mp h
      exact ⟨parent, pre, post, as, bs, hp, hc, hpost, by simpa using hv,
        fun x hx => by simpa using has x hx⟩

/-! ## `before(nodes)` -/

/--
**§4.2.9 `before(nodes)` の、結果まで含めた関係。**

1-2. parent が null なら何もしない。
3. viablePreviousSibling を取る。
5. それが null なら parent の first child、でなければその next sibling を reference にする。
6. pre-insert する。
-/
def BeforeResult (s : DOMState) (this node : NodeId) :
    Except DOMException DOMState → Prop
  | r => (parentOf s.tree this = none ∧ r = .ok s) ∨
    ∃ parent v, parentOf s.tree this = some parent ∧
      ViablePreviousSibling s.tree this [node] v ∧
      PreInsertResult s node parent
        (match v with
         | none => (childrenOf s.tree parent).head?
         | some v => nextSibling s.tree v) r

theorem before_result_sound {s : DOMState} (hwf : WellFormed s.tree) (this node : NodeId) :
    BeforeResult s this node (before s this node) := by
  unfold before
  split
  · next hp => exact Or.inl ⟨hp, rfl⟩
  · next parent hp =>
    exact Or.inr ⟨parent, _, hp, viablePreviousSibling_spec hwf this [node],
      preInsert_result_sound hwf node parent _⟩

theorem before_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {this node : NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : BeforeResult s this node r₁) (h₂ : BeforeResult s this node r₂) :
    ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨hp₁, rfl⟩ | ⟨p₁, v₁, hp₁, hv₁, hr₁⟩ <;>
  rcases h₂ with ⟨hp₂, rfl⟩ | ⟨p₂, v₂, hp₂, hv₂, hr₂⟩
  · exact ResultObsEq.refl _
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
    rw [viablePreviousSibling_eq_of_spec hwf hp₁ hv₁] at hr₁
    rw [viablePreviousSibling_eq_of_spec hwf hp₁ hv₂] at hr₂
    exact preInsert_result_deterministic hwf hr₁ hr₂

theorem before_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {this node : NodeId} {r : Except DOMException DOMState} (h : BeforeResult s this node r) :
    ResultObsEq r (before s this node) :=
  before_result_deterministic hwf h (before_result_sound hwf this node)

/-! ## `after(nodes)` -/

/--
**§4.2.9 `after(nodes)` の、結果まで含めた関係。**

1-2. parent が null なら何もしない。
3. viableNextSibling を取る。
5. それを reference にして pre-insert する。
-/
def AfterResult (s : DOMState) (this node : NodeId) :
    Except DOMException DOMState → Prop
  | r => (parentOf s.tree this = none ∧ r = .ok s) ∨
    ∃ parent v, parentOf s.tree this = some parent ∧
      ViableNextSibling s.tree this [node] v ∧ PreInsertResult s node parent v r

theorem after_result_sound {s : DOMState} (hwf : WellFormed s.tree) (this node : NodeId) :
    AfterResult s this node (after s this node) := by
  unfold after
  split
  · next hp => exact Or.inl ⟨hp, rfl⟩
  · next parent hp =>
    exact Or.inr ⟨parent, _, hp, viableNextSibling_spec hwf this [node],
      preInsert_result_sound hwf node parent _⟩

theorem after_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {this node : NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : AfterResult s this node r₁) (h₂ : AfterResult s this node r₂) :
    ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨hp₁, rfl⟩ | ⟨p₁, v₁, hp₁, hv₁, hr₁⟩ <;>
  rcases h₂ with ⟨hp₂, rfl⟩ | ⟨p₂, v₂, hp₂, hv₂, hr₂⟩
  · exact ResultObsEq.refl _
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
    rw [viableNextSibling_eq_of_spec hwf hp₁ hv₁] at hr₁
    rw [viableNextSibling_eq_of_spec hwf hp₁ hv₂] at hr₂
    exact preInsert_result_deterministic hwf hr₁ hr₂

theorem after_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {this node : NodeId} {r : Except DOMException DOMState} (h : AfterResult s this node r) :
    ResultObsEq r (after s this node) :=
  after_result_deterministic hwf h (after_result_sound hwf this node)

/-! ## `replaceWith(nodes)` -/

/--
**§4.2.9 `replaceWith(nodes)` の、結果まで含めた関係。**

1-2. parent が null なら何もしない。
5. this の parent がまだ parent なら、this を node で replace する。

仕様の step 4（convert nodes into a node）は、引数の node が this の祖先などを
動かしうるので step 5 の条件が要る。model の method は変換済みの node を取り、
step 1 から 5 の間に木を変えないので、step 5 の条件は常に成り立つ。
step 3 の viableNextSibling と step 6 の pre-insert は使われない。
-/
def ReplaceWithResult (s : DOMState) (this node : NodeId) :
    Except DOMException DOMState → Prop
  | r => (parentOf s.tree this = none ∧ r = .ok s) ∨
    ∃ parent, parentOf s.tree this = some parent ∧ ReplaceResult s this node parent r

theorem replaceWith_result_sound {s : DOMState} (hsv : StructurallyValid s.tree)
    (this node : NodeId) : ReplaceWithResult s this node (replaceWith s this node) := by
  unfold replaceWith
  split
  · next hp => exact Or.inl ⟨hp, rfl⟩
  · next parent hp =>
    rw [if_pos hp]
    exact Or.inr ⟨parent, hp, replace_result_sound hsv this node parent⟩

theorem replaceWith_result_deterministic {s : DOMState} (hsv : StructurallyValid s.tree)
    {this node : NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceWithResult s this node r₁) (h₂ : ReplaceWithResult s this node r₂) :
    ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨hp₁, rfl⟩ | ⟨p₁, hp₁, hr₁⟩ <;>
  rcases h₂ with ⟨hp₂, rfl⟩ | ⟨p₂, hp₂, hr₂⟩
  · exact ResultObsEq.refl _
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
    exact replace_result_deterministic hsv hr₁ hr₂

theorem replaceWith_result_complete {s : DOMState} (hsv : StructurallyValid s.tree)
    {this node : NodeId} {r : Except DOMException DOMState}
    (h : ReplaceWithResult s this node r) : ResultObsEq r (replaceWith s this node) :=
  replaceWith_result_deterministic hsv h (replaceWith_result_sound hsv this node)

/-! ## `remove()` -/

/--
**§4.2.9 `remove()` の、結果まで含めた関係。**

parent が null なら何もせず、そうでなければ remove する。
-/
def NodeRemoveResult (s : DOMState) (this : NodeId) :
    Except DOMException DOMState → Prop
  | r => (parentOf s.tree this = none ∧ r = .ok s) ∨
    (parentOf s.tree this ≠ none ∧ RemoveResult s this false r)

theorem nodeRemove_result_sound {s : DOMState} (hwf : WellFormed s.tree) (this : NodeId) :
    NodeRemoveResult s this (nodeRemove s this) := by
  unfold nodeRemove
  split
  · next hp => exact Or.inl ⟨hp, rfl⟩
  · next parent hp =>
    exact Or.inr ⟨by simp [hp], remove_result_sound hwf this false⟩

theorem nodeRemove_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {this : NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : NodeRemoveResult s this r₁) (h₂ : NodeRemoveResult s this r₂) :
    ResultObsEq r₁ r₂ := by
  rcases h₁ with ⟨hp₁, rfl⟩ | ⟨hp₁, hr₁⟩ <;>
  rcases h₂ with ⟨hp₂, rfl⟩ | ⟨hp₂, hr₂⟩
  · exact ResultObsEq.refl _
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · exact remove_result_deterministic hwf hr₁ hr₂

theorem nodeRemove_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {this : NodeId} {r : Except DOMException DOMState} (h : NodeRemoveResult s this r) :
    ResultObsEq r (nodeRemove s this) :=
  nodeRemove_result_deterministic hwf h (nodeRemove_result_sound hwf this)

end Dom.Spec
