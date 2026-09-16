import Dom.Validity.Preservation
import Dom.Properties.Algorithms
import Dom.Properties.CharacterData

/-!
# 共有の補題と、木の形を変えない操作

`filter` の小補題と、kind / children が同じなら制約も同じであること、
それに `ensure pre-insertion validity` が確立する kind の事実。
-/

namespace Dom

/-- 述語を満たす要素が無ければ filter は空。 -/
theorem filter_eq_nil_of_all_false {α : Type _} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  cases hl : l.filter p with
  | nil => rfl
  | cons y r =>
    exfalso
    have hy : y ∈ l.filter p := by rw [hl]; simp
    obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
    rw [h y hy1] at hy2
    simp at hy2

/-- 空でない filter からは、述語を満たす要素が取り出せる。 -/
theorem exists_mem_of_filter_ne_nil {α : Type _} {l : List α} {p : α → Bool}
    (h : l.filter p ≠ []) : ∃ x ∈ l, p x = true := by
  cases hl : l.filter p with
  | nil => exact absurd hl h
  | cons y r =>
    have hy : y ∈ l.filter p := by rw [hl]; simp
    obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
    exact ⟨y, hy1, hy2⟩

/-! ## kind の事実は kind を変えない操作で移る -/

theorem kindFact_of_kindPreserving {t t' : Tree} (h : ShapePreserving t t') {n : NodeId}
    {P : NodeKind → Prop} (hp : ∀ d, t.get? n = some d → P d.kind) :
    ∀ d, t'.get? n = some d → P d.kind := by
  intro d hd
  have hk := h.kind n
  rw [hd] at hk
  cases hd' : t.get? n with
  | none => rw [hd'] at hk; simp at hk
  | some d' =>
    rw [hd'] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    rw [hk]
    exact hp d' hd'

/-- kind が同じなら、node の有無も一致する。 -/
theorem shapePreserving_get? {t t' : Tree} (h : ShapePreserving t t') {m : NodeId} {d : NodeData}
    (hd : t'.get? m = some d) : ∃ d₀, t.get? m = some d₀ ∧ d₀.kind = d.kind := by
  have hk := h.kind m
  rw [hd] at hk
  cases hd₀ : t.get? m with
  | none => rw [hd₀] at hk; simp at hk
  | some d₀ =>
    rw [hd₀] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    exact ⟨d₀, rfl, hk.symm⟩

/-- 「doctype を入れる先は Document である」という事実も kind を変えない操作で移る。 -/
theorem doctypeFact_of_kindPreserving {t t' : Tree} (h : ShapePreserving t t') {n p : NodeId}
    (hp : ∀ nd, t.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t.get? p = some pd → pd.kind = .document) :
    ∀ nd, t'.get? n = some nd → nd.kind = .documentType →
      ∀ pd, t'.get? p = some pd → pd.kind = .document := by
  intro nd hnd hk pd hpd
  obtain ⟨nd₀, hnd₀, hkn⟩ := shapePreserving_get? h hnd
  obtain ⟨pd₀, hpd₀, hkp⟩ := shapePreserving_get? h hpd
  rw [← hkp]
  exact hp nd₀ hnd₀ (by rw [hkn]; exact hk) pd₀ hpd₀

/-! ## 挿入の前提 -/

/--
挿入の保存定理が共有する四つの前提。

`insertEach` / `insertNodesAt` / `insert` の保存定理はどれも同じ仮定列を並べて
いたので、`IterCtx` と同じように bundle にした。定理の意味が読みやすくなり、
仮定の付け忘れにも強い。

四つはすべて `ensure pre-insertion validity` が確立するものである。
-/
structure InsertFacts (t : Tree) (parent : NodeId) (ns : List NodeId) : Prop where
  /-- step 1。parent は children を持てる kind である。 -/
  parentCanHaveChildren : ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true
  /-- step 4。入れる node は Document ではない。 -/
  notDocument : ∀ n ∈ ns, ∀ nd, t.get? n = some nd → nd.kind ≠ NodeKind.document
  /-- 入れる node は DocumentFragment ではない（fragment は step 1 で展開済み）。 -/
  notFragment : ∀ n ∈ ns, ∀ nd, t.get? n = some nd → nd.kind ≠ NodeKind.documentFragment
  /-- step 5。doctype を入れる先は Document である。 -/
  doctypeParentIsDocument : ∀ n ∈ ns, ∀ nd, t.get? n = some nd →
    nd.kind = NodeKind.documentType →
    ∀ pd, t.get? parent = some pd → pd.kind = NodeKind.document

namespace InsertFacts

/-- kind を変えない操作で前提は移る。 -/
theorem congr {t t' : Tree} {parent : NodeId} {ns : List NodeId}
    (hkp : ShapePreserving t t') (h : InsertFacts t parent ns) : InsertFacts t' parent ns where
  parentCanHaveChildren :=
    kindFact_of_kindPreserving hkp (P := fun k => k.canHaveChildren = true)
      h.parentCanHaveChildren
  notDocument := fun n hn =>
    kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.document) (h.notDocument n hn)
  notFragment := fun n hn =>
    kindFact_of_kindPreserving hkp (P := fun k => k ≠ NodeKind.documentFragment)
      (h.notFragment n hn)
  doctypeParentIsDocument := fun n hn =>
    doctypeFact_of_kindPreserving hkp (h.doctypeParentIsDocument n hn)

/-- 先頭を落としても前提は残る。 -/
theorem tail {t : Tree} {parent n : NodeId} {ns : List NodeId}
    (h : InsertFacts t parent (n :: ns)) : InsertFacts t parent ns where
  parentCanHaveChildren := h.parentCanHaveChildren
  notDocument := fun m hm => h.notDocument m (List.mem_cons_of_mem _ hm)
  notFragment := fun m hm => h.notFragment m (List.mem_cons_of_mem _ hm)
  doctypeParentIsDocument := fun m hm => h.doctypeParentIsDocument m (List.mem_cons_of_mem _ hm)

/-- 一つの node についての前提から、一要素の列についての前提を作る。 -/
theorem singleton {t : Tree} {parent node : NodeId}
    (hpk : ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true)
    (hnk : ∀ nd, t.get? node = some nd → nd.kind ≠ NodeKind.document)
    (hnf : ∀ nd, t.get? node = some nd → nd.kind ≠ NodeKind.documentFragment)
    (hdt : ∀ nd, t.get? node = some nd → nd.kind = NodeKind.documentType →
      ∀ pd, t.get? parent = some pd → pd.kind = NodeKind.document) :
    InsertFacts t parent [node] where
  parentCanHaveChildren := hpk
  notDocument := fun m hm => by rcases List.mem_singleton.mp hm with rfl; exact hnk
  notFragment := fun m hm => by rcases List.mem_singleton.mp hm with rfl; exact hnf
  doctypeParentIsDocument := fun m hm => by rcases List.mem_singleton.mp hm with rfl; exact hdt

end InsertFacts

/-! ## 木の形を変えない操作 -/

/--
kind と children が同じなら、document tree の制約も同じである。

`setOwnerDocument` と `replaceData` はどちらもこれに当たる。
-/
theorem documentTreesValid_of_sameShape {t t' : Tree}
    (hkind : ∀ m, kindOf t' m = kindOf t m)
    (hch : ∀ m, childrenOf t' m = childrenOf t m)
    (h : DocumentTreesValid t) : DocumentTreesValid t' := by
  have helem : ∀ m, elementChildren t' m = elementChildren t m := by
    intro m; unfold elementChildren; simp [hch, hkind]
  have hdt : ∀ m, doctypeChildren t' m = doctypeChildren t m := by
    intro m; unfold doctypeChildren; simp [hch, hkind]
  have htx : ∀ m, textChildren t' m = textChildren t m := by
    intro m; unfold textChildren; simp [hch, hkind]
  have hfol : ∀ m c, doctypeFollows t' m c = doctypeFollows t m c := by
    intro m c; exact doctypeFollows_congr (hch m) hkind
  refine ⟨fun doc d hdoc hk => ?_⟩
  have hdoc' : ∃ d', t.get? doc = some d' ∧ d'.kind = .document := by
    have := hkind doc
    rw [kindOf_eq, kindOf_eq, hdoc] at this
    cases hd' : t.get? doc with
    | none => rw [hd'] at this; simp at this
    | some d' =>
      rw [hd'] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨d', rfl, by rw [← this]; exact hk⟩
  obtain ⟨d', hd', hk'⟩ := hdoc'
  obtain ⟨h1, h2, h3, h4⟩ := h.documentChildren doc d' hd' hk'
  exact ⟨by rw [helem]; exact h1, by rw [hdt]; exact h2, by rw [htx]; exact h3,
    fun e he => by rw [hfol]; exact h4 e (by rw [← helem]; exact he)⟩

/-! ## ensure pre-insert validity が確立する kind の事実 -/

/--
step 1。parent は Document / DocumentFragment / Element のいずれかである。
すなわち children を持てる kind である。
-/
theorem ensurePreInsertionValidity_parentCanHaveChildren {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ pd, t.get? parent = some pd → pd.kind.canHaveChildren = true := by
  intro pd hpd
  obtain ⟨pd', _, hpd', -, hk, -, -, -, -⟩ := ensurePreInsertionValidity_ok_steps h
  rw [hpd] at hpd'
  cases hpd'
  cases hkk : pd.kind <;> rw [hkk] at hk <;> simp_all [NodeKind.canHaveChildren]

/-- step 5。parent が Document でないなら doctype は入れられない。逆に言えば、doctype を入れる先は Document である。 -/
theorem ensurePreInsertionValidity_doctypeParentIsDocument {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ nd, t.get? node = some nd → nd.kind = .documentType →
      ∀ pd, t.get? parent = some pd → pd.kind = .document := by
  intro nd hnd hk pd hpd
  obtain ⟨pd', nd', hpd', hnd', -, -, -, -, hstep5⟩ := ensurePreInsertionValidity_ok_steps h
  rw [hpd] at hpd'; cases hpd'
  rw [hnd] at hnd'; cases hnd'
  by_cases hd : pd.kind = NodeKind.document
  · exact hd
  · exact absurd (by simp [hk]) (hstep5 hd)

/-- step 3。`child` が指定されていれば、その parent は `parent` である。 -/
theorem ensurePreInsertionValidity_childParent {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ c, child = some c → parentOf t c = some parent := by
  intro c hc
  subst hc
  obtain ⟨-, -, -, -, -, -, hch, -, -⟩ := ensurePreInsertionValidity_ok_steps h
  exact childHasParent_some_iff.mp hch

/-- step 4。node は DocumentFragment / DocumentType / Element / CharacterData であり、Document ではない。 -/
theorem ensurePreInsertionValidity_nodeNotDocument {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ nd, t.get? node = some nd → nd.kind ≠ .document := by
  intro nd hnd
  obtain ⟨-, nd', -, hnd', -, -, -, hk, -⟩ := ensurePreInsertionValidity_ok_steps h
  rw [hnd] at hnd'
  cases hnd'
  cases hkk : nd.kind <;> rw [hkk] at hk <;> simp_all [NodeKind.isCharacterData]

end Dom
