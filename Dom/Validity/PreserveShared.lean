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
