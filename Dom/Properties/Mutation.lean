import Dom.Mutation.Detach
import Dom.Mutation.Insert
import Dom.Mutation.Adopt
import Dom.Properties.Tree

/-!
# Phase 2 の theorem

PLAN §5.2 に従い、三つの primitive のそれぞれについて次の三種類を証明する。

- **preservation** — `WellFormed t → op t … = .ok t' → WellFormed t'`
- **effect** — 操作した node と parent の `children` が期待どおりになる
- **frame** — 操作に関係しない node の `NodeData` は変わらない

frame は Phase 3 で複合 algorithm の性質を primitive の性質から組み立てるときに使う。
-/

namespace Dom

open Dom.ListUtil

variable {t : Tree}

/-! ## 共通の補助補題 -/

/-- `get?` が一致する node では `parentOf` も一致する。 -/
theorem parentOf_congr {t t' : Tree} {m : NodeId} (h : t'.get? m = t.get? m) :
    parentOf t' m = parentOf t m := by
  unfold parentOf; rw [h]

/-- `get?` が一致する node では `childrenOf` も一致する。 -/
theorem childrenOf_congr {t t' : Tree} {m : NodeId} (h : t'.get? m = t.get? m) :
    childrenOf t' m = childrenOf t m := by
  unfold childrenOf; rw [h]

/--
`WellFormed` の `parent_child` と `child_parent` は、
「parent 関係と children 関係が一致する」という一つの同値に等しい。

`parentOf` と `childrenOf` が木に無い node を `none` / `[]` に潰すので、
node の存在条件はこの同値から導ける。
-/
theorem mem_childrenOf_iff (hwf : WellFormed t) (c p : NodeId) :
    parentOf t c = some p ↔ c ∈ childrenOf t p :=
  ⟨mem_childrenOf_of_parentOf hwf, parentOf_of_mem_childrenOf hwf⟩

/-- 上の同値と残りの三条件から `WellFormed` を組み立てる。 -/
theorem wellFormed_of {t : Tree}
    (hiff : ∀ c p, parentOf t c = some p ↔ c ∈ childrenOf t p)
    (hnodup : ∀ n d, t.get? n = some d → d.children.Nodup)
    (hacyc : ∀ n, ¬ Ancestor t n n)
    (hdoc : ∀ n d, t.get? n = some d →
      ∃ dd, t.get? d.ownerDocument = some dd ∧ dd.kind = .document) : WellFormed t where
  parent_child := by
    intro p pd hpd c hc
    exact parentOf_eq_some ((hiff c p).mpr (by rw [childrenOf_eq hpd]; exact hc))
  child_parent := by
    intro c cd p hcd hcdp
    exact exists_data_of_mem_childrenOf ((hiff c p).mp (by simp [parentOf, hcd, hcdp]))
  children_nodup := hnodup
  acyclic := hacyc
  ownerDocument_is_document := hdoc

/-- node document と kind を保つ変更は `ownerDocument_is_document` を保つ。 -/
theorem ownerDocument_is_document_of {t t' : Tree} (hwf : WellFormed t)
    (hown : ∀ m d, t'.get? m = some d →
      ∃ d₀, t.get? m = some d₀ ∧ d.ownerDocument = d₀.ownerDocument)
    (hkind : ∀ m d₀, t.get? m = some d₀ → ∃ d, t'.get? m = some d ∧ d.kind = d₀.kind) :
    ∀ n d, t'.get? n = some d →
      ∃ dd, t'.get? d.ownerDocument = some dd ∧ dd.kind = .document := by
  intro n d hn
  obtain ⟨d₀, hd₀, howneq⟩ := hown n d hn
  obtain ⟨dd, hdd, hdk⟩ := hwf.ownerDocument_is_document n d₀ hd₀
  obtain ⟨dd', hdd', hdk'⟩ := hkind _ dd hdd
  exact ⟨dd', by rw [howneq]; exact hdd', by rw [hdk', hdk]⟩

/-! ## detach -/

section Detach

variable {t : Tree} {n p : NodeId} {d pd : NodeData}

theorem get?_detachFrom (t : Tree) (n p : NodeId) (d pd : NodeData) (m : NodeId) :
    (detachFrom t n p d pd).get? m =
      if m = n then some { d with parent := none }
      else if m = p then some { pd with children := removeAll pd.children n }
      else t.get? m := by
  show ((t.nodes.insert p _).insert n _).get? m = _
  by_cases h1 : m = n
  · subst h1; simp
  · rw [NodeStore.get?_insert_ne _ (Ne.symm h1), if_neg h1]
    by_cases h2 : m = p
    · subst h2; simp
    · rw [NodeStore.get?_insert_ne _ (Ne.symm h2), if_neg h2]
      rfl

@[simp] theorem get?_detachFrom_self (t : Tree) (n p : NodeId) (d pd : NodeData) :
    (detachFrom t n p d pd).get? n = some { d with parent := none } := by
  simp [get?_detachFrom]

theorem get?_detachFrom_parent (hpn : p ≠ n) :
    (detachFrom t n p d pd).get? p = some { pd with children := removeAll pd.children n } := by
  simp [get?_detachFrom, hpn]

theorem get?_detachFrom_other {m : NodeId} (h1 : m ≠ n) (h2 : m ≠ p) :
    (detachFrom t n p d pd).get? m = t.get? m := by
  simp [get?_detachFrom, h1, h2]

theorem parentOf_detachFrom (hpd : t.get? p = some pd) (m : NodeId) :
    parentOf (detachFrom t n p d pd) m = if m = n then none else parentOf t m := by
  by_cases h1 : m = n
  · subst h1; simp [parentOf]
  · by_cases h2 : m = p
    · subst h2; simp [parentOf, get?_detachFrom_parent h1, hpd, h1]
    · rw [parentOf_congr (get?_detachFrom_other h1 h2), if_neg h1]

theorem childrenOf_detachFrom (hd : t.get? n = some d) (hpd : t.get? p = some pd) (hpn : p ≠ n)
    (m : NodeId) :
    childrenOf (detachFrom t n p d pd) m =
      if m = p then removeAll (childrenOf t p) n else childrenOf t m := by
  by_cases h2 : m = p
  · subst h2
    rw [childrenOf_eq (get?_detachFrom_parent hpn), childrenOf_eq hpd, if_pos rfl]
  · by_cases h1 : m = n
    · subst h1
      rw [childrenOf_eq (get?_detachFrom_self t _ p d pd), childrenOf_eq hd, if_neg h2]
    · rw [childrenOf_congr (get?_detachFrom_other h1 h2), if_neg h2]

/-- PLAN §5.2 preservation。 -/
theorem detachFrom_preserves_wellformed (hwf : WellFormed t)
    (hd : t.get? n = some d) (hp : d.parent = some p) (hpd : t.get? p = some pd) :
    WellFormed (detachFrom t n p d pd) := by
  have hpar : parentOf t n = some p := by simp [parentOf, hd, hp]
  have hpn : p ≠ n := by
    intro he
    exact hwf.acyclic n (Ancestor.step (he ▸ hpar))
  have hnodup : (childrenOf t p).Nodup := by
    rw [childrenOf_eq hpd]; exact hwf.children_nodup p pd hpd
  refine wellFormed_of ?_ ?_ ?_ ?_
  · -- parent 関係と children 関係の一致
    intro c q
    rw [parentOf_detachFrom hpd, childrenOf_detachFrom hd hpd hpn]
    by_cases hcn : c = n
    · rw [if_pos hcn]
      by_cases hqp : q = p
      · rw [if_pos hqp]
        constructor
        · intro he; exact absurd he (by simp)
        · intro hmem
          exact absurd (hcn ▸ hmem) (not_mem_removeAll _ _)
      · rw [if_neg hqp]
        constructor
        · intro he; exact absurd he (by simp)
        · intro hmem
          exfalso
          have hq := (mem_childrenOf_iff hwf c q).mpr hmem
          rw [hcn, hpar] at hq
          exact hqp (Option.some.inj hq).symm
    · rw [if_neg hcn]
      by_cases hqp : q = p
      · rw [if_pos hqp, hqp, mem_removeAll, ← mem_childrenOf_iff hwf]
        exact ⟨fun h => ⟨hcn, h⟩, fun h => h.2⟩
      · rw [if_neg hqp, ← mem_childrenOf_iff hwf]
  · -- children の重複の無さ
    intro m dm hm
    rw [get?_detachFrom] at hm
    by_cases h1 : m = n
    · subst h1
      rw [if_pos rfl] at hm
      cases hm
      show d.children.Nodup
      exact hwf.children_nodup _ _ hd
    · rw [if_neg h1] at hm
      by_cases h2 : m = p
      · subst h2
        rw [if_pos rfl] at hm
        cases hm
        show (removeAll pd.children n).Nodup
        exact nodup_removeAll (hwf.children_nodup _ _ hpd) _
      · rw [if_neg h2] at hm
        exact hwf.children_nodup m dm hm
  · -- acyclicity（parent が減る向きの変更なので保たれる）
    intro m hm
    refine hwf.acyclic m (ancestor_of_parentOf_subset ?_ hm)
    intro x y hxy
    rw [parentOf_detachFrom hpd] at hxy
    by_cases hxn : x = n
    · rw [if_pos hxn] at hxy; simp at hxy
    · rw [if_neg hxn] at hxy; exact hxy
  · -- node document
    refine ownerDocument_is_document_of hwf ?_ ?_
    · intro m dm hm
      rw [get?_detachFrom] at hm
      by_cases h1 : m = n
      · subst h1; rw [if_pos rfl] at hm; cases hm; exact ⟨d, hd, rfl⟩
      · rw [if_neg h1] at hm
        by_cases h2 : m = p
        · subst h2; rw [if_pos rfl] at hm; cases hm; exact ⟨pd, hpd, rfl⟩
        · rw [if_neg h2] at hm; exact ⟨dm, hm, rfl⟩
    · intro m d₀ hm
      rw [get?_detachFrom]
      by_cases h1 : m = n
      · subst h1; rw [hd] at hm; cases hm; simp
      · rw [if_neg h1]
        by_cases h2 : m = p
        · subst h2; rw [hpd] at hm; cases hm; simp
        · rw [if_neg h2]; exact ⟨d₀, hm, rfl⟩

end Detach

/-! ### `detach` に持ち上げる -/

theorem detach_preserves_wellformed {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (h : detach t n = .ok t') : WellFormed t' := by
  rcases detach_ok_cases h with ⟨d, _, _, rfl⟩ | ⟨d, p, pd, hd, hp, hpd, rfl⟩
  · exact hwf
  · exact detachFrom_preserves_wellformed hwf hd hp hpd

/-- PLAN §5.2 effect。detach した node は parent を持たない。 -/
theorem detach_parentOf {t t' : Tree} {n : NodeId} (h : detach t n = .ok t') :
    parentOf t' n = none := by
  rcases detach_ok_cases h with ⟨d, hd, hp, rfl⟩ | ⟨d, p, pd, hd, hp, hpd, rfl⟩
  · simp [parentOf, hd, hp]
  · simp [parentOf]

/-- PLAN §5.2 effect。旧 parent の children から取り除かれる。 -/
theorem detach_childrenOf {t t' : Tree} {n p : NodeId}
    (hwf : WellFormed t) (hpar : parentOf t n = some p) (h : detach t n = .ok t') :
    childrenOf t' p = removeAll (childrenOf t p) n := by
  rcases detach_ok_cases h with ⟨d, hd, hp, rfl⟩ | ⟨d, p', pd, hd, hp, hpd, rfl⟩
  · rw [parentOf, hd] at hpar; simp [hp] at hpar
  · have hpp : p' = p := by
      rw [parentOf, hd] at hpar
      exact Option.some.inj (hp ▸ hpar : some p' = some p)
    subst hpp
    have hpn : p' ≠ n := fun he => hwf.acyclic n (Ancestor.step (he ▸ hpar))
    rw [childrenOf_detachFrom hd hpd hpn, if_pos rfl]

/-- PLAN §5.2 frame。detach した node とその旧 parent 以外は変わらない。 -/
theorem detach_frame {t t' : Tree} {n : NodeId} (h : detach t n = .ok t') {m : NodeId}
    (hmn : m ≠ n) (hmp : ∀ p, parentOf t n = some p → m ≠ p) : t'.get? m = t.get? m := by
  rcases detach_ok_cases h with ⟨d, hd, hp, rfl⟩ | ⟨d, p, pd, hd, hp, hpd, rfl⟩
  · rfl
  · exact get?_detachFrom_other hmn (hmp p (by simp [parentOf, hd, hp]))

/-- parent を持たない node に対する `detach` は木を変えない。 -/
theorem detach_of_no_parent {t : Tree} {n : NodeId} (h : parentOf t n = none)
    (hd : (t.get? n).isSome) : detach t n = .ok t := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
  exact detach_of_parent_eq_none hd (by rw [parentOf, hd] at h; simpa using h)

/-! ## insertAt -/

section Insert

variable {t : Tree} {parent node : NodeId} {child : Option NodeId} {pd nd : NodeData}

theorem get?_insertAtIn (t : Tree) (parent node : NodeId) (child : Option NodeId)
    (pd nd : NodeData) (m : NodeId) :
    (insertAtIn t parent node child pd nd).get? m =
      if m = node then some { nd with parent := some parent }
      else if m = parent then some { pd with children := insertBefore pd.children child node }
      else t.get? m := by
  show ((t.nodes.insert parent _).insert node _).get? m = _
  by_cases h1 : m = node
  · subst h1; simp
  · rw [NodeStore.get?_insert_ne _ (Ne.symm h1), if_neg h1]
    by_cases h2 : m = parent
    · subst h2; simp
    · rw [NodeStore.get?_insert_ne _ (Ne.symm h2), if_neg h2]
      rfl

@[simp] theorem get?_insertAtIn_self (t : Tree) (parent node : NodeId) (child : Option NodeId)
    (pd nd : NodeData) :
    (insertAtIn t parent node child pd nd).get? node = some { nd with parent := some parent } := by
  simp [get?_insertAtIn]

theorem get?_insertAtIn_parent (hne : node ≠ parent) :
    (insertAtIn t parent node child pd nd).get? parent =
      some { pd with children := insertBefore pd.children child node } := by
  simp [get?_insertAtIn, Ne.symm hne]

theorem get?_insertAtIn_other {m : NodeId} (h1 : m ≠ node) (h2 : m ≠ parent) :
    (insertAtIn t parent node child pd nd).get? m = t.get? m := by
  simp [get?_insertAtIn, h1, h2]

theorem parentOf_insertAtIn (hpd : t.get? parent = some pd) (m : NodeId) :
    parentOf (insertAtIn t parent node child pd nd) m =
      if m = node then some parent else parentOf t m := by
  by_cases h1 : m = node
  · subst h1; simp [parentOf]
  · by_cases h2 : m = parent
    · subst h2
      simp [parentOf, get?_insertAtIn_parent (fun he => h1 he.symm), hpd, h1]
    · rw [parentOf_congr (get?_insertAtIn_other h1 h2), if_neg h1]

theorem childrenOf_insertAtIn (hnd : t.get? node = some nd) (hpd : t.get? parent = some pd)
    (hne : node ≠ parent) (m : NodeId) :
    childrenOf (insertAtIn t parent node child pd nd) m =
      if m = parent then insertBefore (childrenOf t parent) child node else childrenOf t m := by
  by_cases h2 : m = parent
  · subst h2
    rw [childrenOf_eq (get?_insertAtIn_parent hne), childrenOf_eq hpd, if_pos rfl]
  · by_cases h1 : m = node
    · subst h1
      rw [childrenOf_eq (get?_insertAtIn_self t parent _ child pd nd), childrenOf_eq hnd,
        if_neg h2]
    · rw [childrenOf_congr (get?_insertAtIn_other h1 h2), if_neg h2]

/--
PLAN §5.2 preservation。

`child` が parent の子であるという前提は要らない。
`insertBefore` は `child` が見つからなければ末尾に挿入するので、
その場合でも木の well-formedness は保たれるからである。
仕様の `notFoundError`（`insertAt` の前提条件 4）は invariant のためではなく、
仕様準拠のための検査である。
-/
theorem insertAtIn_preserves_wellformed (hwf : WellFormed t)
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd) (hnp : nd.parent = none)
    (hanc : ¬ InclusiveAncestor t node parent) :
    WellFormed (insertAtIn t parent node child pd nd) := by
  have hne : node ≠ parent := fun he => hanc (Or.inl he)
  have hnpar : parentOf t node = none := by simp [parentOf, hnd, hnp]
  have hnodemem : node ∉ pd.children := by
    intro hmem
    have : parentOf t node = some parent :=
      (mem_childrenOf_iff hwf node parent).mpr (by rw [childrenOf_eq hpd]; exact hmem)
    rw [hnpar] at this
    simp at this
  refine wellFormed_of ?_ ?_ ?_ ?_
  · intro c q
    rw [parentOf_insertAtIn hpd, childrenOf_insertAtIn hnd hpd hne]
    by_cases hcn : c = node
    · rw [if_pos hcn]
      by_cases hqp : q = parent
      · rw [if_pos hqp, mem_insertBefore]
        exact ⟨fun _ => Or.inl hcn, fun _ => by rw [hqp]⟩
      · rw [if_neg hqp]
        constructor
        · intro he; exact absurd (Option.some.inj he).symm hqp
        · intro hmem
          exfalso
          have hq := (mem_childrenOf_iff hwf c q).mpr hmem
          rw [hcn, hnpar] at hq
          simp at hq
    · rw [if_neg hcn]
      by_cases hqp : q = parent
      · rw [if_pos hqp, hqp, mem_insertBefore, ← mem_childrenOf_iff hwf]
        exact ⟨fun h => Or.inr h, fun h => h.resolve_left hcn⟩
      · rw [if_neg hqp, ← mem_childrenOf_iff hwf]
  · intro m dm hm
    rw [get?_insertAtIn] at hm
    by_cases h1 : m = node
    · rw [if_pos h1] at hm
      cases hm
      show nd.children.Nodup
      exact hwf.children_nodup _ _ hnd
    · rw [if_neg h1] at hm
      by_cases h2 : m = parent
      · rw [if_pos h2] at hm
        cases hm
        show (insertBefore pd.children child node).Nodup
        exact nodup_insertBefore child (hwf.children_nodup _ _ hpd) hnodemem
      · rw [if_neg h2] at hm
        exact hwf.children_nodup m dm hm
  · intro m hm
    have hnodep : parentOf (insertAtIn t parent node child pd nd) node = some parent := by
      rw [parentOf_insertAtIn hpd, if_pos rfl]
    have hother : ∀ x, x ≠ node →
        parentOf (insertAtIn t parent node child pd nd) x = parentOf t x := by
      intro x hx
      rw [parentOf_insertAtIn hpd, if_neg hx]
    rcases ancestor_of_parentOf_insert hnodep hother hm with hmm | ⟨h1, h2⟩
    · exact hwf.acyclic m hmm
    · exact hanc (h1.trans_inclusive h2)
  · refine ownerDocument_is_document_of hwf ?_ ?_
    · intro m dm hm
      rw [get?_insertAtIn] at hm
      by_cases h1 : m = node
      · rw [if_pos h1] at hm; cases hm; exact ⟨nd, by rw [← h1] at hnd; exact hnd, rfl⟩
      · rw [if_neg h1] at hm
        by_cases h2 : m = parent
        · rw [if_pos h2] at hm; cases hm; exact ⟨pd, by rw [← h2] at hpd; exact hpd, rfl⟩
        · rw [if_neg h2] at hm; exact ⟨dm, hm, rfl⟩
    · intro m d₀ hm
      rw [get?_insertAtIn]
      by_cases h1 : m = node
      · rw [if_pos h1]
        rw [h1, hnd] at hm
        cases hm
        simp
      · rw [if_neg h1]
        by_cases h2 : m = parent
        · rw [if_pos h2]
          rw [h2, hpd] at hm
          cases hm
          simp
        · rw [if_neg h2]; exact ⟨d₀, hm, rfl⟩

end Insert

/-! ### `insertAt` に持ち上げる -/

theorem insertAt_preserves_wellformed {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (h : insertAt t parent node child = .ok t') :
    WellFormed t' := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  refine insertAtIn_preserves_wellformed hwf hpd hnd hnp ?_
  intro hcon
  rw [← isInclusiveAncestorOf_iff hwf] at hcon
  rw [hanc] at hcon
  simp at hcon

/-- PLAN §5.2 effect。insert した node の parent は指定した parent になる。 -/
theorem insertAt_parentOf {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') : parentOf t' node = some parent := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  rw [parentOf_insertAtIn hpd, if_pos rfl]

/-- PLAN §5.2 effect。parent の children は `child` の直前に node を入れたものになる。 -/
theorem insertAt_childrenOf {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : insertAt t parent node child = .ok t') :
    childrenOf t' parent = insertBefore (childrenOf t parent) child node := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  have hne : node ≠ parent := by
    intro he
    have : isInclusiveAncestorOf t node parent = true :=
      (isInclusiveAncestorOf_iff hwf node parent).mpr (Or.inl he)
    rw [hanc] at this
    simp at this
  rw [childrenOf_insertAtIn hnd hpd hne, if_pos rfl]

/-- insert した node は、指定した child のちょうど直前に入る。 -/
theorem insertAt_children_split {t t' : Tree} {parent node c : NodeId}
    (hwf : WellFormed t) (h : insertAt t parent node (some c) = .ok t') :
    ∃ s₁ s₂, childrenOf t parent = s₁ ++ c :: s₂ ∧
      childrenOf t' parent = s₁ ++ node :: c :: s₂ := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, ht⟩ := insertAt_ok_cases h
  have hcmem : c ∈ childrenOf t parent := by
    rw [childrenOf_eq hpd]; exact hchild c rfl
  obtain ⟨s₁, s₂, h₁, h₂⟩ := insertBeforeFirst_eq_of_mem (l := childrenOf t parent) node hcmem
  refine ⟨s₁, s₂, h₁, ?_⟩
  rw [insertAt_childrenOf hwf h, insertBefore_some, h₂]

/-- well-formed な木では children に重複が無い。 -/
theorem childrenOf_nodup {t : Tree} (hwf : WellFormed t) (n : NodeId) :
    (childrenOf t n).Nodup := by
  unfold childrenOf
  split
  · simp
  · next d hd => exact hwf.children_nodup n d hd

/-- `insertAt` は parent 以外の children を変えない。 -/
theorem insertAt_childrenOf_ne {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : insertAt t parent node child = .ok t') {m : NodeId}
    (hm : m ≠ parent) : childrenOf t' m = childrenOf t m := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  have hne : node ≠ parent := by
    intro he
    have : isInclusiveAncestorOf t node parent = true :=
      (isInclusiveAncestorOf_iff hwf node parent).mpr (Or.inl he)
    rw [hanc] at this
    simp at this
  rw [childrenOf_insertAtIn hnd hpd hne, if_neg hm]

/--
`insertAt` は parent の children のどこか一箇所に node を挿す。

`child` が `none` かどうかで場合分けせずに扱えるので、
children の列に関する証明はこの形を使う。
-/
theorem insertAt_children_split_general {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (h : insertAt t parent node child = .ok t') :
    ∃ A B, childrenOf t parent = A ++ B ∧ childrenOf t' parent = A ++ node :: B := by
  cases child with
  | none =>
    refine ⟨childrenOf t parent, [], by simp, ?_⟩
    rw [insertAt_childrenOf hwf h, insertBefore_none]
  | some c =>
    obtain ⟨s₁, s₂, h₁, h₂⟩ := insertAt_children_split hwf h
    exact ⟨s₁, c :: s₂, h₁, h₂⟩

/-- `insertAt` する node は、まだ parent の children に入っていない。 -/
theorem insertAt_node_not_mem {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : insertAt t parent node child = .ok t') :
    node ∉ childrenOf t parent := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  intro hmem
  have : parentOf t node = some parent := (mem_childrenOf_iff hwf node parent).mpr hmem
  simp [parentOf, hnd, hnp] at this

/-- PLAN §5.2 frame。insert した node と parent 以外は変わらない。 -/
theorem insertAt_frame {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') {m : NodeId}
    (h1 : m ≠ node) (h2 : m ≠ parent) : t'.get? m = t.get? m := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  exact get?_insertAtIn_other h1 h2

/-! ## setOwnerDocument -/

section Adopt

variable {t : Tree} {n doc : NodeId}

theorem get?_setOwnerDocument_of_mem {m : NodeId} {d : NodeData}
    (hm : m ∈ preorder t n) (hd : t.get? m = some d) :
    (setOwnerDocument t n doc).get? m = some { d with ownerDocument := doc } := by
  rw [get?_setOwnerDocument, hd]
  simp [hm]

/-- PLAN §5.2 frame。inclusive descendant でない node は変わらない。 -/
theorem get?_setOwnerDocument_of_not_mem {m : NodeId} (hm : m ∉ preorder t n) :
    (setOwnerDocument t n doc).get? m = t.get? m := by
  rw [get?_setOwnerDocument]
  cases t.get? m with
  | none => rfl
  | some d => simp [hm]

/-- 木の形は変わらない。 -/
theorem parentOf_setOwnerDocument (t : Tree) (n doc m : NodeId) :
    parentOf (setOwnerDocument t n doc) m = parentOf t m := by
  unfold parentOf
  rw [get?_setOwnerDocument]
  cases t.get? m with
  | none => rfl
  | some d => by_cases hm : m ∈ preorder t n <;> simp [hm]

theorem childrenOf_setOwnerDocument (t : Tree) (n doc m : NodeId) :
    childrenOf (setOwnerDocument t n doc) m = childrenOf t m := by
  unfold childrenOf
  rw [get?_setOwnerDocument]
  cases t.get? m with
  | none => rfl
  | some d => by_cases hm : m ∈ preorder t n <;> simp [hm]

theorem ancestor_setOwnerDocument {a b : NodeId} :
    Ancestor (setOwnerDocument t n doc) a b ↔ Ancestor t a b := by
  constructor
  · exact ancestor_of_parentOf_subset fun x y hxy => by
      rw [← parentOf_setOwnerDocument t n doc x]; exact hxy
  · exact ancestor_of_parentOf_subset fun x y hxy => by
      rw [parentOf_setOwnerDocument t n doc x]; exact hxy

theorem exists_get?_setOwnerDocument {m : NodeId} {d₀ : NodeData} (h : t.get? m = some d₀) :
    ∃ d, (setOwnerDocument t n doc).get? m = some d ∧ d.kind = d₀.kind := by
  rw [get?_setOwnerDocument, h]
  by_cases hm : m ∈ preorder t n <;> simp [hm]

/-- PLAN §5.2 preservation。付け替え先が document node であることが前提になる。 -/
theorem setOwnerDocument_preserves_wellformed (hwf : WellFormed t) {dd : NodeData}
    (hdoc : t.get? doc = some dd) (hkind : dd.kind = .document) :
    WellFormed (setOwnerDocument t n doc) := by
  refine wellFormed_of ?_ ?_ ?_ ?_
  · intro c q
    rw [parentOf_setOwnerDocument, childrenOf_setOwnerDocument]
    exact mem_childrenOf_iff hwf c q
  · intro m dm hm
    rw [get?_setOwnerDocument] at hm
    cases h₀ : t.get? m with
    | none => rw [h₀] at hm; simp at hm
    | some d₀ =>
      rw [h₀] at hm
      by_cases hmem : m ∈ preorder t n
      · simp only [Option.map_some, if_pos hmem] at hm
        cases hm
        show d₀.children.Nodup
        exact hwf.children_nodup m d₀ h₀
      · simp only [Option.map_some, if_neg hmem] at hm
        cases hm
        exact hwf.children_nodup m _ h₀
  · intro m hm
    exact hwf.acyclic m (ancestor_setOwnerDocument.mp hm)
  · intro m dm hm
    rw [get?_setOwnerDocument] at hm
    cases h₀ : t.get? m with
    | none => rw [h₀] at hm; simp at hm
    | some d₀ =>
      rw [h₀] at hm
      by_cases hmem : m ∈ preorder t n
      · simp only [Option.map_some, if_pos hmem] at hm
        cases hm
        obtain ⟨dd', hdd', hk⟩ := exists_get?_setOwnerDocument (n := n) (doc := doc) hdoc
        exact ⟨dd', hdd', by rw [hk, hkind]⟩
      · simp only [Option.map_some, if_neg hmem] at hm
        cases hm
        obtain ⟨dd₁, hdd₁, hk₁⟩ := hwf.ownerDocument_is_document m _ h₀
        obtain ⟨dd', hdd', hk⟩ := exists_get?_setOwnerDocument (n := n) (doc := doc) hdd₁
        exact ⟨dd', hdd', by rw [hk, hk₁]⟩

/-- PLAN §5.2 effect。inclusive descendant の node document は `doc` になる。 -/
theorem ownerDocumentOf_setOwnerDocument (hwf : WellFormed t) {dn : NodeData}
    (hn : t.get? n = some dn) {m : NodeId} (hm : InclusiveDescendant t m n)
    (hmd : (t.get? m).isSome) :
    ownerDocumentOf (setOwnerDocument t n doc) m = some doc := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hmd
  rw [ownerDocumentOf,
    get?_setOwnerDocument_of_mem ((mem_preorder_iff hwf hn m).mpr hm) hd]
  rfl

end Adopt

/-! ## detach と ancestor 関係 -/

theorem parentOf_detach {t t' : Tree} {n : NodeId} (hd : detach t n = .ok t') (m : NodeId) :
    parentOf t' m = if m = n then none else parentOf t m := by
  rcases detach_ok_cases hd with ⟨d, hdd, hdp, rfl⟩ | ⟨d, p, pd, hdd, hdp, hpd, rfl⟩
  · by_cases hm : m = n
    · rw [if_pos hm, hm]; simp [parentOf, hdd, hdp]
    · rw [if_neg hm]
  · exact parentOf_detachFrom hpd m

/--
`detach` が外す辺が経路上に無ければ、ancestor 関係は残る。

`n` の親への辺だけが消えるので、`x` から `a` へ登る経路がその辺を通らなければよい。
経路がその辺を通るのは「`n` が `x` の inclusive ancestor」かつ「`a` が `n` の ancestor」のときである。
-/
theorem ancestor_detach_of_not_below {t t' : Tree} {n a : NodeId}
    (hd : detach t n = .ok t') {x : NodeId} (h : Ancestor t a x) :
    ¬ (InclusiveAncestor t n x ∧ Ancestor t a n) → Ancestor t' a x := by
  induction h with
  | @step m hp =>
    intro hnot
    have hmn : m ≠ n := by
      intro he
      exact hnot ⟨Or.inl he.symm, by rw [← he]; exact Ancestor.step hp⟩
    refine Ancestor.step ?_
    rw [parentOf_detach hd, if_neg hmn]
    exact hp
  | @trans m b hp hprev ih =>
    -- hp : parentOf t b = some m（b が下、m がその parent）
    intro hnot
    have hbn : b ≠ n := by
      intro he
      exact hnot ⟨Or.inl he.symm, by rw [← he]; exact Ancestor.trans hp hprev⟩
    refine Ancestor.trans (by rw [parentOf_detach hd, if_neg hbn]; exact hp) (ih ?_)
    rintro ⟨hnm, han⟩
    refine hnot ⟨?_, han⟩
    rcases hnm with he | ha
    · exact Or.inr (by rw [← he] at hp; exact Ancestor.step hp)
    · exact Or.inr (ha.trans_ancestor (Ancestor.step hp))

theorem inclusiveAncestor_detach_of_not_below {t t' : Tree} {n r x : NodeId}
    (hd : detach t n = .ok t') (h : InclusiveAncestor t r x)
    (hnot : ¬ (InclusiveAncestor t n x ∧ Ancestor t r n)) : InclusiveAncestor t' r x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (ancestor_detach_of_not_below hd h hnot)


end Dom
