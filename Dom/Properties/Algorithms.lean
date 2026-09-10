import Dom.Mutation.Algorithms
import Dom.Mutation.Api
import Dom.Properties.Mutation

/-!
# Phase 3 の theorem

PLAN §6.3 に挙げた性質を証明する。

1. 各 algorithm の preservation
2. `ensurePreInsertionValidity` が `.ok` を返すなら `insertAt` の前提条件が成り立つ
3. `insert` の後、node は parent の `children` において child の直前にある
4. `remove` の後、node は parent を持たず、旧 parent の `children` に現れない
5. 既存 node の `insert` と `remove` ∘ `insert` の同値、および `move` との一致

定義側（`Dom/Mutation/Algorithms.lean`）と分けてあるので、
定義の変更が証明の再 build に波及する範囲を限定できる（PLAN §2.2）。
-/

namespace Dom

/-! ## kind を変えない変更 -/

/-- 木の変更が node の kind を変えないこと。`adopt` の前提を持ち回るのに使う。 -/
def KindPreserving (t t' : Tree) : Prop :=
  ∀ m, (t'.get? m).map (·.kind) = (t.get? m).map (·.kind)

/-- `doc` が document node として木にあること。DOM Standard §4.5 adopt の前提。 -/
def IsDocument (t : Tree) (doc : NodeId) : Prop :=
  ∃ dd, t.get? doc = some dd ∧ dd.kind = .document

namespace KindPreserving

theorem refl (t : Tree) : KindPreserving t t := fun _ => rfl

theorem trans {t t₁ t₂ : Tree} (h₁ : KindPreserving t t₁) (h₂ : KindPreserving t₁ t₂) :
    KindPreserving t t₂ := fun m => (h₂ m).trans (h₁ m)

end KindPreserving

theorem IsDocument.map {t t' : Tree} {doc : NodeId} (h : KindPreserving t t')
    (hd : IsDocument t doc) : IsDocument t' doc := by
  obtain ⟨dd, hdd, hk⟩ := hd
  have hm := h doc
  rw [hdd] at hm
  cases hd' : t'.get? doc with
  | none => rw [hd'] at hm; simp at hm
  | some dd' =>
    rw [hd'] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    exact ⟨dd', hd', by rw [hm, hk]⟩

/-- well-formed な木では、どの node の node document も document node である。 -/
theorem isDocument_ownerDocument {t : Tree} (hwf : WellFormed t) {m : NodeId} {d : NodeData}
    (hm : t.get? m = some d) : IsDocument t d.ownerDocument :=
  hwf.ownerDocument_is_document m d hm

/-! ## primitive が kind を変えないこと -/

theorem kindPreserving_detach {t t' : Tree} {n : NodeId} (h : detach t n = .ok t') :
    KindPreserving t t' := by
  intro m
  rcases detach_ok_cases h with ⟨d, _, _, rfl⟩ | ⟨d, p, pd, hd, hp, hpd, rfl⟩
  · rfl
  · rw [get?_detachFrom]
    by_cases h1 : m = n
    · rw [if_pos h1, h1, hd]; rfl
    · rw [if_neg h1]
      by_cases h2 : m = p
      · rw [if_pos h2, h2, hpd]; rfl
      · rw [if_neg h2]

theorem kindPreserving_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') : KindPreserving t t' := by
  intro m
  obtain ⟨pd, nd, hpd, hnd, _, _, _, rfl⟩ := insertAt_ok_cases h
  rw [get?_insertAtIn]
  by_cases h1 : m = node
  · rw [if_pos h1, h1, hnd]; rfl
  · rw [if_neg h1]
    by_cases h2 : m = parent
    · rw [if_pos h2, h2, hpd]; rfl
    · rw [if_neg h2]

theorem kindPreserving_setOwnerDocument (t : Tree) (n doc : NodeId) :
    KindPreserving t (setOwnerDocument t n doc) := by
  intro m
  rw [get?_setOwnerDocument]
  cases t.get? m with
  | none => rfl
  | some d => by_cases hm : m ∈ preorder t n <;> simp [hm]

/-! ## hook は恒等関数である -/

@[simp] theorem liveRangePreRemove_eq (t : Tree) (n : NodeId) : liveRangePreRemove t n = t := rfl

@[simp] theorem iteratorPreRemove_eq (t : Tree) (n : NodeId) : iteratorPreRemove t n = t := rfl

@[simp] theorem liveRangeInsertAdjust_eq (t : Tree) (p : NodeId) (c : Option NodeId) (k : Nat) :
    liveRangeInsertAdjust t p c k = t := rfl

@[simp] theorem detachWithLiveAdjust_eq (t : Tree) (n : NodeId) :
    detachWithLiveAdjust t n = detach t n := rfl

/-! ## remove -/

theorem remove_eq_detach {t : Tree} {n p : NodeId} (h : parentOf t n = some p) :
    remove t n = detach t n := by
  simp [remove, h]

theorem remove_preserves_wellformed {t t' : Tree} {n : NodeId}
    (hwf : WellFormed t) (h : remove t n = .ok t') : WellFormed t' := by
  unfold remove at h
  split at h
  · simp at h
  · exact detach_preserves_wellformed hwf (by simpa using h)

theorem kindPreserving_remove {t t' : Tree} {n : NodeId} (h : remove t n = .ok t') :
    KindPreserving t t' := by
  unfold remove at h
  split at h
  · simp at h
  · exact kindPreserving_detach (by simpa using h)

/-- PLAN §6.3。`remove` した node は parent を持たない。 -/
theorem remove_parentOf {t t' : Tree} {n : NodeId} (h : remove t n = .ok t') :
    parentOf t' n = none := by
  unfold remove at h
  split at h
  · simp at h
  · exact detach_parentOf (by simpa using h)

/-- PLAN §6.3。`remove` の後、node は旧 parent の children に現れない。 -/
theorem remove_not_mem_childrenOf {t t' : Tree} {n p : NodeId}
    (hwf : WellFormed t) (hp : parentOf t n = some p) (h : remove t n = .ok t') :
    n ∉ childrenOf t' p := by
  rw [detach_childrenOf hwf hp (by rwa [← remove_eq_detach hp])]
  exact ListUtil.not_mem_removeAll _ _

theorem removeEach_preserves_wellformed :
    ∀ (ns : List NodeId) {t t' : Tree}, WellFormed t → removeEach t ns = .ok t' → WellFormed t'
  | [], _, _, hwf, h => by rw [removeEach] at h; cases h; exact hwf
  | n :: ns, t, t', hwf, h => by
    rw [removeEach] at h
    split at h
    · simp at h
    · next t₁ hr =>
      exact removeEach_preserves_wellformed ns (remove_preserves_wellformed hwf hr) h

theorem kindPreserving_removeEach :
    ∀ (ns : List NodeId) {t t' : Tree}, removeEach t ns = .ok t' → KindPreserving t t'
  | [], _, _, h => by rw [removeEach] at h; cases h; exact KindPreserving.refl _
  | n :: ns, t, t', h => by
    rw [removeEach] at h
    split at h
    · simp at h
    · next t₁ hr =>
      exact (kindPreserving_remove hr).trans (kindPreserving_removeEach ns h)

/-! ## adopt -/

theorem adopt_preserves_wellformed {t t' : Tree} {node doc : NodeId}
    (hwf : WellFormed t) (hdoc : IsDocument t doc) (h : adopt t node doc = .ok t') :
    WellFormed t' := by
  unfold adopt at h
  split at h
  · simp at h
  · next oldDocument _ =>
    split at h
    · simp at h
    · next t₁ hr =>
      have hwf₁ : WellFormed t₁ := by
        revert hr; split
        · intro hr; cases hr; exact hwf
        · intro hr; exact remove_preserves_wellformed hwf (by simpa using hr)
      have hkp : KindPreserving t t₁ := by
        revert hr; split
        · intro hr; cases hr; exact KindPreserving.refl _
        · intro hr; exact kindPreserving_remove (by simpa using hr)
      split at h
      · cases h; exact hwf₁
      · cases h
        obtain ⟨dd, hdd, hk⟩ := hdoc.map hkp
        exact setOwnerDocument_preserves_wellformed hwf₁ hdd hk

theorem kindPreserving_adopt {t t' : Tree} {node doc : NodeId} (h : adopt t node doc = .ok t') :
    KindPreserving t t' := by
  unfold adopt at h
  split at h
  · simp at h
  · next oldDocument _ =>
    split at h
    · simp at h
    · next t₁ hr =>
      have hkp : KindPreserving t t₁ := by
        revert hr; split
        · intro hr; cases hr; exact KindPreserving.refl _
        · intro hr; exact kindPreserving_remove (by simpa using hr)
      split at h
      · cases h; exact hkp
      · cases h; exact hkp.trans (kindPreserving_setOwnerDocument _ _ _)

/-! ## insert -/

theorem insertEach_preserves_wellformed :
    ∀ (ns : List NodeId) {t t' : Tree} {parent : NodeId} {child : Option NodeId} {doc : NodeId},
      WellFormed t → IsDocument t doc → insertEach t parent child doc ns = .ok t' →
      WellFormed t'
  | [], _, _, _, _, _, hwf, _, h => by rw [insertEach] at h; cases h; exact hwf
  | n :: ns, t, t', parent, child, doc, hwf, hdoc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next t₁ ha =>
      have hwf₁ := adopt_preserves_wellformed hwf hdoc ha
      have hdoc₁ := hdoc.map (kindPreserving_adopt ha)
      split at h
      · simp at h
      · next t₂ hi =>
        exact insertEach_preserves_wellformed ns (insertAt_preserves_wellformed hwf₁ hi)
          (hdoc₁.map (kindPreserving_insertAt hi)) h

theorem kindPreserving_insertEach :
    ∀ (ns : List NodeId) {t t' : Tree} {parent : NodeId} {child : Option NodeId} {doc : NodeId},
      insertEach t parent child doc ns = .ok t' → KindPreserving t t'
  | [], _, _, _, _, _, h => by rw [insertEach] at h; cases h; exact KindPreserving.refl _
  | n :: ns, t, t', parent, child, doc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next t₁ ha =>
      split at h
      · simp at h
      · next t₂ hi =>
        exact (kindPreserving_adopt ha).trans
          ((kindPreserving_insertAt hi).trans (kindPreserving_insertEach ns h))

theorem insertEachAt_preserves_wellformed {t t' : Tree} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId}
    (hwf : WellFormed t) (h : insertEachAt t parent child nodes = .ok t') : WellFormed t' := by
  unfold insertEachAt at h
  split at h
  · simp at h
  · next pd hpd =>
    exact insertEach_preserves_wellformed _ hwf (isDocument_ownerDocument hwf hpd) h

theorem kindPreserving_insertEachAt {t t' : Tree} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} (h : insertEachAt t parent child nodes = .ok t') :
    KindPreserving t t' := by
  unfold insertEachAt at h
  split at h
  · simp at h
  · exact kindPreserving_insertEach _ h

theorem insertNodesAt_preserves_wellformed {t t' : Tree} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId}
    (hwf : WellFormed t) (h : insertNodesAt t parent child nodes = .ok t') : WellFormed t' := by
  unfold insertNodesAt at h
  rw [liveRangeInsertAdjust_eq] at h
  exact insertEachAt_preserves_wellformed hwf h

theorem kindPreserving_insertNodesAt {t t' : Tree} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} (h : insertNodesAt t parent child nodes = .ok t') :
    KindPreserving t t' := by
  unfold insertNodesAt at h
  rw [liveRangeInsertAdjust_eq] at h
  exact kindPreserving_insertEachAt h

/-- PLAN §6.3。`insert` は well-formedness を保つ。 -/
theorem insert_preserves_wellformed {t t' : Tree} {node parent : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : insert t node parent child = .ok t') : WellFormed t' := by
  unfold insert at h
  split at h
  · simp at h
  · next nd hnd =>
    split at h
    · split at h
      · rw [← Except.ok.inj h]; exact hwf
      · split at h
        · simp at h
        · next t₁ hr =>
          exact insertNodesAt_preserves_wellformed (removeEach_preserves_wellformed _ hwf hr) h
    · exact insertNodesAt_preserves_wellformed hwf h

theorem kindPreserving_insert {t t' : Tree} {node parent : NodeId} {child : Option NodeId}
    (h : insert t node parent child = .ok t') : KindPreserving t t' := by
  unfold insert at h
  split at h
  · simp at h
  · next nd hnd =>
    split at h
    · split at h
      · rw [← Except.ok.inj h]; exact KindPreserving.refl _
      · split at h
        · simp at h
        · next t₁ hr =>
          exact (kindPreserving_removeEach _ hr).trans (kindPreserving_insertNodesAt h)
    · exact kindPreserving_insertNodesAt h

/-! ## 残りの algorithm の preservation -/

theorem preInsert_preserves_wellformed {t t' : Tree} {node parent : NodeId}
    {child : Option NodeId} (hwf : WellFormed t) (h : preInsert t node parent child = .ok t') :
    WellFormed t' := by
  unfold preInsert at h
  split at h
  · simp at h
  · exact insert_preserves_wellformed hwf h

theorem append_preserves_wellformed {t t' : Tree} {node parent : NodeId}
    (hwf : WellFormed t) (h : append t node parent = .ok t') : WellFormed t' :=
  preInsert_preserves_wellformed hwf h

theorem preRemove_preserves_wellformed {t t' : Tree} {child parent : NodeId}
    (hwf : WellFormed t) (h : preRemove t child parent = .ok t') : WellFormed t' := by
  unfold preRemove at h
  split at h
  · simp at h
  · exact remove_preserves_wellformed hwf h

theorem replace_preserves_wellformed {t t' : Tree} {child node parent : NodeId}
    (hwf : WellFormed t) (h : replace t child node parent = .ok t') : WellFormed t' := by
  unfold replace at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next pd hpd =>
      split at h
      · simp at h
      · next t₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        split at h
        · simp at h
        · next t₂ hr =>
          have hwf₂ : WellFormed t₂ := by
            revert hr; split
            · intro hr; cases hr; exact hwf₁
            · intro hr; exact remove_preserves_wellformed hwf₁ (by simpa using hr)
          exact insert_preserves_wellformed hwf₂ h

theorem replaceAll_preserves_wellformed {t t' : Tree} {node : Option NodeId} {parent : NodeId}
    (hwf : WellFormed t) (h : replaceAll t node parent = .ok t') : WellFormed t' := by
  unfold replaceAll at h
  split at h
  · simp at h
  · next t₁ hr =>
    have hwf₁ := removeEach_preserves_wellformed _ hwf hr
    split at h
    · cases h; exact hwf₁
    · exact insert_preserves_wellformed hwf₁ h

/-! ## move -/

/--
PLAN §6.2 / `memo.md` の `move_equivalent_to_remove_insert`（Phase 3 では木への射影）。

`move` の木への効果は、`remove` の後に `insertAt` した結果と一致する。
`move` は仕様どおり node document を付け替えないので、
`insert`（adopt を含む）ではなく primitive の `insertAt` との一致になる。

live range と NodeIterator の調整 hook は `remove` と共有しているので、
Phase 5 と 6 で hook に中身を入れてもこの一致は保たれる。
-/
theorem move_eq_remove_insertAt {t t' : Tree} {node newParent : NodeId} {child : Option NodeId}
    (h : move t node newParent child = .ok t') :
    ∃ t₁, remove t node = .ok t₁ ∧ insertAt t₁ newParent node child = .ok t' := by
  unfold move at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next p hp =>
      split at h
      · simp at h
      · next t₁ hd =>
        rw [liveRangeInsertAdjust_eq] at h
        exact ⟨t₁, by rw [remove, hp]; exact hd, h⟩

/-- PLAN §6.3。`move` は well-formedness を保つ。 -/
theorem move_preserves_wellformed {t t' : Tree} {node newParent : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : move t node newParent child = .ok t') : WellFormed t' := by
  obtain ⟨t₁, hr, hi⟩ := move_eq_remove_insertAt h
  exact insertAt_preserves_wellformed (remove_preserves_wellformed hwf hr) hi

/-- `move` した node の parent は指定した parent になる。 -/
theorem move_parentOf {t t' : Tree} {node newParent : NodeId} {child : Option NodeId}
    (h : move t node newParent child = .ok t') : parentOf t' node = some newParent := by
  obtain ⟨t₁, _, hi⟩ := move_eq_remove_insertAt h
  exact insertAt_parentOf hi

/-- `move` した node は、旧 parent の children から外れて新 parent の children に入る。 -/
theorem move_childrenOf {t t' : Tree} {node newParent : NodeId} {child : Option NodeId}
    (hwf : WellFormed t) (h : move t node newParent child = .ok t') :
    ∃ t₁, remove t node = .ok t₁ ∧
      childrenOf t' newParent = ListUtil.insertBefore (childrenOf t₁ newParent) child node := by
  obtain ⟨t₁, hr, hi⟩ := move_eq_remove_insertAt h
  refine ⟨t₁, hr, ?_⟩
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, _, rfl⟩ := insertAt_ok_cases hi
  have hne : node ≠ newParent := by
    intro he
    have : isInclusiveAncestorOf t₁ node newParent = true :=
      (isInclusiveAncestorOf_iff (remove_preserves_wellformed hwf hr) node newParent).mpr
        (Or.inl he)
    rw [hanc] at this
    simp at this
  rw [childrenOf_insertAtIn hnd hpd hne, if_pos rfl]

/-! ## ensure pre-insert validity -/

/-- `childHasParent` が真なら、`child` が指定されていればその parent は `parent` である。 -/
theorem parentOf_of_childHasParent {t : Tree} {child : Option NodeId} {parent : NodeId}
    (h : childHasParent t child parent = true) {c : NodeId} (hc : child = some c) :
    parentOf t c = some parent := by
  subst hc
  simpa [childHasParent] using h

/-- `ensurePreInsertionValidity` が通れば、step 1-3 が保証する事実が取り出せる。 -/
theorem ensurePreInsertionValidity_ok {t : Tree} {node parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    (∃ pd, t.get? parent = some pd) ∧ (∃ nd, t.get? node = some nd) ∧
      isInclusiveAncestorOf t node parent = false ∧
      ∀ c, child = some c → parentOf t c = some parent := by
  unfold ensurePreInsertionValidity at h
  split at h
  · simp at h
  · next pd hpd =>
    split at h
    · simp at h
    · next nd hnd =>
      split at h
      · simp at h
      · split at h
        · simp at h
        · next hanc =>
          split at h
          · simp at h
          · next hchild =>
            exact ⟨⟨pd, hpd⟩, ⟨nd, hnd⟩, by simpa using hanc,
              fun c hc => parentOf_of_childHasParent (by simpa using hchild) hc⟩

/--
PLAN §6.3。`ensurePreInsertionValidity` が `.ok` を返し、node が parent を持たないなら、
primitive の `insertAt` は必ず成功する。

「node が parent を持たない」は `insert` の中で `adopt` が保証する。
-/
theorem insertAt_isOk_of_validity {t : Tree} {node parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (hwf : WellFormed t)
    (hv : ensurePreInsertionValidity t node parent child excl = .ok ())
    (hnp : parentOf t node = none) : ∃ t', insertAt t parent node child = .ok t' := by
  obtain ⟨⟨pd, hpd⟩, ⟨nd, hnd⟩, hanc, hchild⟩ := ensurePreInsertionValidity_ok hv
  have hnp' : nd.parent = none := by
    rw [parentOf, hnd] at hnp; simpa using hnp
  refine ⟨_, insertAt_eq_ok hpd hnd hnp' hanc ?_⟩
  intro c hc
  have hmem := mem_childrenOf_of_parentOf hwf (hchild c hc)
  rwa [childrenOf_eq hpd] at hmem

/-! ## insert の効果 -/

/-- fragment でない node の `insert` は、adopt してから `insertAt` を呼ぶだけである。 -/
theorem insert_single {t t' : Tree} {node parent : NodeId} {child : Option NodeId}
    {nd : NodeData} (hnd : t.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert t node parent child = .ok t') :
    ∃ pd t₁, t.get? parent = some pd ∧ adopt t node pd.ownerDocument = .ok t₁ ∧
      insertAt t₁ parent node child = .ok t' := by
  unfold insert at h
  split at h
  · next hn => rw [hnd] at hn; simp at hn
  · next nd' hnd' =>
    rw [hnd] at hnd'
    cases hnd'
    split at h
    · next hf => exact absurd hf hk
    · unfold insertNodesAt insertEachAt at h
      rw [liveRangeInsertAdjust_eq] at h
      split at h
      · simp at h
      · next pd hpd =>
        rw [insertEach] at h
        split at h
        · simp at h
        · next t₁ ha =>
          split at h
          · simp at h
          · next t₂ hi =>
            rw [insertEach] at h
            exact ⟨pd, t₁, hpd, ha, by rw [hi, ← Except.ok.inj h]⟩

/--
PLAN §6.3。fragment でない node を `insert` すると、
node は parent の children において child のちょうど直前に来る。
-/
theorem insert_children_split {t t' : Tree} {node parent c : NodeId} {nd : NodeData}
    (hwf : WellFormed t) (hnd : t.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert t node parent (some c) = .ok t') :
    ∃ t₁, childrenOf t' parent = ListUtil.insertBefore (childrenOf t₁ parent) (some c) node ∧
      ∃ s₁ s₂, childrenOf t₁ parent = s₁ ++ c :: s₂ ∧
        childrenOf t' parent = s₁ ++ node :: c :: s₂ := by
  obtain ⟨pd, t₁, hpd, ha, hi⟩ := insert_single hnd hk h
  have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
  exact ⟨t₁, insertAt_childrenOf hwf₁ hi, insertAt_children_split hwf₁ hi⟩

/-- `insert` した node の parent は指定した parent になる。 -/
theorem insert_parentOf {t t' : Tree} {node parent : NodeId} {child : Option NodeId}
    {nd : NodeData} (hnd : t.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert t node parent child = .ok t') : parentOf t' node = some parent := by
  obtain ⟨pd, t₁, hpd, ha, hi⟩ := insert_single hnd hk h
  exact insertAt_parentOf hi

/-- parent を持つ node の `adopt` は `remove` を経由する。 -/
theorem adopt_of_parent_isSome {t t₁ : Tree} {node doc : NodeId}
    (hp : (parentOf t node).isSome) (h : adopt t node doc = .ok t₁) :
    ∃ t₀, remove t node = .ok t₀ ∧ (t₁ = t₀ ∨ t₁ = setOwnerDocument t₀ node doc) := by
  unfold adopt at h
  split at h
  · simp at h
  · next old hold =>
    split at h
    · simp at h
    · next t₀ hr =>
      have hr' : remove t node = .ok t₀ := by
        split at hr
        · next hn => rw [hn] at hp; simp at hp
        · exact hr
      split at h
      · exact ⟨t₀, hr', Or.inl (Except.ok.inj h).symm⟩
      · exact ⟨t₀, hr', Or.inr (Except.ok.inj h).symm⟩

/--
PLAN §6.3 / `memo.md` §9。既に parent を持つ node の `insert` は、必ず `remove` を経由する。

`adopt` が素の detach ではなく完全な `remove` を呼ぶので、
explicit な remove と move 中の implicit な removal が同じ経路を通る。
違いは node document の付け替えを挟むかどうかだけである。

`move_eq_remove_insertAt` と合わせると、
`move` も既存 node の `insert` も「`remove` してから `insertAt`」に分解できることが分かる。
-/
theorem insert_factors_through_remove {t t' : Tree} {node parent : NodeId}
    {child : Option NodeId} {nd : NodeData} (hnd : t.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (hp : (parentOf t node).isSome) (h : insert t node parent child = .ok t') :
    ∃ t₀ t₁, remove t node = .ok t₀ ∧
      (t₁ = t₀ ∨ ∃ doc, t₁ = setOwnerDocument t₀ node doc) ∧
      insertAt t₁ parent node child = .ok t' := by
  obtain ⟨pd, t₁, hpd, ha, hi⟩ := insert_single hnd hk h
  obtain ⟨t₀, hr, hcase⟩ := adopt_of_parent_isSome hp ha
  refine ⟨t₀, t₁, hr, ?_, hi⟩
  rcases hcase with he | he
  · exact Or.inl he
  · exact Or.inr ⟨pd.ownerDocument, he⟩

/-! ## public API の preservation -/

/--
PLAN §6.1。public API はすべて §4.2.3 の algorithm を経由するので、
well-formedness の保存は algorithm 側の定理から直ちに従う。

この構造が「どの API から始めても live object の調整が迂回されない」ことの土台になる
（`memo.md` §7）。Phase 5 と 6 で hook に中身を入れたときも、
API ごとに証明をやり直す必要はない。
-/
theorem appendChild_preserves_wellformed {t t' : Tree} {parent node : NodeId}
    (hwf : WellFormed t) (h : appendChild t parent node = .ok t') : WellFormed t' :=
  append_preserves_wellformed hwf h

theorem insertBefore_preserves_wellformed {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t)
    (h : insertBefore t parent node child = .ok t') : WellFormed t' :=
  preInsert_preserves_wellformed hwf h

theorem replaceChild_preserves_wellformed {t t' : Tree} {parent node child : NodeId}
    (hwf : WellFormed t) (h : replaceChild t parent node child = .ok t') : WellFormed t' :=
  replace_preserves_wellformed hwf h

theorem removeChild_preserves_wellformed {t t' : Tree} {parent child : NodeId}
    (hwf : WellFormed t) (h : removeChild t parent child = .ok t') : WellFormed t' :=
  preRemove_preserves_wellformed hwf h

theorem replaceChildren_preserves_wellformed {t t' : Tree} {parent : NodeId}
    {node : Option NodeId} (hwf : WellFormed t)
    (h : replaceChildren t parent node = .ok t') : WellFormed t' := by
  unfold replaceChildren at h
  split at h
  · exact replaceAll_preserves_wellformed hwf h
  · split at h
    · simp at h
    · exact replaceAll_preserves_wellformed hwf h

theorem before_preserves_wellformed {t t' : Tree} {this node : NodeId}
    (hwf : WellFormed t) (h : before t this node = .ok t') : WellFormed t' := by
  unfold before at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact preInsert_preserves_wellformed hwf h

theorem after_preserves_wellformed {t t' : Tree} {this node : NodeId}
    (hwf : WellFormed t) (h : after t this node = .ok t') : WellFormed t' := by
  unfold after at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact preInsert_preserves_wellformed hwf h

theorem replaceWith_preserves_wellformed {t t' : Tree} {this node : NodeId}
    (hwf : WellFormed t) (h : replaceWith t this node = .ok t') : WellFormed t' := by
  unfold replaceWith at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · next parent hpar =>
    rw [if_pos hpar] at h
    exact replace_preserves_wellformed hwf h

theorem nodeRemove_preserves_wellformed {t t' : Tree} {this : NodeId}
    (hwf : WellFormed t) (h : nodeRemove t this = .ok t') : WellFormed t' := by
  unfold nodeRemove at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact remove_preserves_wellformed hwf h

theorem moveBefore_preserves_wellformed {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed t)
    (h : moveBefore t parent node child = .ok t') : WellFormed t' :=
  move_preserves_wellformed hwf h

/-- `moveBefore` も `remove` してから `insertAt` する形に分解できる。 -/
theorem moveBefore_eq_remove_insertAt {t t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (h : moveBefore t parent node child = .ok t') :
    ∃ t₁ ref, remove t node = .ok t₁ ∧ insertAt t₁ parent node ref = .ok t' := by
  obtain ⟨t₁, hr, hi⟩ := move_eq_remove_insertAt h
  exact ⟨t₁, _, hr, hi⟩

end Dom
