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

/-! ## kind と attribute を変えない変更 -/

/--
木の変更が node の kind と attribute list を変えないこと。

§4.2.3 の algorithm は parent・children・node document しか動かさないので、
どれもこれを満たす。`adopt` の前提を持ち回るのと、
attribute の妥当性を運ぶのに使う。
-/
def ShapePreserving (t t' : Tree) : Prop :=
  ∀ m, (t'.get? m).map NodeData.shape = (t.get? m).map NodeData.shape

/-- `doc` が document node として木にあること。DOM Standard §4.5 adopt の前提。 -/
def IsDocument (t : Tree) (doc : NodeId) : Prop :=
  ∃ dd, t.get? doc = some dd ∧ dd.kind = .document

namespace ShapePreserving

theorem refl (t : Tree) : ShapePreserving t t := fun _ => rfl

theorem trans {t t₁ t₂ : Tree} (h₁ : ShapePreserving t t₁) (h₂ : ShapePreserving t₁ t₂) :
    ShapePreserving t t₂ := fun m => (h₂ m).trans (h₁ m)

theorem map_shape_fst (o : Option NodeData) :
    o.map (·.kind) = (o.map NodeData.shape).map Prod.fst := by cases o <;> rfl

theorem map_shape_snd (o : Option NodeData) :
    o.map (·.attributes) = (o.map NodeData.shape).map Prod.snd := by cases o <;> rfl

/-- kind だけを取り出す。 -/
theorem kind {t t' : Tree} (h : ShapePreserving t t') (m : NodeId) :
    (t'.get? m).map (·.kind) = (t.get? m).map (·.kind) := by
  rw [map_shape_fst, map_shape_fst, h m]

/-- attribute list だけを取り出す。 -/
theorem attributes {t t' : Tree} (h : ShapePreserving t t') (m : NodeId) :
    (t'.get? m).map (·.attributes) = (t.get? m).map (·.attributes) := by
  rw [map_shape_snd, map_shape_snd, h m]

/-- 変更後に node があるなら変更前にもあり、kind と attribute list は同じである。 -/
theorem exists_get? {t t' : Tree} (h : ShapePreserving t t') {m : NodeId} {d : NodeData}
    (hd : t'.get? m = some d) :
    ∃ d₀, t.get? m = some d₀ ∧ d₀.kind = d.kind ∧ d₀.attributes = d.attributes := by
  have hm := h m
  rw [hd] at hm
  cases hd₀ : t.get? m with
  | none => rw [hd₀] at hm; simp at hm
  | some d₀ =>
    rw [hd₀] at hm
    simp only [Option.map_some, Option.some.injEq, NodeData.shape, Prod.mk.injEq] at hm
    exact ⟨d₀, rfl, hm.1.symm, hm.2.symm⟩

end ShapePreserving

theorem IsDocument.map {t t' : Tree} {doc : NodeId} (h : ShapePreserving t t')
    (hd : IsDocument t doc) : IsDocument t' doc := by
  obtain ⟨dd, hdd, hk⟩ := hd
  have hm := h.kind doc
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

theorem shapePreserving_detach {t t' : Tree} {n : NodeId} (h : detach t n = .ok t') :
    ShapePreserving t t' := by
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

theorem shapePreserving_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') : ShapePreserving t t' := by
  intro m
  obtain ⟨pd, nd, hpd, hnd, _, _, _, rfl⟩ := insertAt_ok_cases h
  rw [get?_insertAtIn]
  by_cases h1 : m = node
  · rw [if_pos h1, h1, hnd]; rfl
  · rw [if_neg h1]
    by_cases h2 : m = parent
    · rw [if_pos h2, h2, hpd]; rfl
    · rw [if_neg h2]

theorem shapePreserving_setOwnerDocument (t : Tree) (n doc : NodeId) :
    ShapePreserving t (setOwnerDocument t n doc) := by
  intro m
  rw [get?_setOwnerDocument]
  cases t.get? m with
  | none => rfl
  | some d => by_cases hm : m ∈ preorder t n <;> simp [hm, NodeData.shape]

/-! ## remove -/

theorem detachWithLiveAdjust_tree {s s' : DOMState} {n : NodeId}
    (h : detachWithLiveAdjust s n = .ok s') : detach s.tree n = .ok s'.tree := by
  unfold detachWithLiveAdjust at h
  have := (DOMState.mapTree_eq_ok h).1
  simpa using this

/--
`remove` が成功したなら parent があり、木の効果は `detach` と同じである。

mutation record を積む step（20-21）は木を変えないので、
`suppressObservers` の値に依らず成り立つ。
-/
theorem remove_ok {s s' : DOMState} {n : NodeId} {b : Bool} (h : remove s n b = .ok s') :
    (∃ p, parentOf s.tree n = some p) ∧ detach s.tree n = .ok s'.tree := by
  unfold remove at h
  split at h
  · simp at h
  · next p hp =>
    simp only at h
    split at h
    · simp at h
    · next s₁ hd =>
      refine ⟨⟨p, hp⟩, ?_⟩
      have htree : s'.tree = s₁.tree := by
        split at h
        · rw [← Except.ok.inj h]; simp
        · rw [← Except.ok.inj h]; simp
      rw [htree]
      exact detachWithLiveAdjust_tree hd

theorem remove_preserves_wellformed {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : remove s n b = .ok s') : WellFormed s'.tree :=
  detach_preserves_wellformed hwf (remove_ok h).2

theorem shapePreserving_remove {s s' : DOMState} {n : NodeId} {b : Bool} (h : remove s n b = .ok s') :
    ShapePreserving s.tree s'.tree :=
  shapePreserving_detach (remove_ok h).2

/-- PLAN §6.3。`remove` した node は parent を持たない。 -/
theorem remove_parentOf {s s' : DOMState} {n : NodeId} {b : Bool} (h : remove s n b = .ok s') :
    parentOf s'.tree n = none :=
  detach_parentOf (remove_ok h).2

/-- PLAN §6.3。`remove` の後、node は旧 parent の children に現れない。 -/
theorem remove_not_mem_childrenOf {s s' : DOMState} {n p : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (hp : parentOf s.tree n = some p) (h : remove s n b = .ok s') :
    n ∉ childrenOf s'.tree p := by
  rw [detach_childrenOf hwf hp (remove_ok h).2]
  exact ListUtil.not_mem_removeAll _ _

theorem removeEach_preserves_wellformed :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool}, WellFormed s.tree →
      removeEach s ns b = .ok s' → WellFormed s'.tree
  | [], _, _, _, hwf, h => by
    simp only [removeEach] at h; rw [← Except.ok.inj h]; exact hwf
  | n :: ns, s, s', b, hwf, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      exact removeEach_preserves_wellformed ns (remove_preserves_wellformed hwf hr) h

theorem shapePreserving_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool}, removeEach s ns b = .ok s' →
      ShapePreserving s.tree s'.tree
  | [], _, _, _, h => by
    simp only [removeEach] at h; rw [← Except.ok.inj h]; exact ShapePreserving.refl _
  | n :: ns, s, s', b, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      exact (shapePreserving_remove hr).trans (shapePreserving_removeEach ns h)

/-! ## adopt -/

/-- `adopt` の中で `remove` が呼ばれたかどうかで場合分けする。 -/
theorem adopt_ok_cases {s s' : DOMState} {node doc : NodeId} (h : adopt s node doc = .ok s') :
    ∃ s₁, (parentOf s.tree node = none ∧ s₁ = s ∨ remove s node = .ok s₁) ∧
      (s' = s₁ ∨ s' = s₁.withTree (setOwnerDocument s₁.tree node doc)) := by
  unfold adopt at h
  split at h
  · simp at h
  · next old hold =>
    split at h
    · simp at h
    · next s₁ hr =>
      refine ⟨s₁, ?_, ?_⟩
      · revert hr
        split
        · next hn => intro hr; exact Or.inl ⟨hn, (Except.ok.inj hr).symm⟩
        · next p hn => intro hr; exact Or.inr hr
      · split at h
        · exact Or.inl (Except.ok.inj h).symm
        · exact Or.inr (Except.ok.inj h).symm

theorem adopt_preserves_wellformed {s s' : DOMState} {node doc : NodeId}
    (hwf : WellFormed s.tree) (hdoc : IsDocument s.tree doc) (h : adopt s node doc = .ok s') :
    WellFormed s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have hwf₁ : WellFormed s₁.tree ∧ ShapePreserving s.tree s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ⟨hwf, ShapePreserving.refl _⟩
    · exact ⟨remove_preserves_wellformed hwf hr, shapePreserving_remove hr⟩
  rcases hfinal with rfl | rfl
  · exact hwf₁.1
  · obtain ⟨dd, hdd, hk⟩ := hdoc.map hwf₁.2
    exact setOwnerDocument_preserves_wellformed hwf₁.1 hdd hk

theorem shapePreserving_adopt {s s' : DOMState} {node doc : NodeId}
    (h : adopt s node doc = .ok s') : ShapePreserving s.tree s'.tree := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have hkp : ShapePreserving s.tree s₁.tree := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact ShapePreserving.refl _
    · exact shapePreserving_remove hr
  rcases hfinal with rfl | rfl
  · exact hkp
  · exact hkp.trans (shapePreserving_setOwnerDocument _ _ _)

/-! ## insert -/

theorem insertEach_preserves_wellformed :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      WellFormed s.tree → IsDocument s.tree doc → insertEach s parent child doc ns = .ok s' →
      WellFormed s'.tree
  | [], _, _, _, _, _, hwf, _, h => by rw [insertEach] at h; rw [← Except.ok.inj h]; exact hwf
  | n :: ns, s, s', parent, child, doc, hwf, hdoc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      have hwf₁ := adopt_preserves_wellformed hwf hdoc ha
      have hdoc₁ := hdoc.map (shapePreserving_adopt ha)
      split at h
      · simp at h
      · next s₂ hi =>
        have hi' := (DOMState.mapTree_eq_ok hi).1
        exact insertEach_preserves_wellformed ns (insertAt_preserves_wellformed hwf₁ hi')
          (hdoc₁.map (shapePreserving_insertAt hi')) h

theorem shapePreserving_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId},
      insertEach s parent child doc ns = .ok s' → ShapePreserving s.tree s'.tree
  | [], _, _, _, _, _, h => by
    rw [insertEach] at h; rw [← Except.ok.inj h]; exact ShapePreserving.refl _
  | n :: ns, s, s', parent, child, doc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      split at h
      · simp at h
      · next s₂ hi =>
        exact (shapePreserving_adopt ha).trans
          ((shapePreserving_insertAt (DOMState.mapTree_eq_ok hi).1).trans
            (shapePreserving_insertEach ns h))

theorem insertEachAt_preserves_wellformed {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId}
    (hwf : WellFormed s.tree) (h : insertEachAt s parent child nodes = .ok s') :
    WellFormed s'.tree := by
  unfold insertEachAt at h
  split at h
  · simp at h
  · next pd hpd =>
    exact insertEach_preserves_wellformed _ hwf (isDocument_ownerDocument hwf hpd) h

theorem shapePreserving_insertEachAt {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} (h : insertEachAt s parent child nodes = .ok s') :
    ShapePreserving s.tree s'.tree := by
  unfold insertEachAt at h
  split at h
  · simp at h
  · exact shapePreserving_insertEach _ h

theorem insertNodesAt_preserves_wellformed {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : insertNodesAt s parent child nodes b = .ok s') :
    WellFormed s'.tree := by
  unfold insertNodesAt at h
  simp only at h
  split at h
  · simp at h
  · next s₁ hi =>
    have htree : s'.tree = s₁.tree := by
      split at h
      · rw [← Except.ok.inj h]
      · rw [← Except.ok.inj h]; simp
    rw [htree]
    exact insertEachAt_preserves_wellformed (by simpa using hwf) hi

theorem shapePreserving_insertNodesAt {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} {b : Bool} (h : insertNodesAt s parent child nodes b = .ok s') :
    ShapePreserving s.tree s'.tree := by
  unfold insertNodesAt at h
  simp only at h
  split at h
  · simp at h
  · next s₁ hi =>
    have htree : s'.tree = s₁.tree := by
      split at h
      · rw [← Except.ok.inj h]
      · rw [← Except.ok.inj h]; simp
    rw [htree]
    simpa using shapePreserving_insertEachAt hi

/-- PLAN §6.3。`insert` は well-formedness を保つ。 -/
theorem insert_preserves_wellformed {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : insert s node parent child b = .ok s') : WellFormed s'.tree := by
  unfold insert at h
  split at h
  · simp at h
  · next nd hnd =>
    split at h
    · split at h
      · rw [← Except.ok.inj h]; exact hwf
      · split at h
        · simp at h
        · next s₁ hr =>
          exact insertNodesAt_preserves_wellformed
            (by simpa using removeEach_preserves_wellformed _ hwf hr) h
    · exact insertNodesAt_preserves_wellformed hwf h

theorem shapePreserving_insert {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} (h : insert s node parent child b = .ok s') : ShapePreserving s.tree s'.tree := by
  unfold insert at h
  split at h
  · simp at h
  · next nd hnd =>
    split at h
    · split at h
      · rw [← Except.ok.inj h]; exact ShapePreserving.refl _
      · split at h
        · simp at h
        · next s₁ hr =>
          exact (shapePreserving_removeEach _ hr).trans
            (by simpa using shapePreserving_insertNodesAt h)
    · exact shapePreserving_insertNodesAt h

/-! ## 残りの algorithm の preservation -/

theorem preInsert_preserves_wellformed {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (h : preInsert s node parent child = .ok s') : WellFormed s'.tree := by
  unfold preInsert at h
  split at h
  · simp at h
  · exact insert_preserves_wellformed hwf h

theorem append_preserves_wellformed {s s' : DOMState} {node parent : NodeId}
    (hwf : WellFormed s.tree) (h : append s node parent = .ok s') : WellFormed s'.tree :=
  preInsert_preserves_wellformed hwf h

theorem preRemove_preserves_wellformed {s s' : DOMState} {child parent : NodeId}
    (hwf : WellFormed s.tree) (h : preRemove s child parent = .ok s') : WellFormed s'.tree := by
  unfold preRemove at h
  split at h
  · simp at h
  · exact remove_preserves_wellformed hwf h

theorem replace_preserves_wellformed {s s' : DOMState} {child node parent : NodeId}
    (hwf : WellFormed s.tree) (h : replace s child node parent = .ok s') :
    WellFormed s'.tree := by
  unfold replace at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next pd hpd =>
      simp only at h
      split at h
      · simp at h
      · next s₁ ha =>
        have hwf₁ := adopt_preserves_wellformed hwf (isDocument_ownerDocument hwf hpd) ha
        split at h
        · simp at h
        · next s₂ hr =>
          have hwf₂ : WellFormed s₂.tree := by
            revert hr; split
            · intro hr; rw [← Except.ok.inj hr]; exact hwf₁
            · intro hr; exact remove_preserves_wellformed hwf₁ (by simpa using hr)
          split at h
          · simp at h
          · next s₃ hi =>
            rw [← Except.ok.inj h]
            simpa using insert_preserves_wellformed hwf₂ hi

theorem replaceAll_preserves_wellformed {s s' : DOMState} {node : Option NodeId}
    {parent : NodeId} (hwf : WellFormed s.tree) (h : replaceAll s node parent = .ok s') :
    WellFormed s'.tree := by
  unfold replaceAll at h
  simp only at h
  split at h
  · simp at h
  · next s₁ hr =>
    have hwf₁ := removeEach_preserves_wellformed _ hwf hr
    split at h
    · simp at h
    · next s₂ hi =>
      have hwf₂ : WellFormed s₂.tree := by
        revert hi; split
        · intro hi; rw [← Except.ok.inj hi]; exact hwf₁
        · intro hi; exact insert_preserves_wellformed hwf₁ (by simpa using hi)
      rw [← Except.ok.inj h]
      simpa using hwf₂

/-! ## move -/

/--
`remove` は `detachWithLiveAdjust` の結果に record と transient observer を足しただけである。

足す step は木・range・iterator を変えないので、`move` の証明ではこの形で使う。
-/
theorem remove_eq_of_detach {s sd : DOMState} {n p : NodeId} {b : Bool}
    (hp : parentOf s.tree n = some p) (hd : detachWithLiveAdjust s n = .ok sd) :
    ∃ s₁, remove s n b = .ok s₁ ∧ s₁.tree = sd.tree ∧ s₁.ranges = sd.ranges ∧
      s₁.iterators = sd.iterators := by
  unfold remove
  rw [hp]
  simp only [hd]
  cases b
  · exact ⟨_, rfl, by simp, by simp, by simp⟩
  · exact ⟨_, rfl, by simp, by simp, by simp⟩

/-- 挿入側の range 調整は、木と range が同じ状態に対して同じ結果を返す。 -/
theorem liveRangeInsertAdjust_ranges_congr {s₁ s₂ : DOMState} {p : NodeId}
    {c : Option NodeId} {k : Nat} (ht : s₁.tree = s₂.tree) (hr : s₁.ranges = s₂.ranges) :
    (liveRangeInsertAdjust s₁ p c k).ranges = (liveRangeInsertAdjust s₂ p c k).ranges := by
  unfold liveRangeInsertAdjust
  cases c <;> simp [ht, hr]

/--
PLAN §6.2 / `memo.md` の `move_equivalent_to_remove_insert`（木への射影）。

`move` の木への効果は、`remove` の後に `insertAt` した結果と一致する。
`move` は仕様どおり node document を付け替えないので、
`insert`（adopt を含む）ではなく primitive の `insertAt` との一致になる。

live range と NodeIterator の調整 hook は `remove` と共有しているので、
Phase 5 と 6 で hook に中身を入れてもこの一致は保たれる。
-/
theorem move_eq_remove_insertAt {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (h : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧ insertAt s₁.tree newParent node child = .ok s'.tree := by
  unfold move at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next p hp =>
      split at h
      · simp at h
      · next sd hd =>
        obtain ⟨s₁, hrm, ht, _, _⟩ := remove_eq_of_detach (b := false) hp hd
        refine ⟨s₁, hrm, ?_⟩
        simp only at h
        split at h
        · simp at h
        · next s₂ hi =>
          have he : s'.tree = s₂.tree := by
            rw [← Except.ok.inj h]
            simp only [queueTreeMutationRecord_tree]
            split <;> simp
          rw [he, ht]
          simpa using (DOMState.mapTree_eq_ok hi).1

/-- `move` の後の range は、`remove` の後の range に挿入側の調整をかけたものである。 -/
theorem move_ranges {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      s'.ranges = (liveRangeInsertAdjust s₁ newParent child 1).ranges := by
  unfold move at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next p hp =>
      split at h
      · simp at h
      · next sd hd =>
        obtain ⟨s₁, hrm, ht, hr, _⟩ := remove_eq_of_detach (b := false) hp hd
        refine ⟨s₁, hrm, ?_⟩
        simp only at h
        split at h
        · simp at h
        · next s₂ hi =>
          have he : s'.ranges = s₂.ranges := by
            rw [← Except.ok.inj h]
            simp only [queueTreeMutationRecord_ranges]
            split <;> simp
          rw [he, (DOMState.mapTree_eq_ok hi).2, DOMState.withTree_ranges]
          exact liveRangeInsertAdjust_ranges_congr ht.symm hr.symm

/--
`moveValidity` が通ったときに得られる kind の事実。

step 4 は「node は Element か CharacterData」、
step 5 は「Document の子に Text は置けない」、
step 6 は「Document の子の element は高々一つで、その後ろに doctype は無い」である。
どれも `DocumentTreesValid` / `StructurallyValid` の保存に必要なものと対応する。
-/
theorem moveValidity_ok {t : Tree} {node newParent : NodeId} {child : Option NodeId}
    (h : moveValidity t node newParent child = .ok ()) :
    ∃ nd pd, t.get? node = some nd ∧ t.get? newParent = some pd ∧
      root t newParent = root t node ∧
      (nd.kind = .element ∨ nd.kind.isCharacterData = true) ∧
      (pd.kind = .document → nd.kind.isText = false) ∧
      (pd.kind = .document → nd.kind = .element →
        elementChildren t newParent = [] ∧ doctypeAtOrAfter t newParent child = false) := by
  unfold moveValidity at h
  split at h
  · simp at h
  · next pd hpd =>
    split at h
    · simp at h
    · next nd hnd =>
      split at h
      · simp at h
      · next h1 =>
          split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · next h4 =>
                split at h
                · simp at h
                · next h5 =>
                  split at h
                  · simp at h
                  · next h6 =>
                    rw [Bool.not_eq_true] at h4 h5 h6
                    simp only [Bool.not_eq_false'] at h4
                    refine ⟨nd, pd, hnd, hpd, by simpa using h1, ?_, ?_, ?_⟩
                    · rcases Bool.or_eq_true_iff.mp h4 with hk | hk
                      · exact Or.inl (by simpa using hk)
                      · exact Or.inr hk
                    · intro hdoc
                      simp only [hdoc, beq_self_eq_true, Bool.and_true] at h5
                      exact h5
                    · intro hdoc helem
                      simp only [hdoc, helem, beq_self_eq_true, Bool.true_and,
                        Bool.and_true] at h6
                      rw [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at h6
                      exact h6

/-- `move` が成功したなら step 1-6 の validity 検査を通っている。 -/
theorem move_moveValidity {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : move s node newParent child = .ok s') :
    moveValidity s.tree node newParent child = .ok () := by
  unfold move at h
  split at h
  · simp at h
  · next u hv => exact hv

/-- `move` の後の iterator は、`remove` の後の iterator と同じである。 -/
theorem move_iterators {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧ s'.iterators = s₁.iterators := by
  unfold move at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next p hp =>
      split at h
      · simp at h
      · next sd hd =>
        obtain ⟨s₁, hrm, _, _, hit⟩ := remove_eq_of_detach (b := false) hp hd
        refine ⟨s₁, hrm, ?_⟩
        simp only at h
        split at h
        · simp at h
        · next s₂ hi =>
          have he : s'.iterators = s₂.iterators := by
            rw [← Except.ok.inj h]
            simp only [queueTreeMutationRecord_iterators]
            split <;> simp
          rw [he, (DOMState.mapTree_eq_ok hi).2, DOMState.withTree_iterators,
            liveRangeInsertAdjust_iterators, hit]

/-- PLAN §6.3。`move` は well-formedness を保つ。 -/
theorem move_preserves_wellformed {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (h : move s node newParent child = .ok s') : WellFormed s'.tree := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt h
  exact insertAt_preserves_wellformed (remove_preserves_wellformed hwf hr) hi

/-- `move` した node の parent は指定した parent になる。 -/
theorem move_parentOf {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : move s node newParent child = .ok s') : parentOf s'.tree node = some newParent := by
  obtain ⟨s₁, _, hi⟩ := move_eq_remove_insertAt h
  exact insertAt_parentOf hi

/-- `move` した node は、旧 parent の children から外れて新 parent の children に入る。 -/
theorem move_childrenOf {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (hwf : WellFormed s.tree) (h : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      childrenOf s'.tree newParent =
        ListUtil.insertBefore (childrenOf s₁.tree newParent) child node := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt h
  refine ⟨s₁, hr, ?_⟩
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, _, ht⟩ := insertAt_ok_cases hi
  have hne : node ≠ newParent := by
    intro he
    have hcon : isInclusiveAncestorOf s₁.tree node newParent = true :=
      (isInclusiveAncestorOf_iff (remove_preserves_wellformed hwf hr) node newParent).mpr
        (Or.inl he)
    rw [hanc] at hcon
    simp at hcon
  rw [ht, childrenOf_insertAtIn hnd hpd hne, if_pos rfl]

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
theorem insert_single {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} {nd : NodeData} (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert s node parent child b = .ok s') :
    ∃ pd s₁, s.tree.get? parent = some pd ∧
      adopt (liveRangeInsertAdjust s parent child 1) node pd.ownerDocument = .ok s₁ ∧
      insertAt s₁.tree parent node child = .ok s'.tree ∧ s'.ranges = s₁.ranges := by
  unfold insert at h
  split at h
  · next hn => rw [hnd] at hn; simp at hn
  · next nd' hnd' =>
    rw [hnd] at hnd'
    cases hnd'
    split at h
    · next hf => exact absurd hf hk
    · unfold insertNodesAt at h
      simp only at h
      split at h
      · simp at h
      · next sx hx =>
        -- step 9 の record は木も range も変えない。
        have ht : s'.tree = sx.tree := by
          split at h
          · rw [← Except.ok.inj h]
          · rw [← Except.ok.inj h]; simp
        have hr : s'.ranges = sx.ranges := by
          split at h
          · rw [← Except.ok.inj h]
          · rw [← Except.ok.inj h]; simp
        unfold insertEachAt at hx
        simp only [List.length_cons, List.length_nil, liveRangeInsertAdjust_tree] at hx
        split at hx
        · simp at hx
        · next pd hpd =>
          rw [insertEach] at hx
          split at hx
          · simp at hx
          · next s₁ ha =>
            split at hx
            · simp at hx
            · next s₂ hi =>
              rw [insertEach] at hx
              obtain ⟨hi₁, hi₂⟩ := DOMState.mapTree_eq_ok hi
              refine ⟨pd, s₁, hpd, ha, ?_, ?_⟩
              · rw [ht, ← Except.ok.inj hx]; exact hi₁
              · rw [hr, ← Except.ok.inj hx, hi₂]; rfl

/--
PLAN §6.3。fragment でない node を `insert` すると、
node は parent の children において child のちょうど直前に来る。
-/
theorem insert_children_split {s s' : DOMState} {node parent c : NodeId} {b : Bool}
    {nd : NodeData} (hwf : WellFormed s.tree) (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert s node parent (some c) b = .ok s') :
    ∃ t₁, childrenOf s'.tree parent = ListUtil.insertBefore (childrenOf t₁ parent) (some c) node ∧
      ∃ s₁ s₂, childrenOf t₁ parent = s₁ ++ c :: s₂ ∧
        childrenOf s'.tree parent = s₁ ++ node :: c :: s₂ := by
  obtain ⟨pd, s₁, hpd, ha, hi, _⟩ := insert_single hnd hk h
  have hwf₁ : WellFormed s₁.tree :=
    adopt_preserves_wellformed (by simpa using hwf)
      (by simpa using isDocument_ownerDocument hwf hpd) ha
  exact ⟨s₁.tree, insertAt_childrenOf hwf₁ hi, insertAt_children_split hwf₁ hi⟩

/-- `insert` した node の parent は指定した parent になる。 -/
theorem insert_parentOf {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    {nd : NodeData} (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (h : insert s node parent child = .ok s') : parentOf s'.tree node = some parent := by
  obtain ⟨pd, s₁, hpd, ha, hi, _⟩ := insert_single hnd hk h
  exact insertAt_parentOf hi

/-- parent を持つ node の `adopt` は `remove` を経由する。 -/
theorem adopt_of_parent_isSome {s s₁ : DOMState} {node doc : NodeId}
    (hp : (parentOf s.tree node).isSome) (h : adopt s node doc = .ok s₁) :
    ∃ s₀, remove s node = .ok s₀ ∧
      (s₁ = s₀ ∨ s₁ = s₀.withTree (setOwnerDocument s₀.tree node doc)) := by
  obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases h
  refine ⟨s₀, ?_, hfinal⟩
  rcases hstep with ⟨hn, _⟩ | hr
  · rw [hn] at hp; simp at hp
  · exact hr

/--
PLAN §6.3 / `memo.md` §9。既に parent を持つ node の `insert` は、必ず `remove` を経由する。

`adopt` が素の detach ではなく完全な `remove` を呼ぶので、
explicit な remove と move 中の implicit な removal が同じ経路を通る。
違いは node document の付け替えを挟むかどうかだけである。
-/
theorem insert_factors_through_remove {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} {nd : NodeData} (hnd : s.tree.get? node = some nd)
    (hk : ¬ (nd.kind == NodeKind.documentFragment) = true)
    (hp : (parentOf s.tree node).isSome) (h : insert s node parent child b = .ok s') :
    ∃ s₀ t₁, remove (liveRangeInsertAdjust s parent child 1) node = .ok s₀ ∧
      (t₁ = s₀.tree ∨ ∃ doc, t₁ = setOwnerDocument s₀.tree node doc) ∧
      insertAt t₁ parent node child = .ok s'.tree := by
  obtain ⟨pd, s₁, hpd, ha, hi, _⟩ := insert_single hnd hk h
  obtain ⟨s₀, hr, hcase⟩ :=
    adopt_of_parent_isSome (by simpa using hp) ha
  refine ⟨s₀, s₁.tree, hr, ?_, hi⟩
  rcases hcase with he | he
  · exact Or.inl (by rw [he])
  · exact Or.inr ⟨pd.ownerDocument, by rw [he]; rfl⟩

/-! ## public API の preservation -/

/--
PLAN §6.1。public API はすべて §4.2.3 の algorithm を経由するので、
well-formedness の保存は algorithm 側の定理から直ちに従う。

この構造が「どの API から始めても live object の調整が迂回されない」ことの土台になる
（`memo.md` §7）。Phase 5 と 6 で hook に中身を入れたときも、
API ごとに証明をやり直す必要はない。
-/
theorem appendChild_preserves_wellformed {s s' : DOMState} {parent node : NodeId}
    (hwf : WellFormed s.tree) (h : appendChild s parent node = .ok s') : WellFormed s'.tree :=
  append_preserves_wellformed hwf h

theorem insertBefore_preserves_wellformed {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (h : insertBefore s parent node child = .ok s') : WellFormed s'.tree :=
  preInsert_preserves_wellformed hwf h

theorem replaceChild_preserves_wellformed {s s' : DOMState} {parent node child : NodeId}
    (hwf : WellFormed s.tree) (h : replaceChild s parent node child = .ok s') :
    WellFormed s'.tree :=
  replace_preserves_wellformed hwf h

theorem removeChild_preserves_wellformed {s s' : DOMState} {parent child : NodeId}
    (hwf : WellFormed s.tree) (h : removeChild s parent child = .ok s') : WellFormed s'.tree :=
  preRemove_preserves_wellformed hwf h

theorem replaceChildren_preserves_wellformed {s s' : DOMState} {parent : NodeId}
    {node : Option NodeId} (hwf : WellFormed s.tree)
    (h : replaceChildren s parent node = .ok s') : WellFormed s'.tree := by
  unfold replaceChildren at h
  split at h
  · exact replaceAll_preserves_wellformed hwf h
  · split at h
    · simp at h
    · exact replaceAll_preserves_wellformed hwf h

theorem before_preserves_wellformed {s s' : DOMState} {this node : NodeId}
    (hwf : WellFormed s.tree) (h : before s this node = .ok s') : WellFormed s'.tree := by
  unfold before at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact preInsert_preserves_wellformed hwf h

theorem after_preserves_wellformed {s s' : DOMState} {this node : NodeId}
    (hwf : WellFormed s.tree) (h : after s this node = .ok s') : WellFormed s'.tree := by
  unfold after at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact preInsert_preserves_wellformed hwf h

theorem replaceWith_preserves_wellformed {s s' : DOMState} {this node : NodeId}
    (hwf : WellFormed s.tree) (h : replaceWith s this node = .ok s') : WellFormed s'.tree := by
  unfold replaceWith at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · next parent hpar =>
    rw [if_pos hpar] at h
    exact replace_preserves_wellformed hwf h

theorem nodeRemove_preserves_wellformed {s s' : DOMState} {this : NodeId}
    (hwf : WellFormed s.tree) (h : nodeRemove s this = .ok s') : WellFormed s'.tree := by
  unfold nodeRemove at h
  split at h
  · rw [← Except.ok.inj h]; exact hwf
  · exact remove_preserves_wellformed hwf h

/--
`moveBefore` は receiver の kind を検査してから `move` を呼ぶ。

検査を通った後は `move` そのものなので、`move` の定理をそのまま持ち上げられる。
-/
theorem moveBefore_ok {s s' : DOMState} {parent node : NodeId} {child : Option NodeId}
    (h : moveBefore s parent node child = .ok s') :
    ∃ pd ref, s.tree.get? parent = some pd ∧ pd.kind.canHaveChildren = true ∧
      move s node parent ref = .ok s' := by
  unfold moveBefore at h
  split at h
  · simp at h
  · next pd hpd =>
    split at h
    · simp at h
    · next hk => exact ⟨pd, _, hpd, by simpa using hk, h⟩

theorem moveBefore_preserves_wellformed {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (h : moveBefore s parent node child = .ok s') : WellFormed s'.tree := by
  obtain ⟨_, _, _, _, hm⟩ := moveBefore_ok h
  exact move_preserves_wellformed hwf hm

/-! ## replace / replace all / move も kind と attribute を変えない -/

/-- 木が変わらないなら当然 `ShapePreserving` である。 -/
theorem shapePreserving_of_tree_eq {t t' : Tree} (h : t' = t) : ShapePreserving t t' := by
  rw [h]; exact ShapePreserving.refl _

theorem shapePreserving_move {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hm : move s node newParent child = .ok s') :
    ShapePreserving s.tree s'.tree := by
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  exact (shapePreserving_remove hr).trans (shapePreserving_insertAt hi)

theorem shapePreserving_moveBefore {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : moveBefore s parent node child = .ok s') :
    ShapePreserving s.tree s'.tree := by
  obtain ⟨_, _, _, _, hm⟩ := moveBefore_ok h
  exact shapePreserving_move hm

theorem shapePreserving_replace {s s' : DOMState} {child node parent : NodeId}
    (hr : replace s child node parent = .ok s') : ShapePreserving s.tree s'.tree := by
  unfold replace at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next pd hpd =>
      simp only at hr
      split at hr
      · simp at hr
      · next s₁ ha =>
        split at hr
        · simp at hr
        · next s₂ hrm =>
          have h₂ : ShapePreserving s₁.tree s₂.tree := by
            revert hrm
            split
            · intro hrm; rw [← Except.ok.inj hrm]; exact ShapePreserving.refl _
            · intro hrm; exact shapePreserving_remove (by simpa using hrm)
          split at hr
          · simp at hr
          · next s₃ hi =>
            rw [← Except.ok.inj hr]
            refine (((shapePreserving_adopt ha).trans h₂).trans (shapePreserving_insert hi)).trans ?_
            exact shapePreserving_of_tree_eq (by simp)

theorem shapePreserving_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hr : replaceAll s node parent = .ok s') : ShapePreserving s.tree s'.tree := by
  unfold replaceAll at hr
  simp only at hr
  split at hr
  · simp at hr
  · next s₁ hre =>
    split at hr
    · simp at hr
    · next s₂ hins =>
      have h₂ : ShapePreserving s₁.tree s₂.tree := by
        revert hins
        split
        · intro hins; rw [← Except.ok.inj hins]; exact ShapePreserving.refl _
        · intro hins; exact shapePreserving_insert (by simpa using hins)
      rw [← Except.ok.inj hr]
      refine ((shapePreserving_removeEach _ hre).trans h₂).trans ?_
      exact shapePreserving_of_tree_eq (by simp)

/-- `moveBefore` も `remove` してから `insertAt` する形に分解できる。 -/
theorem moveBefore_eq_remove_insertAt {s s' : DOMState} {parent node : NodeId}
    {child : Option NodeId} (h : moveBefore s parent node child = .ok s') :
    ∃ s₁ ref, remove s node = .ok s₁ ∧ insertAt s₁.tree parent node ref = .ok s'.tree := by
  obtain ⟨_, _, _, _, hm⟩ := moveBefore_ok h
  obtain ⟨s₁, hr, hi⟩ := move_eq_remove_insertAt hm
  exact ⟨s₁, _, hr, hi⟩

end Dom
