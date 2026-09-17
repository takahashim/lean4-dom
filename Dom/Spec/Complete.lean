import Dom.Spec.RemoveCongr
import Dom.Spec.AdoptCongr
import Dom.Spec.InsertCongr
import Dom.Spec.InsertSound
import Dom.Properties.Contract

/-!
# 関係を満たす状態は、実行関数が実際に作る

soundness（`Dom/Spec/RemoveSound.lean` ほか）は「実行関数の結果は関係を満たす」を言う。
その逆、**completeness** は二つに分かれる。

1. **余計な model が無いこと**：関係を満たす状態は、実行関数が作る状態と観測が等しい。
   これは soundness と一意性（`Dom/Spec/RemoveCongr.lean` ほか）から出る。
2. **実現できること**：関係が満たせるなら、実行関数は失敗しない。
   これは契約（`Dom/Properties/Contract.lean`）から出る。

二つ合わせて「関係と実行関数は観測の上で同じものを表す」と言える。
soundness だけだと、関係が緩くても（あるいは満たせなくても）成り立ってしまう。
-/

namespace Dom.Spec

open Dom

/-! ## `remove` -/

/--
**`RemoveSpec` を満たす状態があるなら、`remove` は成功してその観測を作る。**

関係の step 1-2（parent が非 null）がそのまま契約の成功条件である。
-/
theorem remove_complete {s s' : DOMState} {n : NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : RemoveSpec s n b s') : ∃ out, remove s n b = .ok out ∧ ObsEq s' out := by
  have hc := h
  obtain ⟨parent, -, hpre, -⟩ := hc
  obtain ⟨out, hout⟩ := (remove_succeeds_iff hwf (n := n) (b := b)).mpr (by rw [hpre]; rfl)
  exact ⟨out, hout, removeSpec_congr hwf (ObsEq.refl s) h (remove_sound hwf hout)⟩

/-! ## `adopt` -/

/--
`adopt` が成功する条件は step 1 だけである。

step 2 の `remove` は parent がある node にしか呼ばないので、そこでは失敗しない。
-/
theorem adopt_succeeds_of_ownerDocument {s : DOMState} {node doc oldDoc : NodeId}
    (hwf : WellFormed s.tree) (h : ownerDocumentOf s.tree node = some oldDoc) :
    ∃ out, adopt s node doc = .ok out := by
  cases hp : parentOf s.tree node with
  | none => exact ⟨_, adopt_of_steps h (Or.inl ⟨hp, rfl⟩)⟩
  | some p =>
    obtain ⟨s₁, hs₁⟩ := (remove_succeeds_iff hwf (n := node) (b := false)).mpr (by rw [hp]; rfl)
    exact ⟨_, adopt_of_steps h (Or.inr ⟨⟨p, hp⟩, hs₁⟩)⟩

/-- **`AdoptSpec` を満たす状態があるなら、`adopt` は成功してその観測を作る。** -/
theorem adopt_complete {s s' : DOMState} {node doc : NodeId} (hwf : WellFormed s.tree)
    (h : AdoptSpec s node doc s') : ∃ out, adopt s node doc = .ok out ∧ ObsEq s' out := by
  have hc := h
  obtain ⟨oldDoc, hod, -⟩ := hc
  obtain ⟨out, hout⟩ := adopt_succeeds_of_ownerDocument (doc := doc) hwf hod
  exact ⟨out, hout, adoptSpec_congr hwf (ObsEq.refl s) h (adopt_sound hwf hout)⟩

/-! ## `insert` -/

/-- `adopt` の後、node は parent を持たない。 -/
theorem adopt_parentOf_none {s sout : DOMState} {node doc : NodeId}
    (h : adopt s node doc = .ok sout) : parentOf sout.tree node = none := by
  obtain ⟨_, s₀, _, hstep, hfinal⟩ := adopt_cases h
  have hnp₀ : parentOf s₀.tree node = none := by
    rcases hstep with ⟨hn, rfl⟩ | ⟨-, hr⟩
    · exact hn
    · exact remove_parentOf hr
  rcases hfinal with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hnp₀
  · rw [DOMState.withTree_tree, parentOf_setOwnerDocument]
    exact hnp₀

/--
**step 7 の実現可能性。**

関係 `InsertedEach` を満たす状態があるなら、`insertEach` は成功して観測の等しい
結果を返す。各段で `adopt` の完全性と `insertAt` の四つの前提条件を使う。
`child` が `parent` の子であることは `TreeInserted.childIsChild` が与える。
-/
theorem insertEach_complete {parent : NodeId} {child : Option NodeId} {doc : NodeId} :
    ∀ (ns : List NodeId) {s sx out : DOMState},
    WellFormed s.tree → IsDocument s.tree doc →
    (∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent) →
    (∃ pd, s.tree.get? parent = some pd) →
    InsertedEach parent child doc s ns out → ObsEq s sx →
    ∃ o, insertEach sx parent child doc ns = .ok o ∧ ObsEq out o := by
  intro ns
  induction ns with
  | nil =>
    intro s sx out _ _ _ _ h hobs
    cases h
    exact ⟨sx, by rw [insertEach], hobs⟩
  | cons n ns ih =>
    intro s sx out hwf hdoc hacyc hpe h hobs
    cases h with
    | @cons _ sa sb _ _ _ ha hi hlive hrest =>
      obtain ⟨pd, hpd⟩ := hpe
      obtain ⟨hwfa, hanca, hwfb, hdocb, hacycb⟩ := insertedEach_step hwf hdoc hacyc ha hi
      -- step 7.1：adopt は成功する
      obtain ⟨oldDoc, hod, -⟩ := id ha
      have hodx : ownerDocumentOf sx.tree n = some oldDoc := by
        rw [hobs.tree.ownerDocumentOf]; exact hod
      obtain ⟨o₁, ho₁⟩ := adopt_succeeds_of_ownerDocument (doc := doc)
        (hobs.tree.wellFormed hwf) hodx
      have hobsa : ObsEq sa o₁ :=
        adoptSpec_congr hwf hobs ha (adopt_sound (hobs.tree.wellFormed hwf) ho₁)
      -- step 7.2：insertAt の四つの前提
      have hkp : ShapePreserving sx.tree o₁.tree := shapePreserving_adopt ho₁
      have hpdx : sx.tree.get? parent = some pd := by rw [hobs.tree]; exact hpd
      obtain ⟨pd₁, hpd₁⟩ := exists_get?_of_kindPreserving hkp hpdx
      obtain ⟨nd₁, hnd₁⟩ : ∃ nd₁, o₁.tree.get? n = some nd₁ := by
        obtain ⟨nd, hnd⟩ : ∃ nd, sx.tree.get? n = some nd := by
          cases hq : sx.tree.get? n with
          | some x => exact ⟨x, rfl⟩
          | none => rw [ownerDocumentOf_eq, hq] at hodx; simp at hodx
        exact exists_get?_of_kindPreserving hkp hnd
      have hnp : nd₁.parent = none := by
        have := adopt_parentOf_none ho₁
        rw [parentOf_of_get? hnd₁] at this
        exact this
      have hanc : isInclusiveAncestorOf o₁.tree n parent = false := by
        cases hb : isInclusiveAncestorOf o₁.tree n parent with
        | false => rfl
        | true =>
          exfalso
          refine hanca ?_
          refine (hobsa.tree.inclusiveAncestor_iff).mp ?_
          exact (isInclusiveAncestorOf_iff (hobsa.tree.wellFormed hwfa) n parent).mp hb
      have hchild : ∀ c, child = some c → c ∈ pd₁.children := by
        intro c hc
        have hcm := hi.childIsChild c hc
        rw [← childrenOf_eq hpd₁]
        rw [hobsa.tree.childrenOf]
        exact hcm
      have hins := insertAt_eq_ok hpd₁ hnd₁ hnp hanc hchild
      have hmap : o₁.mapTree (fun t => insertAt t parent n child) =
          .ok (o₁.withTree (insertAtIn o₁.tree parent n child pd₁ nd₁)) := by
        show (match insertAt o₁.tree parent n child with
          | Except.error e => Except.error e
          | Except.ok t => Except.ok (o₁.withTree t)) = _
        rw [hins]
      -- step 7.3：結果は観測が等しい
      obtain ⟨o₂, ho₂⟩ : ∃ o₂ : DOMState,
          o₂ = o₁.withTree (insertAtIn o₁.tree parent n child pd₁ nd₁) := ⟨_, rfl⟩
      have hins₂ : TreeInserted o₁.tree o₂.tree parent n child :=
        treeInserted_insertAt (by rw [ho₂, DOMState.withTree_tree]; exact hins)
      have htree : TreeObsEq sb.tree o₂.tree := treeInserted_congr hobsa.tree hi hins₂
      have hobsb : ObsEq sb o₂ := by
        refine ⟨htree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ho₂, DOMState.withTree_ranges, hobsa.ranges, hlive.ranges]
        · rw [ho₂, DOMState.withTree_iterators, hobsa.iterators, hlive.iterators]
        · intro r
          rw [ho₂]
          show r ∈ o₁.registrations ↔ _
          rw [hobsa.registrations r, hlive.registrations]
        · intro mo
          rw [ho₂]
          show (o₁.observers[mo]?).map (·.records) = _
          rw [hobsa.records mo, hlive.observers]
        · intro mo
          rw [ho₂]
          show mo ∈ o₁.pendingObservers ↔ _
          rw [hobsa.pendingObservers mo, hlive.pendingObservers]
        · rw [ho₂, DOMState.withTree_microtaskQueued, hobsa.microtaskQueued,
            hlive.microtaskQueued]
        · rw [ho₂, DOMState.withTree_walkers, hobsa.walkers, hlive.untouched.walkers]
        · rw [ho₂, DOMState.withTree_listeners, hobsa.listeners, hlive.untouched.listeners]
        · rw [ho₂, DOMState.withTree_detachedAttrs, hobsa.detachedAttrs,
            hlive.untouched.detachedAttrs]
      have hpdsa : sa.tree.get? parent = some pd₁ := by rw [← hobsa.tree parent]; exact hpd₁
      have hpdsb : ∃ pdb, sb.tree.get? parent = some pdb := by
        have hsn := hi.sameNodes parent
        rw [hpdsa] at hsn
        cases hq : sb.tree.get? parent with
        | none => rw [hq] at hsn; simp at hsn
        | some x => exact ⟨x, rfl⟩
      obtain ⟨o, hoeq, hoobs⟩ := ih hwfb hdocb hacycb hpdsb hrest hobsb
      refine ⟨o, ?_, hoobs⟩
      rw [insertEach, ho₁]
      show (match o₁.mapTree (fun t => insertAt t parent n child) with
        | Except.error e => Except.error e
        | Except.ok s₂ => insertEach s₂ parent child doc ns) = _
      rw [hmap, ← ho₂]
      exact hoeq

/-- **step 4 の実現可能性。** -/
theorem removeEach_complete : ∀ (ns : List NodeId) {s sx out : DOMState} {b : Bool},
    WellFormed s.tree → RemoveEachSpec s ns b out → ObsEq s sx →
    ∃ o, removeEach sx ns b = .ok o ∧ ObsEq out o := by
  intro ns
  induction ns with
  | nil =>
    intro s sx out b _ h hobs
    cases h
    exact ⟨sx, by rw [removeEach], hobs⟩
  | cons n ns ih =>
    intro s sx out b hwf h hobs
    cases h with
    | @cons _ s₁ _ _ _ _ hr hrest =>
      have hwfx : WellFormed sx.tree := hobs.tree.wellFormed hwf
      have hrx : RemoveSpec sx n b s₁ := removeSpec_transport hwfx (ObsEq.symm hobs) hr
      obtain ⟨o₁, ho₁, hobs₁⟩ := remove_complete hwfx hrx
      have hwf₁ : WellFormed s₁.tree := removeSpec_wellFormed hwf hr
      obtain ⟨o, hoeq, hoobs⟩ := ih hwf₁ hrest hobs₁
      refine ⟨o, ?_, hoobs⟩
      rw [removeEach, ho₁]
      exact hoeq


/--
**`InsertSpec` に余計な model は無い。**

`insert` が成功するなら、関係を満たす状態はその結果と観測が等しい。
「関係を満たせるなら `insert` は成功する」（実現できること）のほうは、
`insertAt` の step 4（`child` が `parent` の子であること）を関係が述べていないので
まだ言えない。仕様ではその検査は `insert` の呼び出し側（pre-insert）にある。
-/
theorem insert_of_empty_fragment {s : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} {d : NodeData}
    (hnd : s.tree.get? node = some d) (hk : d.kind = NodeKind.documentFragment)
    (hch : d.children = []) : insert s node parent child b = .ok s := by
  unfold insert
  simp only [hnd]
  rw [if_pos (by simp [hk]), if_pos (by rw [hch]; rfl)]

/--
**空の DocumentFragment については完全性が言える。**

`InsertSpec` の step 2-3 の枝（入れる node の列が空）では、
関係を満たす状態は必ず `insert` の結果である。
-/
theorem insert_complete_of_nil {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} {nodes : List NodeId}
    (hn : NodesToInsert s.tree node nodes) (hnil : nodes = []) (hs : s' = s) :
    insert s node parent child b = .ok s' := by
  obtain ⟨d, hnd, hcase⟩ := hn
  rcases hcase with ⟨hk, hch⟩ | ⟨-, hsing⟩
  · rw [hs]
    exact insert_of_empty_fragment hnd hk (by rw [← hch, hnil])
  · exact absurd (hnil ▸ hsing) (by simp)

theorem insert_no_extra_models {s s' out : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h : InsertSpec s node parent child b s') (hok : insert s node parent child b = .ok out) :
    ObsEq s' out :=
  insertSpec_congr hwf (ObsEq.refl s) hacyc h (insert_sound hwf hok)

/-- **step 5-7 の実現可能性。** -/
theorem insertEachAt_complete {parent : NodeId} {child : Option NodeId} {doc : NodeId}
    {nodes : List NodeId} {s sx out : DOMState} {pd : NodeData}
    (hwf : WellFormed s.tree) (hdoc : IsDocument s.tree doc)
    (hacyc : ∀ m ∈ nodes, ¬ InclusiveAncestor s.tree m parent)
    (hpd : s.tree.get? parent = some pd) (hdeq : doc = pd.ownerDocument)
    (h : InsertedEach parent child doc s nodes out) (hobs : ObsEq s sx) :
    ∃ o, insertEachAt sx parent child nodes = .ok o ∧ ObsEq out o := by
  have hpdx : sx.tree.get? parent = some pd := by rw [hobs.tree]; exact hpd
  rw [insertEachAt_of_get? hpdx, ← hdeq]
  exact insertEach_complete nodes hwf hdoc hacyc ⟨pd, hpd⟩ h hobs

/-- step 5-9 の実現可能性（共通部分）。 -/
theorem insertNodesAt_isOk_of_spec {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} {s₁ sx s₂ s₃ : DOMState} {idx : Nat} {pd : NodeData} {b : Bool}
    (hwf : WellFormed s₁.tree)
    (hacyc : ∀ m ∈ nodes, ¬ InclusiveAncestor s₁.tree m parent)
    (hpd : s₁.tree.get? parent = some pd)
    (hidx : ChildIndex s₁.tree child idx)
    (hra : RangeInsertAdjusted s₁ s₂ parent child idx nodes.length)
    (hie : InsertedEach parent child pd.ownerDocument s₂ nodes s₃)
    (hobs : ObsEq s₁ sx) :
    ∃ o, insertNodesAt sx parent child nodes b = .ok o := by
  have hidxx : ChildIndex sx.tree child idx := by
    cases child with
    | none => exact hidx
    | some c =>
      show index sx.tree c = some idx
      rw [hobs.tree.index]; exact hidx
  have hobs₂ : ObsEq s₂ (liveRangeInsertAdjust sx parent child nodes.length) :=
    rangeInsertAdjusted_congr hobs hra
      (rangeInsertAdjusted_of_adjust sx parent child nodes.length idx hidxx)
  have hwf₂ : WellFormed s₂.tree := by rw [hra.tree]; exact hwf
  have hdoc₂ : IsDocument s₂.tree pd.ownerDocument := by
    rw [hra.tree]; exact isDocument_ownerDocument hwf hpd
  have hpd₂ : s₂.tree.get? parent = some pd := by rw [hra.tree]; exact hpd
  have hacyc₂ : ∀ m ∈ nodes, ¬ InclusiveAncestor s₂.tree m parent := by
    rw [hra.tree]; exact hacyc
  obtain ⟨o, hoeq, -⟩ :=
    insertEachAt_complete hwf₂ hdoc₂ hacyc₂ hpd₂ rfl hie hobs₂
  exact insertNodesAt_isOk ⟨o, hoeq⟩

/-- **`insert` は関係を満たす状態があるなら成功する。** -/
theorem insert_isOk_of_spec {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h : InsertSpec s node parent child b s') :
    ∃ out, insert s node parent child b = .ok out := by
  obtain ⟨nodes, hnodes, hcase⟩ := h
  rcases hcase with ⟨hnil, hs⟩ | ⟨hne, s₁, s₂, s₃, idx, prev, pd, hfp, hidx, hprev, hra, hpd,
    hie, hrec, hoo⟩
  · exact ⟨s, insert_complete_of_nil hnodes hnil rfl⟩
  · -- step 4：fragment を空にする
    obtain ⟨hwf₁, hanc₁⟩ := fragmentPrepared_facts hwf hfp
    have hacyc₁ : ∀ m ∈ nodes, ¬ InclusiveAncestor s₁.tree m parent := by
      intro m hm hinc
      refine hacyc nodes hnodes m hm ?_
      rcases hinc with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr (hanc₁ _ _ ha)
    obtain ⟨d, hd, hfpcase⟩ := hfp
    obtain ⟨d', hd', hnc⟩ := hnodes
    rw [hd] at hd'
    cases hd'
    by_cases hk : d.kind = NodeKind.documentFragment
    · rw [if_pos hk] at hfpcase
      obtain ⟨sr, hre, hq, hoo'⟩ := hfpcase
      have hnodes_eq : nodes = d.children := by
        rcases hnc with ⟨-, hch⟩ | ⟨hkne, -⟩
        · exact hch
        · exact absurd hk hkne
      obtain ⟨o₀, ho₀, hobs₀⟩ := removeEach_complete nodes hwf hre (ObsEq.refl s)
      have hwfr : WellFormed sr.tree := removeEachSpec_wellFormed hwf hre
      have hobs₁ : ObsEq s₁ (queueTreeMutationRecord o₀ node [] nodes none none) := by
        refine treeRecordQueued_congr (s := sr) (s' := o₀) hobs₀ hq ?_ hoo' ?_
        · exact treeRecordQueued_of_queue o₀ (hobs₀.tree.wellFormed hwfr) node [] nodes none none
            (by cases hx : nodes with
                | nil => exact absurd hx hne
                | cons a as => simp)
        · exact ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩
      have hstep := insertNodesAt_isOk_of_spec (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (b := b)
        hwf₁ hacyc₁ hpd hidx hra hie hobs₁
      unfold insert
      simp only [hd]
      rw [if_pos (by simp [hk]),
        if_neg (by rw [← hnodes_eq]; cases hx : nodes with
                   | nil => exact absurd hx hne
                   | cons a as => simp)]
      rw [← hnodes_eq]
      simp only [ho₀]
      exact hstep
    · rw [if_neg hk] at hfpcase
      subst hfpcase
      have hnodes_eq : nodes = [node] := by
        rcases hnc with ⟨hkf, -⟩ | ⟨-, hsing⟩
        · exact absurd hkf hk
        · exact hsing
      have hstep := insertNodesAt_isOk_of_spec (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (b := b)
        hwf₁ hacyc₁ hpd hidx hra hie (ObsEq.refl s₁)
      unfold insert
      simp only [hd]
      rw [if_neg (by simp [hk])]
      rw [hnodes_eq] at hstep
      exact hstep

/--
**`insert` の完全性。**

関係 `InsertSpec` を満たす状態があるなら、`insert` は成功して観測の等しい結果を
返す。成功することは `insert_isOk_of_spec`、観測が等しいことは
`insert_no_extra_models` である。
-/
theorem insert_complete {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h : InsertSpec s node parent child b s') :
    ∃ out, insert s node parent child b = .ok out ∧ ObsEq s' out := by
  obtain ⟨out, hok⟩ := insert_isOk_of_spec hwf hacyc h
  exact ⟨out, hok, insert_no_extra_models hwf hacyc h hok⟩

end Dom.Spec
