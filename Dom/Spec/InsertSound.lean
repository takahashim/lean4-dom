import Dom.Spec.Insert
import Dom.Spec.AdoptSound
import Dom.Spec.RecordSound

/-!
# `insert` は関係意味論を満たす（soundness）

`Dom/Spec/Insert.lean` の `InsertSpec` を、実行関数 `insert` が満たすことを示す。

step 4 は `remove_sound`、step 7.1 は `adopt_sound`、step 4.2 と step 9 は
`treeRecordQueued_of_queue` に帰着する。残るのは step 5（range の調整）と
step 7.2-7.3（木への挿入）である。
-/

namespace Dom.Spec

open Dom

/-! ## step 4.1：列を順に外す -/

theorem removeEach_sound : ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
    WellFormed s.tree → removeEach s ns b = .ok s' → RemoveEachSpec s ns b s'
  | [], s, s', b, _, h => by
    rw [removeEach] at h
    rw [← Except.ok.inj h]
    exact .nil
  | n :: rest, s, s', b, hwf, h => by
    rw [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr =>
      exact .cons (remove_sound hwf hr)
        (removeEach_sound rest (remove_preserves_wellformed hwf hr) h)

/-! ## step 7.1：adopt が木に与える影響 -/

/-- `adopt` は、対象の node 以外の parent を動かさない。 -/
theorem parentOf_adopt {s sa : DOMState} {n doc : NodeId} (h : adopt s n doc = .ok sa)
    (m : NodeId) : parentOf sa.tree m = if m = n then none else parentOf s.tree m := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have hpar : ∀ m, parentOf s₁.tree m = if m = n then none else parentOf s.tree m := by
    rcases hstep with ⟨hn, rfl⟩ | hr
    · intro m
      by_cases hm : m = n
      · rw [if_pos hm, hm, hn]
      · rw [if_neg hm]
    · intro m
      exact parentOf_detach (remove_ok hr).2 m
  rcases hfinal with rfl | rfl
  · exact hpar m
  · show parentOf (setOwnerDocument s₁.tree n doc) m = _
    rw [parentOf_setOwnerDocument]
    exact hpar m

/-! ## step 7.2-7.3：木への挿入 -/

/-- **`insertAt` は `TreeInserted` を満たす。** -/
theorem treeInserted_insertAt {t t' : Tree} {parent node : NodeId} {child : Option NodeId}
    (h : insertAt t parent node child = .ok t') : TreeInserted t t' parent node child := by
  obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, rfl⟩ := insertAt_ok_cases h
  have hne : node ≠ parent := by
    intro he
    rw [he] at hanc
    rw [isInclusiveAncestorOf_self] at hanc
    simp at hanc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parentOf_insertAtIn hpd, if_pos rfl]
  · intro c hc
    rw [childrenOf_eq hpd]
    exact hchild c hc
  · rw [childrenOf_insertAtIn hnd hpd hne, if_pos rfl]
  · intro m hm; rw [parentOf_insertAtIn hpd, if_neg hm]
  · intro m hm; rw [childrenOf_insertAtIn hnd hpd hne, if_neg hm]
  · intro m
    rw [get?_insertAtIn]
    split
    · next he => rw [he, hnd]; rfl
    · split
      · next he => rw [he, hpd]; rfl
      · rfl
  · intro m d d' hm hm'
    rw [get?_insertAtIn] at hm'
    split at hm'
    · next he =>
      rw [he, hnd] at hm
      cases hm
      cases hm'
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at hm'
      · next he =>
        rw [he, hpd] at hm
        cases hm
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [hm] at hm'
        cases hm'
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## step 7：一つずつ入れる -/

/-- **`insertEach` は `InsertedEach` を満たす。** -/
theorem insertEach_sound : ∀ (ns : List NodeId) {s s' : DOMState} {parent doc : NodeId}
    {child : Option NodeId}, WellFormed s.tree → IsDocument s.tree doc →
    insertEach s parent child doc ns = .ok s' → InsertedEach parent child doc s ns s'
  | [], s, s', parent, doc, child, _, _, h => by
    rw [insertEach] at h
    rw [← Except.ok.inj h]
    exact .nil
  | n :: ns, s, s', parent, doc, child, hwf, hdoc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next sa ha =>
      split at h
      · simp at h
      · next sb hi =>
        obtain ⟨hi', hsb⟩ := DOMState.mapTree_eq_ok hi
        have hwfa := adopt_preserves_wellformed hwf hdoc ha
        have hdoca := hdoc.map (shapePreserving_adopt ha)
        refine .cons (adopt_sound hwf ha) (treeInserted_insertAt hi') ?_ ?_
        · rw [hsb]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩
        · exact insertEach_sound ns (insertAt_preserves_wellformed hwfa hi')
            (hdoca.map (shapePreserving_insertAt hi')) h

/-! ## step 5：live range の調整 -/

/-- **`liveRangeInsertAdjust` は `RangeInsertAdjusted` を満たす。** -/
theorem rangeInsertAdjusted_of_adjust (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (count idx : Nat) (hidx : ChildIndex s.tree child idx) :
    RangeInsertAdjusted s (liveRangeInsertAdjust s parent child count) parent child idx count := by
  cases child with
  | none =>
    refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩, rfl, ?_⟩
    intro i r r' hr hr'
    refine Or.inl ⟨rfl, ?_⟩
    have he : some r = some r' := by rw [← hr]; exact hr'
    exact (Option.some.inj he).symm
  | some c =>
    have hidx' : (index s.tree c).getD 0 = idx := by
      have : index s.tree c = some idx := hidx
      rw [this]; rfl
    have hranges : (liveRangeInsertAdjust s parent (some c) count).ranges =
        s.ranges.map (liveRangeInsertAdjustRange parent idx count) := by
      show (s.ranges.map (liveRangeInsertAdjustRange parent ((index s.tree c).getD 0) count)) = _
      rw [hidx']
    refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩
    · rw [hranges]; exact List.length_map ..
    · intro i r r' hr hr'
      rw [hranges, List.getElem?_map, hr] at hr'
      simp only [Option.map_some, Option.some.injEq] at hr'
      refine Or.inr ⟨by simp, ?_, ?_⟩ <;>
        · rw [← hr']
          unfold liveRangeInsertAdjustRange rangeShiftAfterInsert InsertShifted
          dsimp only
          split
          · next hcond => exact Or.inl ⟨hcond.1, hcond.2, rfl⟩
          · next hcond => exact Or.inr ⟨hcond, rfl⟩

/-! ## child の index は存在する -/

/--
`insert` が成功したなら、`child` は step 5 の時点で `parent` の子である。

step 7 の最初の `insertAt` が「`child` は parent の子」を検査するので、
そこから遡って言える（`adopt` が外すのは入れる node だけである）。
-/
theorem exists_childIndex_of_insertEach {s s' : DOMState} {parent c doc n : NodeId}
    {ns : List NodeId} (hwf : WellFormed s.tree) (hdoc : IsDocument s.tree doc)
    (h : insertEach s parent (some c) doc (n :: ns) = .ok s') :
    ∃ idx, index s.tree c = some idx := by
  rw [insertEach] at h
  split at h
  · simp at h
  · next sa ha =>
    split at h
    · simp at h
    · next sb hi =>
      obtain ⟨hi', -⟩ := DOMState.mapTree_eq_ok hi
      obtain ⟨pd, nd, hpd, hnd, hnp, hanc, hchild, -⟩ := insertAt_ok_cases hi'
      have hmem : c ∈ childrenOf sa.tree parent := by
        rw [childrenOf_eq hpd]
        exact hchild c rfl
      have hpa : parentOf sa.tree c = some parent :=
        parentOf_of_mem_childrenOf (adopt_preserves_wellformed hwf hdoc ha) hmem
      rw [parentOf_adopt ha c] at hpa
      have hcn : c ≠ n := by
        intro he
        rw [if_pos he] at hpa
        simp at hpa
      rw [if_neg hcn] at hpa
      exact index_isSome hwf hpa

/-! ## step 5-9 -/

/-- **`insertNodesAt` は step 5-9 の関係を満たす。** -/
theorem insertNodesAt_sound {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} {b : Bool} (hwf : WellFormed s.tree) (hne : nodes ≠ [])
    (h : insertNodesAt s parent child nodes b = .ok s') :
    ∃ (s₂ s₃ : DOMState) (idx : Nat) (prev : Option NodeId) (pd : NodeData),
      ChildIndex s.tree child idx ∧
      PreviousSiblingOf s.tree parent child prev ∧
      RangeInsertAdjusted s s₂ parent child idx nodes.length ∧
      s.tree.get? parent = some pd ∧
      InsertedEach parent child pd.ownerDocument s₂ nodes s₃ ∧
      TreeRecordQueued s₃ s' parent nodes [] prev child b ∧ ObserverOnly s₃ s' := by
  obtain ⟨s₃, hie, hrec⟩ := insertNodesAt_cases h
  · obtain ⟨pd, hpd, hie⟩ := insertEachAt_cases hie
    · have htree : (liveRangeInsertAdjust s parent child nodes.length).tree = s.tree :=
        liveRangeInsertAdjust_tree ..
      have hpd' : s.tree.get? parent = some pd := by rw [← htree]; exact hpd
      have hdoc : IsDocument s.tree pd.ownerDocument := isDocument_ownerDocument hwf hpd'
      have hdoc₂ : IsDocument (liveRangeInsertAdjust s parent child nodes.length).tree
          pd.ownerDocument := by rw [htree]; exact hdoc
      have hwf₂ : WellFormed (liveRangeInsertAdjust s parent child nodes.length).tree := by
        rw [htree]; exact hwf
      obtain ⟨idx, hidx⟩ : ∃ idx, ChildIndex s.tree child idx := by
        cases child with
        | none => exact ⟨0, rfl⟩
        | some c =>
          cases nodes with
          | nil => exact absurd rfl hne
          | cons n ns =>
            obtain ⟨idx, hx⟩ := exists_childIndex_of_insertEach hwf₂ hdoc₂ hie
            refine ⟨idx, ?_⟩
            show index s.tree c = some idx
            rw [← htree]
            exact hx
      have hins : InsertedEach parent child pd.ownerDocument
          (liveRangeInsertAdjust s parent child nodes.length) nodes s₃ :=
        insertEach_sound nodes hwf₂ hdoc₂ hie
      have hwf₃ : WellFormed s₃.tree := insertEach_preserves_wellformed nodes hwf₂ hdoc₂ hie
      refine ⟨liveRangeInsertAdjust s parent child nodes.length, s₃, idx,
        (child.elim ((childrenOf s.tree parent).getLast?) (fun c => previousSibling s.tree c)),
        pd, hidx, ?_,
        rangeInsertAdjusted_of_adjust s parent child nodes.length idx hidx, hpd', hins, ?_⟩
      · cases child with
        | none => rfl
        | some c => rfl
      · rcases hrec with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
        · rw [hb]
          exact ⟨treeRecordQueued_of_suppress .., ⟨rfl, rfl, rfl, rfl, Untouched.refl _⟩⟩
        · rw [hb]
          have hnodes : ¬(nodes.isEmpty && ([] : List NodeId).isEmpty) := by
            cases nodes with
            | nil => exact absurd rfl hne
            | cons n ns => simp
          refine ⟨?_, ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩⟩
          cases child with
          | none => exact treeRecordQueued_of_queue s₃ hwf₃ parent nodes [] _ none hnodes
          | some c => exact treeRecordQueued_of_queue s₃ hwf₃ parent nodes [] _ (some c) hnodes

/-! ## まとめ -/

/--
**`insert` は `InsertSpec` を満たす。**

step 1-3 は `nodes` の決め方、step 4 は fragment を空にする枝、
step 5-9 は `insertNodesAt_sound` である。
-/
theorem insert_sound {s s' : DOMState} {node parent : NodeId} {child : Option NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : insert s node parent child b = .ok s') :
    InsertSpec s node parent child b s' := by
  obtain ⟨nd, hnd, hcase⟩ := insert_cases h
  clear h
  rcases hcase with ⟨hk, hempty, hsx⟩ | ⟨hk, hne, sr, hre, h⟩ | ⟨hk, h⟩
  · -- step 2-3。children が空なので何もしない。
    exact ⟨nd.children, ⟨nd, hnd, Or.inl ⟨hk, rfl⟩⟩, Or.inl ⟨hempty, hsx⟩⟩
  · have hwfr : WellFormed sr.tree := removeEach_preserves_wellformed _ hwf hre
    have htree : (queueTreeMutationRecord sr node [] nd.children none none).tree
        = sr.tree := queueTreeMutationRecord_tree ..
    have hwf₁ : WellFormed (queueTreeMutationRecord sr node [] nd.children none none).tree := by
      rw [htree]; exact hwfr
    obtain ⟨s₂, s₃, idx, prev, pd, hidx, hprev, hrange, hpd, hins, hrec, hframe⟩ :=
      insertNodesAt_sound hwf₁ hne h
    refine ⟨nd.children, ⟨nd, hnd, Or.inl ⟨hk, rfl⟩⟩, Or.inr ⟨hne, ?_⟩⟩
    refine ⟨queueTreeMutationRecord sr node [] nd.children none none, s₂, s₃, idx, prev, pd,
      ⟨nd, hnd, ?_⟩, hidx, hprev, hrange, hpd, hins, hrec, hframe⟩
    rw [if_pos hk]
    exact ⟨sr, removeEach_sound _ hwf hre,
      treeRecordQueued_of_queue sr hwfr node [] nd.children none none (by
        cases hc : nd.children with
        | nil => exact absurd hc hne
        | cons x xs => simp),
      ⟨by simp, by simp, by simp, by simp, untouched_queueTreeMutationRecord ..⟩⟩
  · obtain ⟨s₂, s₃, idx, prev, pd, hidx, hprev, hrange, hpd, hins, hrec, hframe⟩ :=
      insertNodesAt_sound hwf (by simp) h
    exact ⟨[node], ⟨nd, hnd, Or.inr ⟨hk, rfl⟩⟩,
      Or.inr ⟨by simp, s, s₂, s₃, idx, prev, pd, ⟨nd, hnd, by rw [if_neg hk]⟩,
        hidx, hprev, hrange, hpd, hins, hrec, hframe⟩⟩

end Dom.Spec
