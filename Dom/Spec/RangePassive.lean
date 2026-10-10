import Dom.Mutation.Algorithms
import Dom.CharacterData.ReplaceData
import Dom.Range.Api

/-!
# live range を一つ差し替えても、replace data と remove の進み方は変わらない

replace data と remove は、live range を「木だけで決まる関数を各 range に当てる」形でしか
変えず、ほかの成分の計算に range を読まない。だから `i` 番目の range を `x` に差し替えた状態で
走らせた結果は、元の状態で走らせた結果の `i` 番目を、`x` に同じ調整を当てたもので差し替えたものになる。
調整が `x` を動かさないなら、結果の `i` 番目は `x` のままである。

`deleteContents()` の step 8 は、range を新しい点に置いてから step 9-11（replace data と remove）を
走らせる。実行関数は step 9-11 を先に走らせてから range を置く。二つが同じになることの部品として使う
（`Dom/Spec/RangeDeleteSound.lean`）。
-/

namespace Dom.Spec

open Dom

/-! ## range を読まない更新 -/

theorem queueMutationObserverMicrotask_withRange (s : DOMState) (i : Nat) (x : RangeState) :
    queueMutationObserverMicrotask (withRange s i x) =
      withRange (queueMutationObserverMicrotask s) i x := by
  unfold queueMutationObserverMicrotask withRange
  split <;> rfl

theorem addPendingObserver_withRange (s : DOMState) (i : Nat) (x : RangeState) (mo : Nat) :
    addPendingObserver (withRange s i x) mo = withRange (addPendingObserver s mo) i x := by
  unfold addPendingObserver withRange
  split <;> rfl

theorem foldl_addPendingObserver_withRange (i : Nat) (x : RangeState) :
    ∀ (l : List (Nat × Option String)) (s : DOMState),
      l.foldl (fun st p => addPendingObserver st p.1) (withRange s i x) =
        withRange (l.foldl (fun st p => addPendingObserver st p.1) s) i x
  | [], _ => rfl
  | p :: rest, s => by
    simp only [List.foldl_cons]
    rw [addPendingObserver_withRange]
    exact foldl_addPendingObserver_withRange i x rest _

theorem queueMutationRecord_withRange (s : DOMState) (i : Nat) (x : RangeState)
    (rec : MutationRecord) (ov : Option String) :
    queueMutationRecord (withRange s i x) rec ov = withRange (queueMutationRecord s rec ov) i x := by
  unfold queueMutationRecord
  have hi : interestedObservers (withRange s i x) rec ov = interestedObservers s rec ov := rfl
  simp only [hi]
  rw [← queueMutationObserverMicrotask_withRange, ← foldl_addPendingObserver_withRange]
  rfl

theorem queueTreeMutationRecord_withRange (s : DOMState) (i : Nat) (x : RangeState)
    (target : NodeId) (a r : List NodeId) (p n : Option NodeId) :
    queueTreeMutationRecord (withRange s i x) target a r p n =
      withRange (queueTreeMutationRecord s target a r p n) i x := by
  unfold queueTreeMutationRecord
  split
  · rfl
  · exact queueMutationRecord_withRange ..

theorem queueCharacterDataRecord_withRange (s : DOMState) (i : Nat) (x : RangeState)
    (target : NodeId) (old : String) :
    queueCharacterDataRecord (withRange s i x) target old =
      withRange (queueCharacterDataRecord s target old) i x :=
  queueMutationRecord_withRange ..

theorem addTransientObservers_withRange (s : DOMState) (i : Nat) (x : RangeState)
    (node parent : NodeId) :
    addTransientObservers (withRange s i x) node parent =
      withRange (addTransientObservers s node parent) i x := rfl

theorem iteratorPreRemove_withRange (s : DOMState) (i : Nat) (x : RangeState) (node : NodeId) :
    iteratorPreRemove (withRange s i x) node = withRange (iteratorPreRemove s node) i x := rfl

/-! ## replace data -/

/-- replace data は、対象の node を指さない boundary point を動かさない。 -/
theorem replaceDataAdjustRange_of_ne {n : NodeId} {offset count newLen : Nat} {x : RangeState}
    (hs : x.start.node ≠ n) (he : x.«end».node ≠ n) :
    replaceDataAdjustRange n offset count newLen x = x := by
  unfold replaceDataAdjustRange replaceDataAdjustBP
  simp [hs, he]

/--
**対象の node を指さない range を差し替えても、replace data の結果はその差し替えだけ違う。**
-/
theorem replaceData_withRange {s : DOMState} {i : Nat} {x : RangeState} {n : NodeId}
    {offset count : Nat} {data : String} (hs : x.start.node ≠ n) (he : x.«end».node ≠ n) :
    replaceData (withRange s i x) n offset count data =
      (replaceData s n offset count data).map (fun s' => withRange s' i x) := by
  unfold replaceData
  show (match s.tree.get? n with
    | none => _
    | some d => _) = _
  cases hd : s.tree.get? n with
  | none => rfl
  | some d =>
    dsimp only
    split
    · rfl
    split
    · rfl
    split
    · rfl
    · rename_i spliced _
      simp only [Except.map]
      rw [queueCharacterDataRecord_withRange]
      congr 1
      unfold withRange
      simp only [List.map_set, replaceDataAdjustRange_of_ne hs he]

/-! ## remove -/

/-- live range pre-remove steps が `x` を動かさないこと。 -/
def PreRemoveFixes (t : Tree) (node : NodeId) (x : RangeState) : Prop :=
  ∀ p, parentOf t node = some p →
    liveRangePreRemoveRange t node p ((index t node).getD 0) x = x

theorem liveRangePreRemove_withRange {s : DOMState} {i : Nat} {x : RangeState} {node : NodeId}
    (hfix : PreRemoveFixes s.tree node x) :
    liveRangePreRemove (withRange s i x) node = withRange (liveRangePreRemove s node) i x := by
  unfold liveRangePreRemove
  show (match parentOf s.tree node with
    | none => _
    | some parent => _) = _
  cases hp : parentOf s.tree node with
  | none => rfl
  | some p =>
    dsimp only
    unfold withRange
    simp only [List.map_set, hfix p hp]

theorem detachWithLiveAdjust_withRange {s : DOMState} {i : Nat} {x : RangeState} {node : NodeId}
    (hfix : PreRemoveFixes s.tree node x) :
    detachWithLiveAdjust (withRange s i x) node =
      (detachWithLiveAdjust s node).map (fun s' => withRange s' i x) := by
  unfold detachWithLiveAdjust
  rw [liveRangePreRemove_withRange hfix, iteratorPreRemove_withRange]
  generalize iteratorPreRemove (liveRangePreRemove s node) node = s₀
  unfold DOMState.mapTree
  have ht : (withRange s₀ i x).tree = s₀.tree := rfl
  simp only [ht]
  cases detach s₀.tree node <;> rfl

/--
**pre-remove steps が動かさない range を差し替えても、remove の結果はその差し替えだけ違う。**
-/
theorem remove_withRange {s : DOMState} {i : Nat} {x : RangeState} {node : NodeId} {b : Bool}
    (hfix : PreRemoveFixes s.tree node x) :
    remove (withRange s i x) node b = (remove s node b).map (fun s' => withRange s' i x) := by
  unfold remove
  show (match parentOf s.tree node with
    | none => _
    | some parent => _) = _
  cases hp : parentOf s.tree node with
  | none => rfl
  | some p =>
    dsimp only
    rw [detachWithLiveAdjust_withRange hfix]
    cases detachWithLiveAdjust s node with
    | error e => rfl
    | ok s₁ =>
      simp only [Except.map]
      rw [addTransientObservers_withRange]
      split
      · rfl
      · rw [queueTreeMutationRecord_withRange]
        rfl

/--
**列を順に remove するとき、各段で pre-remove steps が `x` を動かさないなら、
結果は差し替えだけ違う。**

各段の条件は、その段に至るまでの remove を元の状態で走らせた木について述べる。
-/
theorem removeEach_withRange {i : Nat} {x : RangeState} {b : Bool} :
    ∀ (ns : List NodeId) (s : DOMState),
      (∀ pre n post s', ns = pre ++ n :: post → removeEach s pre b = .ok s' →
        PreRemoveFixes s'.tree n x) →
      removeEach (withRange s i x) ns b = (removeEach s ns b).map (fun s' => withRange s' i x)
  | [], s, _ => rfl
  | n :: rest, s, h => by
    unfold removeEach
    have h0 : PreRemoveFixes s.tree n x := h [] n rest s rfl rfl
    rw [remove_withRange h0]
    cases hr : remove s n b with
    | error e => rfl
    | ok s₁ =>
      simp only [Except.map]
      refine removeEach_withRange rest s₁ fun pre m post s' hns hpre => ?_
      refine h (n :: pre) m post s' (by rw [hns]; rfl) ?_
      unfold removeEach
      rw [hr]
      exact hpre

end Dom.Spec
