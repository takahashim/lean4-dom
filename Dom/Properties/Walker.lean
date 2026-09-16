import Dom.Traversal.TreeWalker
import Dom.Properties.Tree

/-!
# TreeWalker の性質

§6.2 の走査はどれも「木の中の node」を返す、というのがここで示すことである。
それだけで `WalkersValid`（root と current が木にある）は保たれる。

**強いほうの不変条件は成り立たない。** `NodeIterator` の `ValidIterator` は
reference が root の inclusive descendant であることまで要求できるが、
§6.2 には "removing steps" が無いので、remove は `current` を root の外へ出す。
それは仕様どおりの挙動なので、`ValidWalker` には入れていない
（`docs/status.md` の TreeWalker の節）。
-/

namespace Dom

open Dom.ListUtil

variable {t : Tree}

theorem exists_data_of_ancestor (hwf : WellFormed t) {a n : NodeId} (h : Ancestor t a n) :
    ∃ d, t.get? a = some d := by
  induction h with
  | step hp => exact exists_data_of_parentOf hwf hp
  | trans _ _ ih => exact ih

theorem mem_takeUntilIncl {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ takeUntilIncl p l → x ∈ l
  | [], h => by simp [takeUntilIncl] at h
  | a :: rest, h => by
    unfold takeUntilIncl at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · simp at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_takeUntilIncl h)

/-- `preorder` から取り出した node は木にある。 -/
theorem exists_data_of_mem_preorder' {n x : NodeId} (h : x ∈ preorder t n) :
    ∃ d, t.get? x = some d :=
  exists_data_of_mem_preorderFuel _ n x h

theorem exists_data_of_mem_mirrorPreorder {n x : NodeId} (h : x ∈ mirrorPreorder t n) :
    ∃ d, t.get? x = some d :=
  exists_data_of_mem_preorder' ((mem_mirrorPreorder_iff_mem_preorder n x).mp h)

/-! ## それぞれの走査が返す node は木にある -/

theorem exists_data_of_walkerNextNode {w : WalkerState} {n : NodeId}
    (h : walkerNextNode t w = some n) : ∃ d, t.get? n = some d := by
  unfold walkerNextNode at h
  split at h
  · simp at h
  · next before after hs =>
    have hmem : n ∈ after := List.mem_of_find?_eq_some h
    have := splitAt?_eq_some hs
    exact exists_data_of_mem_preorder' (by rw [this]; simp [hmem])

theorem exists_data_of_walkerPreviousNode {w : WalkerState} {n : NodeId}
    (h : walkerPreviousNode t w = some n) : ∃ d, t.get? n = some d := by
  unfold walkerPreviousNode at h
  split at h
  · simp at h
  · next before after hs =>
    have hmem : n ∈ before := List.mem_reverse.mp (List.mem_of_find?_eq_some h)
    have := splitAt?_eq_some hs
    exact exists_data_of_mem_preorder' (by rw [this]; simp [hmem])

theorem exists_data_of_walkerFirstChild {w : WalkerState} {n : NodeId}
    (h : walkerFirstChild t w = some n) : ∃ d, t.get? n = some d := by
  unfold walkerFirstChild at h
  exact exists_data_of_mem_preorder' (List.drop_subset 1 _ (List.mem_of_find?_eq_some h))

theorem exists_data_of_walkerLastChild {w : WalkerState} {n : NodeId}
    (h : walkerLastChild t w = some n) : ∃ d, t.get? n = some d := by
  unfold walkerLastChild at h
  exact exists_data_of_mem_mirrorPreorder (List.drop_subset 1 _ (List.mem_of_find?_eq_some h))

theorem exists_data_of_walkerParentNode (hwf : WellFormed t) {w : WalkerState} {n : NodeId}
    (h : walkerParentNode t w = some n) : ∃ d, t.get? n = some d := by
  unfold walkerParentNode at h
  split at h
  · simp at h
  · have hmem := mem_takeUntilIncl (List.mem_of_find?_eq_some h)
    exact exists_data_of_ancestor hwf ((mem_ancestors_iff hwf _ n).mp hmem)

theorem exists_data_of_mem_siblingCandidates {n x : NodeId} {after : Bool}
    (h : x ∈ siblingCandidates t n after) : ∃ d, t.get? x = some d := by
  unfold siblingCandidates at h
  obtain ⟨s, -, hx⟩ := List.mem_flatMap.mp h
  split at hx
  · exact exists_data_of_mem_preorder' hx
  · exact exists_data_of_mem_mirrorPreorder hx

theorem exists_data_of_walkerSiblingSearch {w : WalkerState} {after : Bool} {n : NodeId} :
    ∀ (chain : List NodeId), walkerSiblingSearch t w after chain = some n →
      ∃ d, t.get? n = some d
  | [], h => by simp [walkerSiblingSearch] at h
  | [m], h => by
    rw [walkerSiblingSearch] at h
    exact exists_data_of_mem_siblingCandidates (List.mem_of_find?_eq_some h)
  | m :: p :: rest, h => by
    rw [walkerSiblingSearch] at h
    split at h
    · next x hx =>
      rw [← Option.some.inj h]
      exact exists_data_of_mem_siblingCandidates (List.mem_of_find?_eq_some hx)
    · split at h
      · simp at h
      · exact exists_data_of_walkerSiblingSearch (p :: rest) h

theorem exists_data_of_walkerSibling {w : WalkerState} {after : Bool} {n : NodeId}
    (h : walkerSibling t w after = some n) : ∃ d, t.get? n = some d := by
  unfold walkerSibling at h
  split at h
  · simp at h
  · exact exists_data_of_walkerSiblingSearch _ h

/-- どの method も、返すのは木の中の node である。 -/
theorem exists_data_of_walkerMethod (hwf : WellFormed t) {m : WalkerMethod} {w : WalkerState}
    {n : NodeId} (h : walkerMethod m t w = some n) : ∃ d, t.get? n = some d := by
  cases m with
  | parentNode => exact exists_data_of_walkerParentNode hwf h
  | firstChild => exact exists_data_of_walkerFirstChild h
  | lastChild => exact exists_data_of_walkerLastChild h
  | previousSibling => exact exists_data_of_walkerSibling h
  | nextSibling => exact exists_data_of_walkerSibling h
  | previousNode => exact exists_data_of_walkerPreviousNode h
  | nextNode => exact exists_data_of_walkerNextNode h

/-! ## 実行時の検査の健全性・完全性 -/

/--
**`checkValidWalker` は `ValidWalker` を決定する。**

harness（`Dom/Exec/Eval.lean`）は `checkWalkersValid` で scenario を弾くので、
これが `WalkersValid` と一致していないと、受理すべき状態を落としたり
その逆をしたりする。`checkWellFormed_iff` や `checkAdmissibleDOMState_iff` と
同じ位置づけの定理である。
-/
theorem checkValidWalker_iff (t : Tree) (w : WalkerState) :
    checkValidWalker t w = true ↔ ValidWalker t w := by
  unfold checkValidWalker ValidWalker
  rw [Bool.and_eq_true, Option.isSome_iff_exists, Option.isSome_iff_exists]

theorem checkWalkersValid_iff (s : DOMState) :
    checkWalkersValid s = true ↔ WalkersValid s := by
  unfold checkWalkersValid WalkersValid
  rw [List.all_eq_true]
  constructor
  · intro h w hw
    exact (checkValidWalker_iff s.tree w).mp (h w hw)
  · intro h w hw
    exact (checkValidWalker_iff s.tree w).mpr (h w hw)

/-! ## `WalkersValid` の保存 -/

/--
走査は `WalkersValid` を保つ。

`f` が返す node が木にあることだけが要る。
-/
theorem walkersValid_walkerRun {s s' : DOMState} {i : Nat} {r : Option NodeId}
    {f : Tree → WalkerState → Option NodeId}
    (hf : ∀ w n, f s.tree w = some n → ∃ d, s.tree.get? n = some d)
    (h : WalkersValid s) (hr : walkerRun s i f = .ok (r, s')) : WalkersValid s' := by
  unfold walkerRun at hr
  split at hr
  · simp at hr
  · next w hw =>
    split at hr
    · have : s' = s := ((Prod.mk.injEq ..).mp (Except.ok.inj hr)).2.symm
      rw [this]; exact h
    · next n hn =>
      have hs' : s' = withWalker s i { w with current := n } :=
        ((Prod.mk.injEq ..).mp (Except.ok.inj hr)).2.symm
      rw [hs']
      intro v hv
      rcases mem_set s.walkers i { w with current := n } v hv with rfl | hmem
      · exact ⟨(h w (List.mem_of_getElem? hw)).1, hf w n hn⟩
      · exact h v hmem

/-- **`TreeWalker` の走査は `WalkersValid` を保つ。** -/
theorem walkersValid_walkerStep {s s' : DOMState} {i : Nat} {m : WalkerMethod} {r : Option NodeId}
    (hwf : WellFormed s.tree) (h : WalkersValid s) (hs : walkerStep s i m = .ok (r, s')) :
    WalkersValid s' :=
  walkersValid_walkerRun (fun _ _ hn => exists_data_of_walkerMethod hwf hn) h hs

end Dom
