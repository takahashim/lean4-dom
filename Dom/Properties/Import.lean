import Dom.Mutation.Import
import Dom.Properties.Clone

/-!
# `importNode` と `adoptNode` の性質

同じ「別の document の node を使えるようにする」でも、identity の扱いが正反対である。
それをそのまま定理にする。

| | 返る id | 原本 | node document |
| --- | --- | --- | --- |
| `importNode` | 新しい（`importNode_ne`） | 動かない（`importNode_keep`） | `doc`（`importNode_ownerDocument`） |
| `adoptNode` | 渡したもの（`adoptNode_id`） | それ自身が移る（`adoptNode_detached`） | `doc`（`adoptNode_ownerDocument`） |
-/

namespace Dom

/-! ## `importNode` -/

theorem importNode_cases {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    (h : importNode s doc n subtree = .ok (c, s')) :
    ∃ dd d, s.tree.get? doc = some dd ∧ dd.kind = .document ∧
      s.tree.get? n = some d ∧ d.kind ≠ NodeKind.document ∧
      cloneNodeIn s n doc subtree = .ok (c, s') := by
  unfold importNode at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    split at h
    · simp at h
    · next d hd =>
      split at h
      · simp at h
      · next hkd => exact ⟨dd, d, hdd, hk, hd, by simpa using hkd, h⟩

theorem importNode_isDocument {s : DOMState} {doc : NodeId} {dd : NodeData}
    (hdd : s.tree.get? doc = some dd) (hk : dd.kind = NodeKind.document) :
    IsDocument s.tree doc := ⟨dd, hdd, hk⟩

/-- **`importNode` は妥当性を保つ。** -/
theorem admissible_importNode {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (h : importNode s doc n subtree = .ok (c, s')) :
    AdmissibleDOMState s' := by
  obtain ⟨dd, d, hdd, hk, -, -, hcl⟩ := importNode_cases h
  exact admissible_cloneNodeIn hv (importNode_isDocument hdd hk) hcl

/-- **`importNode` が返すのは新しい node である。** 原本とは別の id を持つ。 -/
theorem importNode_ne {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (h : importNode s doc n subtree = .ok (c, s')) : c ≠ n := by
  obtain ⟨dd, d, hdd, hk, -, -, hcl⟩ := importNode_cases h
  exact cloneNodeIn_ne hv (importNode_isDocument hdd hk) hcl

/-- **`importNode` は原本を動かさない。** -/
theorem importNode_keep {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (h : importNode s doc n subtree = .ok (c, s'))
    {m : NodeId} {md : NodeData} (hm : s.tree.get? m = some md) :
    s'.tree.get? m = some md := by
  obtain ⟨dd, d, hdd, hk, -, -, hcl⟩ := importNode_cases h
  exact cloneNodeIn_keep hv (importNode_isDocument hdd hk) hcl hm

/-- **`importNode` は live range を動かさない。** -/
theorem importNode_ranges {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (h : importNode s doc n subtree = .ok (c, s')) :
    s'.ranges = s.ranges := by
  obtain ⟨dd, d, hdd, hk, -, -, hcl⟩ := importNode_cases h
  exact cloneNodeIn_ranges hv (importNode_isDocument hdd hk) hcl

/-- **`importNode` が返す copy の node document は受け手の document である。** -/
theorem importNode_ownerDocument {s s' : DOMState} {doc n c : NodeId} {subtree : Bool}
    {cd : NodeData} (hv : AdmissibleDOMState s)
    (h : importNode s doc n subtree = .ok (c, s')) (hcd : s'.tree.get? c = some cd) :
    cd.ownerDocument = doc := by
  obtain ⟨dd, d, hdd, hk, hd, hkd, hcl⟩ := importNode_cases h
  exact cloneNodeIn_ownerDocument hv (importNode_isDocument hdd hk) hd hkd hcl hcd

/-- **`importNode(node, true)` の copy は原本と同じ形である。** -/
theorem importNode_cloneOf {s s' : DOMState} {doc n c : NodeId}
    (hv : AdmissibleDOMState s) (h : importNode s doc n true = .ok (c, s')) :
    CloneOf s'.tree c n := by
  obtain ⟨dd, d, hdd, hk, -, -, hcl⟩ := importNode_cases h
  exact cloneNodeIn_cloneOf hv (importNode_isDocument hdd hk) hcl

/-! ## `adoptNode` -/

theorem adoptNode_cases {s s' : DOMState} {doc n m : NodeId}
    (h : adoptNode s doc n = .ok (m, s')) :
    ∃ dd d, s.tree.get? doc = some dd ∧ dd.kind = NodeKind.document ∧
      s.tree.get? n = some d ∧ d.kind ≠ NodeKind.document ∧ m = n ∧
      adopt s n doc = .ok s' := by
  unfold adoptNode at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    split at h
    · simp at h
    · next d hd =>
      split at h
      · simp at h
      · next hkd =>
        split at h
        · simp at h
        · next s₁ ha =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨dd, d, hdd, hk, hd, by simpa using hkd, rfl, ha⟩

/-- **`adoptNode` が返すのは渡した node そのものである。** copy は作らない。 -/
theorem adoptNode_id {s s' : DOMState} {doc n m : NodeId}
    (h : adoptNode s doc n = .ok (m, s')) : m = n := by
  obtain ⟨-, -, -, -, -, -, he, -⟩ := adoptNode_cases h
  exact he

/-- **`adoptNode` は妥当性を保つ。** -/
theorem admissible_adoptNode {s s' : DOMState} {doc n m : NodeId}
    (hv : AdmissibleDOMState s) (h : adoptNode s doc n = .ok (m, s')) :
    AdmissibleDOMState s' := by
  obtain ⟨dd, d, hdd, hk, hd, hkd, -, ha⟩ := adoptNode_cases h
  refine admissible_adopt hv ⟨dd, hdd, hk⟩ ?_ ha
  intro nd hnd
  rw [hd] at hnd
  cases hnd
  exact hkd

/-- **`adoptNode` の後、node の node document は受け手の document である。** -/
theorem adoptNode_ownerDocument {s s' : DOMState} {doc n m : NodeId}
    (hv : AdmissibleDOMState s) (h : adoptNode s doc n = .ok (m, s')) :
    ownerDocumentOf s'.tree n = some doc := by
  obtain ⟨-, -, -, -, -, -, -, ha⟩ := adoptNode_cases h
  exact adopt_ownerDocument_self hv.wellFormed ha

/-- **`adoptNode` の後、node は元の親から外れている。** -/
theorem adoptNode_detached {s s' : DOMState} {doc n m : NodeId}
    (h : adoptNode s doc n = .ok (m, s')) : parentOf s'.tree n = none := by
  obtain ⟨-, -, -, -, -, -, -, ha⟩ := adoptNode_cases h
  obtain ⟨s₀, hstep, hfinal⟩ := adopt_ok_cases ha
  have hnp₀ : parentOf s₀.tree n = none := by
    rcases hstep with ⟨hn, rfl⟩ | hrm
    · exact hn
    · exact remove_parentOf hrm
  rcases hfinal with rfl | rfl
  · exact hnp₀
  · rw [DOMState.withTree_tree, parentOf_setOwnerDocument]
    exact hnp₀

/-- **`adoptNode` は node の形を変えない。** kind も attribute も名前もそのままである。 -/
theorem adoptNode_shape {s s' : DOMState} {doc n m : NodeId}
    (h : adoptNode s doc n = .ok (m, s')) : ShapePreserving s.tree s'.tree := by
  obtain ⟨-, -, -, -, -, -, -, ha⟩ := adoptNode_cases h
  exact shapePreserving_adopt ha

end Dom
