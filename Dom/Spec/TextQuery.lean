import Dom.Spec.Walker
import Dom.Spec.ReplaceDataSound
import Dom.Query.NodeQuery

/-!
# descendant text content と substring data（§4.4、§4.10）

* `DescendantTextContent t n s`：§4.4 "descendant text content" は、`n` の Text node descendant の data を
  tree order に連結したもの。実行関数 `descendantTextContent` がそれである（`descendantTextContent_spec`）。
* `SubstringResult`：§4.10 "substring data" は、offset が length を超えれば IndexSizeError、そうでなければ
  offset から count（length − offset で切り詰める）code unit を返す。code unit の境界が surrogate pair の途中に
  落ちる場合は、model の対象外として `outsideModel` を返す（`substringData_result_sound`）。
-/

namespace Dom.Spec

open Dom

/-- node の data（木に無ければ空）。 -/
def dataOf (t : Tree) (x : NodeId) : String := ((t.get? x).map NodeData.data).getD ""

/-- §4.4 "descendant text content"。 -/
def DescendantTextContent (t : Tree) (n : NodeId) (s : String) : Prop :=
  ∃ l : List NodeId, l.Pairwise (PrecedesStruct t) ∧
    (∀ x, x ∈ l ↔ Ancestor t n x ∧ ∃ d, t.get? x = some d ∧ d.kind.isText = true) ∧
    s = String.join (l.map (dataOf t))

theorem descendantTextContent_spec {t : Tree} (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : DescendantTextContent t n (descendantTextContent t n) := by
  let isTextNode : NodeId → Bool := fun x =>
    match t.get? x with
    | none => false
    | some d => d.kind.isText
  refine ⟨((preorder t n).drop 1).filter isTextNode, ?_, ?_, ?_⟩
  · exact ((treeOrderList_preorder hwf hn).2.sublist (List.drop_sublist _ _)).filter _
  · intro x
    rw [List.mem_filter, mem_preorder_drop_one hwf hn]
    apply and_congr_right
    intro _
    simp only [isTextNode]
    cases h : t.get? x <;> simp
  · unfold descendantTextContent
    show _ = String.join _
    generalize (preorder t n).drop 1 = l
    have key : ∀ (acc : String) (l : List NodeId),
        (l.filterMap fun x =>
          match t.get? x with
          | none => none
          | some d => if d.kind.isText then some d.data else none).foldl (· ++ ·) acc =
        acc ++ String.join ((l.filter isTextNode).map (dataOf t)) := by
      intro acc l
      induction l generalizing acc with
      | nil => simp [String.join]
      | cons x l ih =>
        cases h : t.get? x with
        | none => simp [h, isTextNode, ih]
        | some dx =>
          by_cases ht : dx.kind.isText = true
          · simp [h, ht, isTextNode, ih, dataOf, String.append_assoc]
          · simp [h, ht, isTextNode, ih]
    exact (key "" l).trans String.empty_append

/-! ## substring data -/

/-- §4.10 "substring data"（CharacterData の node に対して）。 -/
def SubstringResult (t : Tree) (n : NodeId) (offset count : Nat) (r : Except DOMException String) :
    Prop :=
  ∃ d, t.get? n = some d ∧ d.kind.isCharacterData = true ∧
    ((d.length < offset ∧ r = .error .indexSizeError) ∨
     (offset ≤ d.length ∧ ∃ c, ClampedCount d.length offset count c ∧
       ((∃ pre mid post : List Char, d.data.toList = pre ++ mid ++ post ∧
          Utf16.lengthOfList pre = offset ∧ Utf16.lengthOfList mid = c ∧
          r = .ok (String.ofList mid)) ∨
        ((¬ ∃ pre mid post : List Char, d.data.toList = pre ++ mid ++ post ∧
          Utf16.lengthOfList pre = offset ∧ Utf16.lengthOfList mid = c) ∧
          r = .error .outsideModel))))

theorem substringData_result_sound {t : Tree} {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.isCharacterData = true) (offset count : Nat) :
    SubstringResult t n offset count (substringData t n offset count) := by
  refine ⟨d, hn, hk, ?_⟩
  unfold substringData
  rw [hn]
  simp only [hk, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hlt : d.length < offset
  · rw [if_pos (by simpa using hlt)]
    exact Or.inl ⟨hlt, rfl⟩
  · rw [if_neg (by simpa using hlt)]
    refine Or.inr ⟨by omega, adjustedCount d.length offset count,
      clampedCount_adjustedCount _ _ _, ?_⟩
    cases h1 : Utf16.splitAt? d.data.toList offset with
    | none =>
      refine Or.inr ⟨?_, rfl⟩
      rintro ⟨pre, mid, post, hs, hpre, -⟩
      have := Utf16.splitAt?_of_split pre (mid ++ post)
      rw [hpre, ← List.append_assoc, ← hs, h1] at this
      cases this
    | some p =>
      obtain ⟨pre, rest⟩ := p
      obtain ⟨hpr, hpl⟩ := Utf16.splitAt?_spec h1
      simp only
      cases h2 : Utf16.splitAt? rest (adjustedCount d.length offset count) with
      | none =>
        refine Or.inr ⟨?_, rfl⟩
        rintro ⟨pre', mid, post, hs, hpre', hmid⟩
        have h1' := Utf16.splitAt?_of_split pre' (mid ++ post)
        rw [hpre', ← List.append_assoc, ← hs, h1] at h1'
        simp only [Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨-, rfl⟩ := h1'
        have := Utf16.splitAt?_of_split mid post
        rw [hmid, h2] at this
        cases this
      | some q =>
        obtain ⟨mid, post⟩ := q
        obtain ⟨hmr, hml⟩ := Utf16.splitAt?_spec h2
        refine Or.inl ⟨pre, mid, post, ?_, hpl, hml, rfl⟩
        rw [← hpr, ← hmr, List.append_assoc]

end Dom.Spec
