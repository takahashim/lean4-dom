import Dom.Spec.Validity

/-!
# `move` の pre-move validity の関係意味論（§4.2.4）

`Dom/Properties/MoveContract.lean` の `moveBefore_error_iff` は失敗側を実行側の
`moveValidity` に委ねていた。`Dom/Spec/Validity.lean` が `PreInsertResult` について
した仕事と同じで、仕様の step 1-6 を読み違えて実装しても関係がその実装に合わせて
成り立つので、例外の種類については何も保証しない。

ここでは step 1-6 の条件を、`PreInsertValidity` と同じ `Step` / `Return` / `Branch` /
`Done` の combinator を使って、**実行側の関数を呼ばずに**書く。条件は `Dom/Basic/` の
語彙と `Dom/Spec/Validity.lean` が既に独立に定義した語彙
（`InTree` / `InclusiveAncestor` / `ChildIsChildOf` / `IsText` / `IsCharacterData` /
`KindIs`）だけで書く。`elementChildren` や `doctypeAtOrAfter` のような実行側の
helper は使わない。

## step の対応

`docs/spec-version.md` が pin する commit の "To move a node" algorithm、
pre-move validity checks の六つ（`dom.bs` の該当箇所は該当節を参照）。

1. `newParent` と `node` の root が同じであること。
2. `node` が `newParent` の inclusive ancestor でないこと。
3. `child` が非 null なら、その parent が `newParent` であること。
4. `node` が Element または CharacterData であること。
5. `node` が Text で `newParent` が Document なら弾く。
6. `newParent` が Document・`node` が Element で、`newParent` が既に element の子を
   持つか、`child` が doctype かその後ろに doctype があるなら弾く。

先頭の二つ（`newParent` と `node` が木にあること）は model の追加で、
`PreInsertValidity` と同じ理由による（仕様の algorithm は node object を
受け取るので存在を前提にしている）。

## step 6 は `ElementInsertionBlocked` の使い回しではない

`ensure pre-insert validity` の step 9.1（`ElementInsertionBlocked`）と概念は同じだが、
`excl`（fragment の子を除外する引数）を持たない。`move` が動かすのは常に一個の node
（step 4 が DocumentFragment を弾く）で、fragment を展開しないので要らない。
別の名前（`MoveElementInsertionBlocked`）で置く。
-/

namespace Dom.Spec

open Dom

/-! ## 条件の語彙 -/

/-- step 4。`node` が Element または CharacterData であること。 -/
def IsElementOrCharacterData (t : Tree) (n : NodeId) : Prop :=
  KindIs t n .element ∨ IsCharacterData t n

/--
step 6。`newParent` が Document で `node` が Element のときに弾く二条件。

`ElementInsertionBlocked` と違って `excl` を持たない（`move` は fragment を
展開しない）。
-/
def MoveElementInsertionBlocked (t : Tree) (parent : NodeId) (child : Option NodeId) : Prop :=
  HasChildOfKind t parent .element ∨
    (∃ c, child = some c ∧ (KindIs t c .documentType ∨ DoctypeFollowing t parent c))

/-! ## 全体 -/

/--
**§4.2.4 "move" の pre-move validity（step 1-6）の関係意味論。**

仕様の `<ol>` の先頭六つをそのまま写した形である。
-/
def MoveValidity (t : Tree) (node newParent : NodeId) (child : Option NodeId) :
    Except DOMException Unit → Prop :=
  -- model の追加：newParent と node が木にあること
  Step (¬ InTree t newParent) .notFoundError <|
  Step (¬ InTree t node) .notFoundError <|
  -- step 1
  Step (root t newParent ≠ root t node) .hierarchyRequestError <|
  -- step 2
  Step (InclusiveAncestor t node newParent) .hierarchyRequestError <|
  -- step 3
  Step (¬ ChildIsChildOf t child newParent) .notFoundError <|
  -- step 4
  Step (¬ IsElementOrCharacterData t node) .hierarchyRequestError <|
  -- step 5
  Step (IsText t node ∧ KindIs t newParent .document) .hierarchyRequestError <|
  -- step 6
  Step (KindIs t newParent .document ∧ KindIs t node .element ∧
        MoveElementInsertionBlocked t newParent child) .hierarchyRequestError
  Done

/-! ## 実行側との橋

条件が実行側の判定と一致することを言う。**関係の定義は実行側を呼ばないが、
橋の定理は両方に触れてよい**（`ruby test/spec_dependence.rb` が見るのは `def` の
本体だけである）。
-/

theorem isElementOrCharacterData_iff {t : Tree} {n : NodeId} {d : NodeData}
    (h : t.get? n = some d) :
    IsElementOrCharacterData t n ↔ (d.kind = .element ∨ d.kind.isCharacterData = true) := by
  unfold IsElementOrCharacterData KindIs IsCharacterData
  rw [h]
  simp

/-- `MoveElementInsertionBlocked` は `moveValidity` の step 6 の boolean 式と一致する。 -/
theorem moveElementInsertionBlocked_iff {t : Tree} {parent : NodeId} {child : Option NodeId} :
    MoveElementInsertionBlocked t parent child ↔
      (!(elementChildren t parent).isEmpty || doctypeAtOrAfter t parent child) = true := by
  unfold MoveElementInsertionBlocked doctypeAtOrAfter
  rw [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ← hasElementChild_iff]
  refine or_congr Iff.rfl ?_
  cases child with
  | none => simp
  | some c =>
    simp only [Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨c', hc', h⟩
      cases hc'
      rcases h with h | h
      · exact Or.inl (kindIs_iff.mp h)
      · exact Or.inr (doctypeFollowing_iff.mp h)
    · rintro (h | h)
      · exact ⟨c, rfl, Or.inl (kindIs_iff.mpr h)⟩
      · exact ⟨c, rfl, Or.inr (doctypeFollowing_iff.mpr h)⟩

/--
**関係は結果を一つに決める。**

combinator ごとの補題を組むだけである。`PreInsertValidity` と同じ形。
-/
theorem moveValidity_deterministic (t : Tree) (node newParent : NodeId)
    (child : Option NodeId) : Deterministic (MoveValidity t node newParent child) :=
  Step_deterministic <| Step_deterministic <| Step_deterministic <| Step_deterministic <|
  Step_deterministic <| Step_deterministic <| Step_deterministic <|
  Step_deterministic Done_deterministic

/-! ## soundness -/

/--
**`moveValidity` の結果は、成否によらず関係を満たす。**

仮定を置かないので、「どの入力でどの例外を返すか」まで関係が決めることになる。
`WellFormed` が要るのは step 2（`isInclusiveAncestorOf` と `InclusiveAncestor` の対応）
だけである。
-/
theorem moveValidity_spec {t : Tree} (hwf : WellFormed t) (node newParent : NodeId)
    (child : Option NodeId) :
    MoveValidity t node newParent child (moveValidity t node newParent child) := by
  unfold MoveValidity moveValidity Step Done
  cases hpd : t.get? newParent with
  | none => exact Or.inl ⟨by rw [inTree_iff, hpd]; simp, rfl⟩
  | some pd =>
  simp only []
  refine Or.inr ⟨by rw [inTree_iff, hpd]; simp, ?_⟩
  cases hnd : t.get? node with
  | none => exact Or.inl ⟨by rw [inTree_iff, hnd]; simp, rfl⟩
  | some nd =>
  simp only []
  refine Or.inr ⟨by rw [inTree_iff, hnd]; simp, ?_⟩
  -- step 1
  by_cases h1 : root t newParent ≠ root t node
  · rw [if_pos h1]
    exact Or.inl ⟨h1, rfl⟩
  · rw [if_neg h1]
    refine Or.inr ⟨h1, ?_⟩
    -- step 2
    by_cases h2 : isInclusiveAncestorOf t node newParent = true
    · rw [if_pos h2]
      exact Or.inl ⟨(isInclusiveAncestorOf_iff hwf node newParent).mp h2, rfl⟩
    · rw [if_neg h2]
      refine Or.inr ⟨fun hq => h2 ((isInclusiveAncestorOf_iff hwf node newParent).mpr hq), ?_⟩
      -- step 3
      by_cases h3 : childHasParent t child newParent = true
      · rw [if_neg (by simp [h3])]
        refine Or.inr ⟨not_not_intro (childIsChildOf_iff.mpr h3), ?_⟩
        -- step 4
        by_cases h4 : (nd.kind = .element ∨ nd.kind.isCharacterData = true)
        · have hb4 : (nd.kind == .element || nd.kind.isCharacterData) = true := by
            rcases h4 with h | h <;> simp [h]
          rw [if_neg (by simp [hb4])]
          have hnn4 : ¬¬IsElementOrCharacterData t node := by
            rw [isElementOrCharacterData_iff hnd]; exact fun hq => hq h4
          refine Or.inr ⟨hnn4, ?_⟩
          -- step 5
          by_cases h5 : (nd.kind.isText && pd.kind == .document) = true
          · rw [if_pos h5]
            rw [Bool.and_eq_true, beq_iff_eq] at h5
            exact Or.inl ⟨⟨(isText_iff hnd).mpr h5.1,
              kindIs_iff.mpr (by rw [kindOf_of_get? hpd]; exact congrArg some h5.2)⟩, rfl⟩
          · rw [if_neg h5]
            refine Or.inr ⟨?_, ?_⟩
            · rintro ⟨ht, hdoc⟩
              refine h5 ?_
              rw [Bool.and_eq_true, beq_iff_eq]
              refine ⟨(isText_iff hnd).mp ht, ?_⟩
              have := kindIs_iff.mp hdoc
              rw [kindOf_of_get? hpd] at this
              exact Option.some.inj this
            · -- step 6
              by_cases h6 : (pd.kind == .document && nd.kind == .element &&
                  (!(elementChildren t newParent).isEmpty ||
                    doctypeAtOrAfter t newParent child)) = true
              · rw [if_pos h6]
                rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h6
                obtain ⟨⟨hpdoc, helt⟩, hblk⟩ := h6
                have hpdoc' : KindIs t newParent .document := by
                  rw [kindIs_iff, kindOf_of_get? hpd]; exact congrArg some hpdoc
                have helt' : KindIs t node .element := by
                  rw [kindIs_iff, kindOf_of_get? hnd]; exact congrArg some helt
                exact Or.inl ⟨⟨hpdoc', helt', moveElementInsertionBlocked_iff.mpr hblk⟩, rfl⟩
              · rw [if_neg h6]
                refine Or.inr ⟨?_, rfl⟩
                rintro ⟨hpdoc, helt, hblk⟩
                refine h6 ?_
                rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
                refine ⟨⟨?_, ?_⟩, moveElementInsertionBlocked_iff.mp hblk⟩
                · have := kindIs_iff.mp hpdoc
                  rw [kindOf_of_get? hpd] at this
                  exact Option.some.inj this
                · have := kindIs_iff.mp helt
                  rw [kindOf_of_get? hnd] at this
                  exact Option.some.inj this
        · have hb4 : (nd.kind == .element || nd.kind.isCharacterData) = false := by
            rw [not_or] at h4
            rw [Bool.or_eq_false_iff]
            exact ⟨beq_eq_false_iff_ne.mpr h4.1, by simpa using h4.2⟩
          have hnb4 : ¬IsElementOrCharacterData t node := by
            rw [isElementOrCharacterData_iff hnd]; exact h4
          rw [if_pos (by rw [Bool.not_eq_true']; exact hb4)]
          exact Or.inl ⟨hnb4, rfl⟩
      · rw [if_pos (by simp [h3])]
        exact Or.inl ⟨fun hq => h3 (childIsChildOf_iff.mp hq), rfl⟩

/--
**関係を満たす結果は、実行関数の結果そのものである。**

soundness（仮定なし）と一意性を繋いだもの。
-/
theorem moveValidity_eq_of_spec {t : Tree} (hwf : WellFormed t)
    {node newParent : NodeId} {child : Option NodeId} {r : Except DOMException Unit}
    (h : MoveValidity t node newParent child r) :
    r = moveValidity t node newParent child :=
  moveValidity_deterministic t node newParent child _ _ h
    (moveValidity_spec hwf node newParent child)

/-- **関係と実行関数は同じ結果を指す。** 上の二つを繋いだ形。 -/
theorem moveValidity_iff {t : Tree} (hwf : WellFormed t)
    {node newParent : NodeId} {child : Option NodeId} {r : Except DOMException Unit} :
    MoveValidity t node newParent child r ↔ moveValidity t node newParent child = r := by
  constructor
  · intro h; exact (moveValidity_eq_of_spec hwf h).symm
  · intro h; rw [← h]; exact moveValidity_spec hwf node newParent child

end Dom.Spec
