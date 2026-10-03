import Dom.Spec.RangeQuery

/-!
# Range の端点を動かす method の関係意味論（§5.5）

`setStart` / `setEnd`、`setStartBefore` ほかの sibling setter、`collapse`、`selectNode`、
`selectNodeContents` を、例外まで含めた関係で書き、実行関数の結果と**等しい**ことを示す。

「set the start / end」の step 4-5 は、§5.3 の `BPBefore` と range の root で書く。
range の root は start node の root である。実行関数の `setStart` は新しい端点の root を
end node の root と比べているが、妥当な range（`RangeValid`）では start と end の root は等しいので、
定理はそれを仮定する。
-/

namespace Dom.Spec

open Dom

variable {t : Tree}

/-! ## 関係 -/

/-- "set the start or end" の step 1-2（と、node が木に無いという model の都合）。 -/
def BoundaryPointError (t : Tree) (bp : BoundaryPoint) (e : DOMException) : Prop :=
  (t.get? bp.node = none ∧ e = .notFoundError) ∨
    (∃ d, t.get? bp.node = some d ∧ d.kind = .documentType ∧ e = .invalidNodeTypeError) ∨
    (∃ d, t.get? bp.node = some d ∧ d.kind ≠ .documentType ∧ d.length < bp.offset ∧
      e = .indexSizeError)

/-- step 1-2 を通ること。 -/
def BoundaryPointOk (t : Tree) (bp : BoundaryPoint) : Prop :=
  ∃ d, t.get? bp.node = some d ∧ d.kind ≠ .documentType ∧ bp.offset ≤ d.length

/--
"set the start" の step 4。range の root が node の root でないか、bp が end の isAfter なら、
end も bp にする。start は bp にする。
-/
def StartSet (t : Tree) (r : RangeState) (bp : BoundaryPoint) (r' : RangeState) : Prop :=
  ((root t r.start.node ≠ root t bp.node ∨ BPBefore t r.«end» bp) ∧ r' = ⟨bp, bp⟩) ∨
    (¬ (root t r.start.node ≠ root t bp.node ∨ BPBefore t r.«end» bp) ∧ r' = { r with start := bp })

/-- "set the end" の step 5。bp が start の before なら start も bp にする。 -/
def EndSet (t : Tree) (r : RangeState) (bp : BoundaryPoint) (r' : RangeState) : Prop :=
  ((root t r.start.node ≠ root t bp.node ∨ BPBefore t bp r.start) ∧ r' = ⟨bp, bp⟩) ∨
    (¬ (root t r.start.node ≠ root t bp.node ∨ BPBefore t bp r.start) ∧ r' = { r with «end» := bp })

/-- **`setStart(node, offset)`。** `r` は `s.ranges` の `i` 番目。 -/
def SetStartResult (s : DOMState) (i : Nat) (r : RangeState) (bp : BoundaryPoint) :
    Except DOMException DOMState → Prop
  | .error e => BoundaryPointError s.tree bp e
  | .ok s' => BoundaryPointOk s.tree bp ∧
      ∃ r', StartSet s.tree r bp r' ∧ s' = { s with ranges := s.ranges.set i r' }

/-- **`setEnd(node, offset)`。** -/
def SetEndResult (s : DOMState) (i : Nat) (r : RangeState) (bp : BoundaryPoint) :
    Except DOMException DOMState → Prop
  | .error e => BoundaryPointError s.tree bp e
  | .ok s' => BoundaryPointOk s.tree bp ∧
      ∃ r', EndSet s.tree r bp r' ∧ s' = { s with ranges := s.ranges.set i r' }

/--
`setStartBefore` / `setStartAfter` / `setEndBefore` / `setEndAfter` の step 1-2。

parent が null なら InvalidNodeTypeError、そうでなければ (parent, index)（After なら index + 1）。
-/
def SiblingPoint (t : Tree) (n : NodeId) (isAfter : Bool) (bp : BoundaryPoint) : Prop :=
  ∃ p idx, parentOf t n = some p ∧ index t n = some idx ∧
    bp = ⟨p, if isAfter then idx + 1 else idx⟩

/-- **`setStartBefore(node)` / `setStartAfter(node)`。** -/
def SetStartSiblingResult (s : DOMState) (i : Nat) (r : RangeState) (n : NodeId) (isAfter : Bool) :
    Except DOMException DOMState → Prop
  | res => (parentOf s.tree n = none ∧ res = .error .invalidNodeTypeError) ∨
      ∃ bp, SiblingPoint s.tree n isAfter bp ∧ SetStartResult s i r bp res

/-- **`setEndBefore(node)` / `setEndAfter(node)`。** -/
def SetEndSiblingResult (s : DOMState) (i : Nat) (r : RangeState) (n : NodeId) (isAfter : Bool) :
    Except DOMException DOMState → Prop
  | res => (parentOf s.tree n = none ∧ res = .error .invalidNodeTypeError) ∨
      ∃ bp, SiblingPoint s.tree n isAfter bp ∧ SetEndResult s i r bp res

/-- **`collapse(toStart)`。** toStart なら end を start に、そうでなければ start を end にする。 -/
def CollapseResult (s : DOMState) (i : Nat) (r : RangeState) (toStart : Bool) :
    Except DOMException DOMState → Prop
  | res => (toStart = true ∧ res = .ok { s with ranges := s.ranges.set i ⟨r.start, r.start⟩ }) ∨
      (toStart = false ∧ res = .ok { s with ranges := s.ranges.set i ⟨r.«end», r.«end»⟩ })

/-- **`selectNode(node)`。** parent が null なら InvalidNodeTypeError。 -/
def SelectNodeResult (s : DOMState) (i : Nat) (n : NodeId) :
    Except DOMException DOMState → Prop
  | res => (parentOf s.tree n = none ∧ res = .error .invalidNodeTypeError) ∨
      ∃ p idx, parentOf s.tree n = some p ∧ index s.tree n = some idx ∧
        res = .ok { s with ranges := s.ranges.set i ⟨⟨p, idx⟩, ⟨p, idx + 1⟩⟩ }

/-- **`selectNodeContents(node)`。** doctype なら InvalidNodeTypeError。 -/
def SelectNodeContentsResult (s : DOMState) (i : Nat) (n : NodeId) :
    Except DOMException DOMState → Prop
  | res => (s.tree.get? n = none ∧ res = .error .notFoundError) ∨
      (∃ d, s.tree.get? n = some d ∧ d.kind = .documentType ∧
        res = .error .invalidNodeTypeError) ∨
      (∃ d, s.tree.get? n = some d ∧ d.kind ≠ .documentType ∧
        res = .ok { s with ranges := s.ranges.set i ⟨⟨n, 0⟩, ⟨n, d.length⟩⟩ })

/-! ## 実行側との一致 -/

theorem rangeBoundaryError_spec (t : Tree) (bp : BoundaryPoint) :
    (∃ e, rangeBoundaryError t bp = some e ∧ BoundaryPointError t bp e) ∨
      (rangeBoundaryError t bp = none ∧ BoundaryPointOk t bp) := by
  unfold rangeBoundaryError BoundaryPointError BoundaryPointOk
  cases hd : t.get? bp.node with
  | none => exact Or.inl ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some d =>
    dsimp only
    by_cases hk : d.kind = .documentType
    · rw [if_pos (by simp [hk])]
      exact Or.inl ⟨_, rfl, Or.inr (Or.inl ⟨d, rfl, hk, rfl⟩)⟩
    · rw [if_neg (by simp [hk])]
      by_cases hl : d.length < bp.offset
      · rw [if_pos hl]; exact Or.inl ⟨_, rfl, Or.inr (Or.inr ⟨d, rfl, hk, hl, rfl⟩)⟩
      · rw [if_neg hl]; exact Or.inr ⟨rfl, d, rfl, hk, by omega⟩

theorem boundaryPointError_unique {bp : BoundaryPoint} {e₁ e₂ : DOMException}
    (h₁ : BoundaryPointError t bp e₁) (h₂ : BoundaryPointError t bp e₂) : e₁ = e₂ := by
  rcases h₁ with ⟨hn, rfl⟩ | ⟨d, hd, hk, rfl⟩ | ⟨d, hd, hk, hl, rfl⟩ <;>
    rcases h₂ with ⟨hn', rfl⟩ | ⟨d', hd', hk', rfl⟩ | ⟨d', hd', hk', hl', rfl⟩ <;>
    first
      | rfl
      | (rw [hn] at hd'; cases hd')
      | (rw [hn'] at hd; cases hd)
      | (rw [hd] at hd'; cases hd'; contradiction)

theorem not_boundaryPointError {bp : BoundaryPoint} {e : DOMException}
    (hok : BoundaryPointOk t bp) (h : BoundaryPointError t bp e) : False := by
  obtain ⟨d, hd, hk, hl⟩ := hok
  rcases h with ⟨hn, -⟩ | ⟨d', hd', hk', -⟩ | ⟨d', hd', -, hl', -⟩ <;>
    first
      | (rw [hd] at hn; cases hn)
      | (rw [hd] at hd'; cases hd'; first | exact hk hk' | omega)

section Valid

variable (hwf : WellFormed t) {r : RangeState} (hrv : RangeValid t r)
include hwf hrv

theorem rangeNeedsCollapse_start_iff {bp : BoundaryPoint} (hbp : BoundaryPointOk t bp) :
    rangeNeedsCollapse t bp r.«end» = true ↔
      (root t r.start.node ≠ root t bp.node ∨ BPBefore t r.«end» bp) := by
  obtain ⟨-, ⟨ed, he, -⟩, hroot, -⟩ := hrv
  obtain ⟨d, hd, -, -⟩ := hbp
  unfold rangeNeedsCollapse
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  rw [hroot]
  by_cases hr : root t bp.node = root t r.«end».node
  · rw [bpPosition_eq_gt_iff hwf hd he hr]
    simp [hr]
  · constructor
    · intro _; exact Or.inl (fun h => hr h.symm)
    · intro _; exact Or.inl hr

theorem rangeNeedsCollapse_end_iff {bp : BoundaryPoint} (hbp : BoundaryPointOk t bp) :
    rangeNeedsCollapse t r.start bp = true ↔
      (root t r.start.node ≠ root t bp.node ∨ BPBefore t bp r.start) := by
  obtain ⟨⟨sd, hs, -⟩, -, -, -⟩ := hrv
  obtain ⟨d, hd, -, -⟩ := hbp
  unfold rangeNeedsCollapse
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases hr : root t r.start.node = root t bp.node
  · rw [bpPosition_eq_gt_iff hwf hs hd hr]
  · simp [hr]

theorem setStartBP_spec {bp : BoundaryPoint} (hbp : BoundaryPointOk t bp) :
    StartSet t r bp (setStartBP t r bp) := by
  unfold setStartBP StartSet
  by_cases h : rangeNeedsCollapse t bp r.«end» = true
  · rw [if_pos h]; exact Or.inl ⟨(rangeNeedsCollapse_start_iff hwf hrv hbp).mp h, rfl⟩
  · rw [if_neg h]
    exact Or.inr ⟨fun h' => h ((rangeNeedsCollapse_start_iff hwf hrv hbp).mpr h'), rfl⟩

theorem setEndBP_spec {bp : BoundaryPoint} (hbp : BoundaryPointOk t bp) :
    EndSet t r bp (setEndBP t r bp) := by
  unfold setEndBP EndSet
  by_cases h : rangeNeedsCollapse t r.start bp = true
  · rw [if_pos h]; exact Or.inl ⟨(rangeNeedsCollapse_end_iff hwf hrv hbp).mp h, rfl⟩
  · rw [if_neg h]
    exact Or.inr ⟨fun h' => h ((rangeNeedsCollapse_end_iff hwf hrv hbp).mpr h'), rfl⟩

end Valid

theorem startSet_unique {r r₁ r₂ : RangeState} {bp : BoundaryPoint}
    (h₁ : StartSet t r bp r₁) (h₂ : StartSet t r bp r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨c₁, rfl⟩ | ⟨c₁, rfl⟩ <;> rcases h₂ with ⟨c₂, rfl⟩ | ⟨c₂, rfl⟩
  · rfl
  · exact absurd c₁ c₂
  · exact absurd c₂ c₁
  · rfl

theorem endSet_unique {r r₁ r₂ : RangeState} {bp : BoundaryPoint}
    (h₁ : EndSet t r bp r₁) (h₂ : EndSet t r bp r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨c₁, rfl⟩ | ⟨c₁, rfl⟩ <;> rcases h₂ with ⟨c₂, rfl⟩ | ⟨c₂, rfl⟩
  · rfl
  · exact absurd c₁ c₂
  · exact absurd c₂ c₁
  · rfl

/-! ## 全体 -/

section Results

variable {s : DOMState} (hwf : WellFormed s.tree) {i : Nat} {r : RangeState}
  (hr : s.ranges[i]? = some r) (hrv : RangeValid s.tree r)
include hwf hr hrv

theorem rangeSetStart_result_sound (bp : BoundaryPoint) :
    SetStartResult s i r bp (rangeSetStart s i bp) := by
  unfold rangeSetStart
  rw [hr]
  rcases rangeBoundaryError_spec s.tree bp with ⟨e, he, hspec⟩ | ⟨he, hok⟩
  · rw [he]; exact hspec
  · rw [he]; exact ⟨hok, _, setStartBP_spec hwf hrv hok, rfl⟩

theorem rangeSetStart_result_complete {bp : BoundaryPoint} {res : Except DOMException DOMState}
    (h : SetStartResult s i r bp res) : res = rangeSetStart s i bp := by
  have hs := rangeSetStart_result_sound hwf hr hrv bp
  generalize rangeSetStart s i bp = res' at hs
  rcases res with e | s₁ <;> rcases res' with e' | s₂
  · rw [boundaryPointError_unique h hs]
  · exact (not_boundaryPointError hs.1 h).elim
  · exact (not_boundaryPointError h.1 hs).elim
  · obtain ⟨-, r₁, h₁, rfl⟩ := h
    obtain ⟨-, r₂, h₂, rfl⟩ := hs
    rw [startSet_unique h₁ h₂]

theorem rangeSetEnd_result_sound (bp : BoundaryPoint) :
    SetEndResult s i r bp (rangeSetEnd s i bp) := by
  unfold rangeSetEnd
  rw [hr]
  rcases rangeBoundaryError_spec s.tree bp with ⟨e, he, hspec⟩ | ⟨he, hok⟩
  · rw [he]; exact hspec
  · rw [he]; exact ⟨hok, _, setEndBP_spec hwf hrv hok, rfl⟩

theorem rangeSetEnd_result_complete {bp : BoundaryPoint} {res : Except DOMException DOMState}
    (h : SetEndResult s i r bp res) : res = rangeSetEnd s i bp := by
  have hs := rangeSetEnd_result_sound hwf hr hrv bp
  generalize rangeSetEnd s i bp = res' at hs
  rcases res with e | s₁ <;> rcases res' with e' | s₂
  · rw [boundaryPointError_unique h hs]
  · exact (not_boundaryPointError hs.1 h).elim
  · exact (not_boundaryPointError h.1 hs).elim
  · obtain ⟨-, r₁, h₁, rfl⟩ := h
    obtain ⟨-, r₂, h₂, rfl⟩ := hs
    rw [endSet_unique h₁ h₂]

omit hr hrv in
theorem siblingBP_spec (n : NodeId) (isAfter : Bool) :
    (parentOf s.tree n = none ∧ siblingBP s.tree n isAfter = none) ∨
      ∃ bp, SiblingPoint s.tree n isAfter bp ∧ siblingBP s.tree n isAfter = some bp := by
  unfold siblingBP SiblingPoint
  cases hp : parentOf s.tree n with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p =>
    obtain ⟨idx, hi⟩ := index_isSome hwf hp
    simp only [hi]
    exact Or.inr ⟨_, ⟨p, idx, rfl, rfl, rfl⟩, rfl⟩

omit hwf hr hrv in
theorem siblingPoint_unique {n : NodeId} {isAfter : Bool} {a b : BoundaryPoint}
    (h₁ : SiblingPoint s.tree n isAfter a) (h₂ : SiblingPoint s.tree n isAfter b) : a = b := by
  obtain ⟨p, i₁, hp, hi, rfl⟩ := h₁
  obtain ⟨p', i₂, hp', hi', rfl⟩ := h₂
  rw [hp] at hp'; cases hp'
  rw [hi] at hi'; cases hi'
  rfl

theorem rangeSetStartSibling_result_complete {n : NodeId} {isAfter : Bool}
    {res : Except DOMException DOMState} (h : SetStartSiblingResult s i r n isAfter res) :
    res = rangeSetStartSibling s i n isAfter := by
  unfold rangeSetStartSibling
  rcases siblingBP_spec hwf n isAfter with ⟨hp, hb⟩ | ⟨bp, hsp, hb⟩ <;> rw [hb]
  · rcases h with ⟨-, rfl⟩ | ⟨bp, ⟨p, idx, hp', -, -⟩, -⟩
    · rfl
    · rw [hp] at hp'; cases hp'
  · rcases h with ⟨hp, -⟩ | ⟨bp', hsp', hres⟩
    · obtain ⟨p, idx, hp', -, -⟩ := hsp; rw [hp] at hp'; cases hp'
    · rw [siblingPoint_unique hsp' hsp] at hres
      exact rangeSetStart_result_complete hwf hr hrv hres

theorem rangeSetStartSibling_result_sound (n : NodeId) (isAfter : Bool) :
    SetStartSiblingResult s i r n isAfter (rangeSetStartSibling s i n isAfter) := by
  unfold rangeSetStartSibling
  rcases siblingBP_spec hwf n isAfter with ⟨hp, hb⟩ | ⟨bp, hsp, hb⟩ <;> rw [hb]
  · exact Or.inl ⟨hp, rfl⟩
  · exact Or.inr ⟨bp, hsp, rangeSetStart_result_sound hwf hr hrv bp⟩

theorem rangeSetEndSibling_result_sound (n : NodeId) (isAfter : Bool) :
    SetEndSiblingResult s i r n isAfter (rangeSetEndSibling s i n isAfter) := by
  unfold rangeSetEndSibling
  rcases siblingBP_spec hwf n isAfter with ⟨hp, hb⟩ | ⟨bp, hsp, hb⟩ <;> rw [hb]
  · exact Or.inl ⟨hp, rfl⟩
  · exact Or.inr ⟨bp, hsp, rangeSetEnd_result_sound hwf hr hrv bp⟩

theorem rangeSetEndSibling_result_complete {n : NodeId} {isAfter : Bool}
    {res : Except DOMException DOMState} (h : SetEndSiblingResult s i r n isAfter res) :
    res = rangeSetEndSibling s i n isAfter := by
  unfold rangeSetEndSibling
  rcases siblingBP_spec hwf n isAfter with ⟨hp, hb⟩ | ⟨bp, hsp, hb⟩ <;> rw [hb]
  · rcases h with ⟨-, rfl⟩ | ⟨bp, ⟨p, idx, hp', -, -⟩, -⟩
    · rfl
    · rw [hp] at hp'; cases hp'
  · rcases h with ⟨hp, -⟩ | ⟨bp', hsp', hres⟩
    · obtain ⟨p, idx, hp', -, -⟩ := hsp; rw [hp] at hp'; cases hp'
    · rw [siblingPoint_unique hsp' hsp] at hres
      exact rangeSetEnd_result_complete hwf hr hrv hres

end Results

theorem rangeCollapse_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hr : s.ranges[i]? = some r) {toStart : Bool} {res : Except DOMException DOMState} :
    CollapseResult s i r toStart res ↔ res = rangeCollapse s i toStart := by
  unfold rangeCollapse CollapseResult
  rw [hr]
  cases toStart <;> simp [withRange]

theorem rangeSelectNode_result_complete {s : DOMState} (hwf : WellFormed s.tree) {i : Nat}
    {r : RangeState} (hr : s.ranges[i]? = some r) {n : NodeId} {res : Except DOMException DOMState} :
    SelectNodeResult s i n res ↔ res = rangeSelectNode s i n := by
  unfold rangeSelectNode SelectNodeResult
  rw [hr]
  dsimp only
  cases hp : parentOf s.tree n with
  | none => simp
  | some p =>
    obtain ⟨idx, hi⟩ := index_isSome hwf hp
    simp only [hi, withRange, reduceCtorEq, false_and, Option.some.injEq, exists_and_left,
      exists_eq_left', false_or]

theorem rangeSelectNodeContents_result_complete {s : DOMState} {i : Nat} {r : RangeState}
    (hr : s.ranges[i]? = some r) {n : NodeId} {res : Except DOMException DOMState} :
    SelectNodeContentsResult s i n res ↔ res = rangeSelectNodeContents s i n := by
  unfold rangeSelectNodeContents SelectNodeContentsResult
  rw [hr]
  cases hd : s.tree.get? n with
  | none => simp
  | some d =>
    dsimp only
    by_cases hk : d.kind = .documentType
    · rw [if_pos (by simp [hk])]; simp [hk]
    · rw [if_neg (by simp [hk])]; simp [hk, withRange]

end Dom.Spec
