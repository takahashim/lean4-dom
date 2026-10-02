import Dom.Spec.NodeQuery
import Dom.Properties.Path
import Dom.Range.Api

/-!
# 値を返す Range の method の関係仕様

`Dom/Range/Api.lean` の `isPointInRange`・`comparePoint`・`intersectsNode`・
`compareBoundaryPoints` の戻り値（例外を含む）を、§5.3 の boundary point position を
**実行側の `bpPosition` を使わずに** 書いた関係 `BPBefore` で言い、実行関数が
それにちょうど一致することを示す。

## `BPBefore`

§5.3 の boundary point position は「node が同じなら offset を比べる」「一方が他方の
ancestor なら、子孫の側へ向かう子の index と offset を比べる」「そうでなければ tree order」
という場合分けである。`BPBefore t a b`（`a` が `b` の before）はこの四つの場合を
§4.2 の語彙（parent・index・inclusive ancestor）だけで並べたもので、`childTowards` も
preorder も使わない。step 3 の「引数を入れ替えて呼ぶ」は、`b.node` が `a.node` の
ancestor である場合（三つ目の選言）として展開してある。

`bpPosition_eq_lt_iff` / `bpPosition_eq_eq_iff` / `bpPosition_eq_gt_iff` が、
同じ木にある二つの boundary point について実行側の `bpPosition` との一致である。
証明は `Dom/Properties/Path.lean` の key（root からの index の列）を経由する。

## 戻り値の関係

仕様の「…なら throw」「…なら return」の列を `ThrowIf` / `ReturnIf` で写す。
`range` の index が無い場合（`notFoundError`）は harness の都合なので、定理は
`s.ranges[i]? = some r` を仮定する。`comparePoint` と `intersectsNode` の
「node が木に無ければ `notFoundError`」も同じく model の都合（JS の node は必ずどこかの木にある）で、
関係の先頭に置いてある。
-/

namespace Dom.Spec

open Dom

variable {t : Tree}

/-! ## boundary point の前後 -/

/-- DOM §5.3。boundary point `a` は `b` の before である。 -/
def BPBefore (t : Tree) (a b : BoundaryPoint) : Prop :=
  -- step 2。同じ node なら offset の順。
  (a.node = b.node ∧ a.offset < b.offset) ∨
  -- step 4-5。`a.node` が `b.node` の ancestor で、`b.node` へ向かう子の index が offset 以上。
  (∃ c i, parentOf t c = some a.node ∧ index t c = some i ∧ InclusiveAncestor t c b.node ∧
    a.offset ≤ i) ∨
  -- step 3（入れ替えて step 4）。`b.node` が `a.node` の ancestor で、
  -- `a.node` へ向かう子の index が offset より小さい。
  (∃ c i, parentOf t c = some b.node ∧ index t c = some i ∧ InclusiveAncestor t c a.node ∧
    i < b.offset) ∨
  -- step 5。どちらも他方の ancestor でなく、`a.node` が tree order で先行する。
  (∃ p cx cy i j, parentOf t cx = some p ∧ parentOf t cy = some p ∧
    index t cx = some i ∧ index t cy = some j ∧ i < j ∧
    InclusiveAncestor t cx a.node ∧ InclusiveAncestor t cy b.node)

theorem lexCmp_self (l : List Nat) : lexCmp l l = .eq := by
  simpa using lexCmp_append_left l [] []

theorem lexCmp_bpKey_of_bpBefore (hwf : WellFormed t) {a b : BoundaryPoint}
    (h : BPBefore t a b) : lexCmp (bpKey t a) (bpKey t b) = .lt := by
  rcases h with ⟨hn, ho⟩ | ⟨c, i, hcp, hci, hcb, hle⟩ | ⟨c, i, hcp, hci, hca, hlt⟩ |
    ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxa, hyb⟩
  · unfold bpKey
    rw [hn, lexCmp_append_left]
    exact lexCmp_cons_lt ho [] []
  · obtain ⟨rest, hrest⟩ := pathIndices_split hwf hcp hcb
    unfold bpKey
    rw [hrest, hci]
    simp only [Option.getD_some, List.append_assoc, List.cons_append]
    rw [lexCmp_append_left]
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact lexCmp_cons_lt h _ _
    · subst h
      rw [lexCmp_cons_eq]
      cases rest <;> rfl
  · obtain ⟨rest, hrest⟩ := pathIndices_split hwf hcp hca
    unfold bpKey
    rw [hrest, hci]
    simp only [Option.getD_some, List.append_assoc, List.cons_append]
    rw [lexCmp_append_left]
    exact lexCmp_cons_lt hlt _ _
  · obtain ⟨r1, hr1⟩ := pathIndices_split hwf hcx hxa
    obtain ⟨r2, hr2⟩ := pathIndices_split hwf hcy hyb
    unfold bpKey
    rw [hr1, hr2, hi, hj]
    simp only [Option.getD_some, List.append_assoc, List.cons_append]
    rw [lexCmp_append_left]
    exact lexCmp_cons_lt hij _ _

/-- 同じ木にある二つの boundary point は、before・equal・after のどれかである。 -/
theorem bpBefore_trichotomy (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hroot : root t a.node = root t b.node) :
    BPBefore t a b ∨ a = b ∨ BPBefore t b a := by
  by_cases hn : a.node = b.node
  · rcases Nat.lt_trichotomy a.offset b.offset with h | h | h
    · exact Or.inl (Or.inl ⟨hn, h⟩)
    · right; left
      cases a; cases b; simp_all
    · exact Or.inr (Or.inr (Or.inl ⟨hn.symm, h⟩))
  by_cases hab : Ancestor t a.node b.node
  · obtain ⟨c, -, hcp, hcb⟩ := childTowards_eq_some hwf hab
    obtain ⟨i, hi⟩ := index_isSome hwf hcp
    by_cases hle : a.offset ≤ i
    · exact Or.inl (Or.inr (Or.inl ⟨c, i, hcp, hi, hcb, hle⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, i, hcp, hi, hcb, by omega⟩))))
  by_cases hba : Ancestor t b.node a.node
  · obtain ⟨c, -, hcp, hca⟩ := childTowards_eq_some hwf hba
    obtain ⟨i, hi⟩ := index_isSome hwf hcp
    by_cases hle : b.offset ≤ i
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, i, hcp, hi, hca, hle⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨c, i, hcp, hi, hca, by omega⟩)))
  cases hp : precedes t b.node a.node with
  | true =>
    rcases (precedes_iff_struct hwf hb hroot.symm (fun h => hn h.symm)).mp hp with h | h
    · exact absurd h hba
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  | false =>
    rcases (precedes_eq_false_iff hwf ha hroot hn).mp hp with h | h
    · exact absurd h hab
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

section Position

variable (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
  (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
  (hroot : root t a.node = root t b.node)
include hwf ha hb hroot

/-- **§5.3 の before は、実行側の `bpPosition` が `.lt` を返すことちょうどである。** -/
theorem bpPosition_eq_lt_iff : bpPosition t a b = .lt ↔ BPBefore t a b := by
  rw [bpPosition_eq_lexCmp hwf ha hb hroot]
  refine ⟨fun h => ?_, lexCmp_bpKey_of_bpBefore hwf⟩
  rcases bpBefore_trichotomy hwf ha hb hroot with h' | rfl | h'
  · exact h'
  · rw [lexCmp_self] at h; cases h
  · rw [lexCmp_swap (bpKey t b), lexCmp_bpKey_of_bpBefore hwf h'] at h; cases h

/-- **§5.3 の equal は、実行側の `bpPosition` が `.eq` を返すことちょうどである。** -/
theorem bpPosition_eq_eq_iff : bpPosition t a b = .eq ↔ a = b := by
  rw [bpPosition_eq_lexCmp hwf ha hb hroot]
  refine ⟨fun h => ?_, fun h => by subst h; exact lexCmp_self _⟩
  rcases bpBefore_trichotomy hwf ha hb hroot with h' | h' | h'
  · rw [lexCmp_bpKey_of_bpBefore hwf h'] at h; cases h
  · exact h'
  · rw [lexCmp_swap (bpKey t b), lexCmp_bpKey_of_bpBefore hwf h'] at h; cases h

/-- **§5.3 の after は、実行側の `bpPosition` が `.gt` を返すことちょうどである。** -/
theorem bpPosition_eq_gt_iff : bpPosition t a b = .gt ↔ BPBefore t b a := by
  rw [bpPosition_eq_lexCmp hwf ha hb hroot]
  refine ⟨fun h => ?_, fun h => by
    rw [lexCmp_swap (bpKey t b), lexCmp_bpKey_of_bpBefore hwf h]; rfl⟩
  rcases bpBefore_trichotomy hwf ha hb hroot with h' | rfl | h'
  · rw [lexCmp_bpKey_of_bpBefore hwf h'] at h; cases h
  · rw [lexCmp_self] at h; cases h
  · exact h'

open Classical in
theorem bpPosition_beq_lt : (bpPosition t a b == .lt) = decide (BPBefore t a b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact bpPosition_eq_lt_iff hwf ha hb hroot

open Classical in
theorem bpPosition_beq_gt : (bpPosition t a b == .gt) = decide (BPBefore t b a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact bpPosition_eq_gt_iff hwf ha hb hroot

end Position

/-! ## 仕様の制御の流れ -/

/-- 「`p` なら `e` を throw、でなければ次へ」。 -/
def ThrowIf {α : Type} (p : Prop) (e : DOMException) (next : Except DOMException α → Prop)
    (res : Except DOMException α) : Prop :=
  (p ∧ res = .error e) ∨ (¬ p ∧ next res)

/-- 「`p` なら `v` を return、でなければ次へ」。 -/
def ReturnIf {α : Type} (p : Prop) (v : α) (next : Except DOMException α → Prop)
    (res : Except DOMException α) : Prop :=
  (p ∧ res = .ok v) ∨ (¬ p ∧ next res)

/-- 「`v` を return」。 -/
def Returns {α : Type} (v : α) (res : Except DOMException α) : Prop := res = .ok v

theorem throwIf_pos {α : Type} {p : Prop} {e : DOMException} {next : Except DOMException α → Prop}
    {res : Except DOMException α} (h : p) : ThrowIf p e next res ↔ res = .error e := by
  simp [ThrowIf, h]

theorem throwIf_neg {α : Type} {p : Prop} {e : DOMException} {next : Except DOMException α → Prop}
    {res : Except DOMException α} (h : ¬ p) : ThrowIf p e next res ↔ next res := by
  simp [ThrowIf, h]

theorem returnIf_pos {α : Type} {p : Prop} {v : α} {next : Except DOMException α → Prop}
    {res : Except DOMException α} (h : p) : ReturnIf p v next res ↔ res = .ok v := by
  simp [ReturnIf, h]

theorem returnIf_neg {α : Type} {p : Prop} {v : α} {next : Except DOMException α → Prop}
    {res : Except DOMException α} (h : ¬ p) : ReturnIf p v next res ↔ next res := by
  simp [ReturnIf, h]

/-! ## 戻り値の関係 -/

/-- DOM §5.5 `isPointInRange(node, offset)`。 -/
def IsPointInRangeResult (t : Tree) (r : RangeState) (bp : BoundaryPoint) :
    Except DOMException Bool → Prop :=
  -- step 1
  ReturnIf (¬ SameTree t bp.node r.start.node) false <|
  -- step 2
  ThrowIf (kindOf t bp.node = some .documentType) .invalidNodeTypeError <|
  -- step 3
  ThrowIf (lengthOf t bp.node < bp.offset) .indexSizeError <|
  -- step 4
  ReturnIf (BPBefore t bp r.start ∨ BPBefore t r.«end» bp) false <|
  -- step 5
  Returns true

/-- DOM §5.5 `comparePoint(node, offset)`。先頭の「木に無い」は model の都合。 -/
def ComparePointResult (t : Tree) (r : RangeState) (bp : BoundaryPoint) :
    Except DOMException Int → Prop :=
  ThrowIf (t.get? bp.node = none) .notFoundError <|
  -- step 1
  ThrowIf (¬ SameTree t bp.node r.start.node) .wrongDocumentError <|
  -- step 2
  ThrowIf (kindOf t bp.node = some .documentType) .invalidNodeTypeError <|
  -- step 3
  ThrowIf (lengthOf t bp.node < bp.offset) .indexSizeError <|
  -- step 4
  ReturnIf (BPBefore t bp r.start) (-1) <|
  -- step 5
  ReturnIf (BPBefore t r.«end» bp) 1 <|
  -- step 6
  Returns 0

/-- DOM §5.5 `intersectsNode(node)`。先頭の「木に無い」は model の都合。 -/
def IntersectsNodeResult (t : Tree) (r : RangeState) (n : NodeId) :
    Except DOMException Bool → Prop :=
  ThrowIf (t.get? n = none) .notFoundError <|
  -- step 1
  ReturnIf (¬ SameTree t n r.start.node) false <|
  -- step 2-3
  ReturnIf (parentOf t n = none) true <|
  -- step 4-6
  fun res => ∃ p i, parentOf t n = some p ∧ index t n = some i ∧
    ReturnIf (BPBefore t ⟨p, i⟩ r.«end» ∧ BPBefore t r.start ⟨p, i + 1⟩) true
      (Returns false) res

/-- DOM §5.5 `compareBoundaryPoints(how, sourceRange)` の step 3 の表。 -/
def compareHowPoints (r source : RangeState) : Nat → BoundaryPoint × BoundaryPoint
  -- START_TO_START
  | 0 => (r.start, source.start)
  -- START_TO_END
  | 1 => (r.«end», source.start)
  -- END_TO_END
  | 2 => (r.«end», source.«end»)
  -- END_TO_START
  | _ => (r.start, source.«end»)

/-- DOM §5.3 の position を -1 / 0 / 1 で返すこと。 -/
def PositionResult (t : Tree) (a b : BoundaryPoint) (res : Except DOMException Int) : Prop :=
  (BPBefore t a b ∧ res = .ok (-1)) ∨ (a = b ∧ res = .ok 0) ∨ (BPBefore t b a ∧ res = .ok 1)

/-- DOM §5.5 `compareBoundaryPoints(how, sourceRange)`。 -/
def CompareBoundaryPointsResult (t : Tree) (r source : RangeState) (how : Nat) :
    Except DOMException Int → Prop :=
  -- step 1
  ThrowIf (3 < how) .notSupportedError <|
  -- step 2
  ThrowIf (¬ SameTree t r.start.node source.start.node) .wrongDocumentError <|
  -- step 3-4
  PositionResult t (compareHowPoints r source how).1 (compareHowPoints r source how).2

/-! ## 実行関数との一致 -/

/-- 同じ木にある node の片方が木にあれば、もう片方も木にある。 -/
theorem exists_get?_of_sameTree (hwf : WellFormed t) {x y : NodeId} {yd : NodeData}
    (hs : SameTree t x y) (hy : t.get? y = some yd) : ∃ xd, t.get? x = some xd := by
  cases hx : t.get? x with
  | some xd => exact ⟨xd, rfl⟩
  | none =>
    exfalso
    have hrx : root t x = x :=
      root_unique hwf (InclusiveAncestor.refl t x) (parentOf_eq_none_of_get?_eq_none hx)
    obtain ⟨rd, hrd⟩ := exists_data_root hwf hy
    rw [← (root_eq_root_iff hwf x y).mpr hs, hrx, hx] at hrd
    cases hrd

theorem lengthOf_of_get? {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    lengthOf t n = d.length := by
  simp [lengthOf, h]

theorem positionResult_iff (hwf : WellFormed t) {a b : BoundaryPoint} {ad bd : NodeData}
    (ha : t.get? a.node = some ad) (hb : t.get? b.node = some bd)
    (hroot : root t a.node = root t b.node) (res : Except DOMException Int) :
    PositionResult t a b res ↔
      res = .ok (match bpPosition t a b with | .lt => -1 | .eq => 0 | .gt => 1) := by
  have hlt := bpPosition_eq_lt_iff hwf ha hb hroot
  have heq := bpPosition_eq_eq_iff hwf ha hb hroot
  have hgt := bpPosition_eq_gt_iff hwf ha hb hroot
  unfold PositionResult
  cases hp : bpPosition t a b with
  | lt =>
    have h1 := hlt.mp hp
    have h2 : ¬ a = b := fun h => by rw [heq.mpr h] at hp; cases hp
    have h3 : ¬ BPBefore t b a := fun h => by rw [hgt.mpr h] at hp; cases hp
    simp [h1, h2, h3]
  | eq =>
    have h1 : ¬ BPBefore t a b := fun h => by rw [hlt.mpr h] at hp; cases hp
    have h2 := heq.mp hp
    subst h2
    simp [h1]
  | gt =>
    have h1 : ¬ BPBefore t a b := fun h => by rw [hlt.mpr h] at hp; cases hp
    have h2 : ¬ a = b := fun h => by rw [heq.mpr h] at hp; cases hp
    have h3 := hgt.mp hp
    simp [h1, h2, h3]

section Range

variable {s : DOMState} {i : Nat} {r : RangeState}
  (hwf : WellFormed s.tree) (hs : s.ranges[i]? = some r) (hr : RangeValid s.tree r)
include hwf hs hr

/-- **`isPointInRange()` の戻り値（例外を含む）は §5.5 の条件ちょうどである。** -/
theorem rangeIsPointInRange_eq_iff (bp : BoundaryPoint) (res : Except DOMException Bool) :
    rangeIsPointInRange s i bp = res ↔ IsPointInRangeResult s.tree r bp res := by
  obtain ⟨⟨sd, hsd, -⟩, ⟨ed, hed, -⟩, hse, -⟩ := hr
  unfold IsPointInRangeResult
  by_cases hroot : root s.tree bp.node = root s.tree r.start.node
  rotate_left
  · have hS : ¬ SameTree s.tree bp.node r.start.node := fun h =>
      hroot ((root_eq_root_iff hwf _ _).mpr h)
    have himpl : rangeIsPointInRange s i bp = .ok false := by
      simp [rangeIsPointInRange, hs, hroot]
    rw [himpl, returnIf_pos hS]
    exact eq_comm
  have hS := (root_eq_root_iff hwf _ _).mp hroot
  rw [returnIf_neg (fun h => h hS)]
  obtain ⟨d, hd⟩ := exists_get?_of_sameTree hwf hS hsd
  rw [kindOf_of_get? hd, lengthOf_of_get? hd]
  by_cases hdt : d.kind = .documentType
  · have himpl : rangeIsPointInRange s i bp = .error .invalidNodeTypeError := by
      simp [rangeIsPointInRange, rangeBoundaryError, hs, hroot, hd, hdt]
    rw [himpl, throwIf_pos (by simp [hdt])]
    exact eq_comm
  rw [throwIf_neg (by simp [hdt])]
  by_cases hlen : d.length < bp.offset
  · have himpl : rangeIsPointInRange s i bp = .error .indexSizeError := by
      simp [rangeIsPointInRange, rangeBoundaryError, hs, hroot, hd, hdt, hlen]
    rw [himpl, throwIf_pos hlen]
    exact eq_comm
  rw [throwIf_neg hlen]
  have himpl : rangeIsPointInRange s i bp =
      .ok (!(bpPosition s.tree bp r.start == .lt) && !(bpPosition s.tree bp r.«end» == .gt)) := by
    simp [rangeIsPointInRange, rangeBoundaryError, hs, hroot, hd, hdt, hlen]
  rw [himpl, bpPosition_beq_lt hwf hd hsd hroot,
    bpPosition_beq_gt hwf hd hed (hroot.trans hse)]
  by_cases hb : BPBefore s.tree bp r.start ∨ BPBefore s.tree r.«end» bp
  · rw [returnIf_pos hb]
    rcases hb with hb | hb <;> simp [hb, eq_comm]
  · rw [returnIf_neg hb]
    simp only [not_or] at hb
    simp [hb.1, hb.2, Returns, eq_comm]

/-- **`comparePoint()` の戻り値（例外を含む）は §5.5 の条件ちょうどである。** -/
theorem rangeComparePoint_eq_iff (bp : BoundaryPoint) (res : Except DOMException Int) :
    rangeComparePoint s i bp = res ↔ ComparePointResult s.tree r bp res := by
  obtain ⟨⟨sd, hsd, -⟩, ⟨ed, hed, -⟩, hse, -⟩ := hr
  unfold ComparePointResult
  cases hd : s.tree.get? bp.node with
  | none =>
    have himpl : rangeComparePoint s i bp = .error .notFoundError := by
      simp [rangeComparePoint, hs, hd]
    rw [himpl, throwIf_pos rfl]
    exact eq_comm
  | some d =>
  rw [throwIf_neg (by simp)]
  by_cases hroot : root s.tree bp.node = root s.tree r.start.node
  rotate_left
  · have hS : ¬ SameTree s.tree bp.node r.start.node := fun h =>
      hroot ((root_eq_root_iff hwf _ _).mpr h)
    have himpl : rangeComparePoint s i bp = .error .wrongDocumentError := by
      simp [rangeComparePoint, hs, hd, hroot]
    rw [himpl, throwIf_pos hS]
    exact eq_comm
  have hS := (root_eq_root_iff hwf _ _).mp hroot
  rw [throwIf_neg (fun h => h hS)]
  rw [kindOf_of_get? hd, lengthOf_of_get? hd]
  by_cases hdt : d.kind = .documentType
  · have himpl : rangeComparePoint s i bp = .error .invalidNodeTypeError := by
      simp [rangeComparePoint, rangeBoundaryError, hs, hroot, hd, hdt]
    rw [himpl, throwIf_pos (by simp [hdt])]
    exact eq_comm
  rw [throwIf_neg (by simp [hdt])]
  by_cases hlen : d.length < bp.offset
  · have himpl : rangeComparePoint s i bp = .error .indexSizeError := by
      simp [rangeComparePoint, rangeBoundaryError, hs, hroot, hd, hdt, hlen]
    rw [himpl, throwIf_pos hlen]
    exact eq_comm
  rw [throwIf_neg hlen]
  have himpl : rangeComparePoint s i bp =
      .ok (if (bpPosition s.tree bp r.start == .lt) then -1
        else if (bpPosition s.tree bp r.«end» == .gt) then 1 else 0) := by
    simp [rangeComparePoint, rangeBoundaryError, hs, hroot, hd, hdt, hlen]
  rw [himpl, bpPosition_beq_lt hwf hd hsd hroot,
    bpPosition_beq_gt hwf hd hed (hroot.trans hse)]
  by_cases h1 : BPBefore s.tree bp r.start
  · rw [returnIf_pos h1]
    simp [h1, eq_comm]
  rw [returnIf_neg h1]
  by_cases h2 : BPBefore s.tree r.«end» bp
  · rw [returnIf_pos h2]
    simp [h1, h2, eq_comm]
  · rw [returnIf_neg h2]
    simp [h1, h2, Returns, eq_comm]

open Classical in
/-- **`intersectsNode()` の戻り値（例外を含む）は §5.5 の条件ちょうどである。** -/
theorem rangeIntersectsNode_eq_iff (n : NodeId) (res : Except DOMException Bool) :
    rangeIntersectsNode s i n = res ↔ IntersectsNodeResult s.tree r n res := by
  obtain ⟨⟨sd, hsd, -⟩, ⟨ed, hed, -⟩, hse, -⟩ := hr
  unfold IntersectsNodeResult
  cases hd : s.tree.get? n with
  | none =>
    have himpl : rangeIntersectsNode s i n = .error .notFoundError := by
      simp [rangeIntersectsNode, hs, hd]
    rw [himpl, throwIf_pos rfl]
    exact eq_comm
  | some d =>
  rw [throwIf_neg (by simp)]
  by_cases hroot : root s.tree n = root s.tree r.start.node
  rotate_left
  · have hS : ¬ SameTree s.tree n r.start.node := fun h =>
      hroot ((root_eq_root_iff hwf _ _).mpr h)
    have himpl : rangeIntersectsNode s i n = .ok false := by
      simp [rangeIntersectsNode, hs, hd, hroot]
    rw [himpl, returnIf_pos hS]
    exact eq_comm
  have hS := (root_eq_root_iff hwf _ _).mp hroot
  rw [returnIf_neg (fun h => h hS)]
  cases hp : parentOf s.tree n with
  | none =>
    have himpl : rangeIntersectsNode s i n = .ok true := by
      simp [rangeIntersectsNode, hs, hd, hroot, hp]
    rw [himpl, returnIf_pos rfl]
    exact eq_comm
  | some p =>
  rw [returnIf_neg (by simp)]
  obtain ⟨k, hk⟩ := index_isSome hwf hp
  have himpl : rangeIntersectsNode s i n =
      .ok (bpPosition s.tree ⟨p, k⟩ r.«end» == .lt &&
        bpPosition s.tree ⟨p, k + 1⟩ r.start == .gt) := by
    simp [rangeIntersectsNode, hs, hd, hroot, hp, hk]
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hp
  have hrp : root s.tree p = root s.tree r.start.node :=
    (root_eq_of_parentOf hwf hp).symm.trans hroot
  rw [himpl, bpPosition_beq_lt (b := r.«end») hwf (a := ⟨p, k⟩) hpd hed (hrp.trans hse),
    bpPosition_beq_gt (b := r.start) hwf (a := ⟨p, k + 1⟩) hpd hsd hrp]
  simp only [Option.some.injEq, hk, exists_and_left, exists_eq_left']
  by_cases hb : BPBefore s.tree ⟨p, k⟩ r.«end» ∧ BPBefore s.tree r.start ⟨p, k + 1⟩
  · rw [returnIf_pos hb]
    simp [hb.1, hb.2, eq_comm]
  · rw [returnIf_neg hb]
    have hv : (decide (BPBefore s.tree ⟨p, k⟩ r.«end») &&
        decide (BPBefore s.tree r.start ⟨p, k + 1⟩)) = false := by
      by_cases h1 : BPBefore s.tree ⟨p, k⟩ r.«end» <;> simp_all
    rw [hv]
    exact eq_comm

end Range

/-- **`compareBoundaryPoints()` の戻り値（例外を含む）は §5.5 の条件ちょうどである。** -/
theorem rangeCompareBoundaryPoints_eq_iff {s : DOMState} {i j : Nat} {r source : RangeState}
    (hwf : WellFormed s.tree) (hi : s.ranges[i]? = some r) (hj : s.ranges[j]? = some source)
    (hr : RangeValid s.tree r) (hsrc : RangeValid s.tree source)
    (how : Nat) (res : Except DOMException Int) :
    rangeCompareBoundaryPoints s i how j = res ↔
      CompareBoundaryPointsResult s.tree r source how res := by
  obtain ⟨⟨sd, hsd, -⟩, ⟨ed, hed, -⟩, hse, -⟩ := hr
  obtain ⟨⟨sd', hsd', -⟩, ⟨ed', hed', -⟩, hse', -⟩ := hsrc
  unfold CompareBoundaryPointsResult
  by_cases h3 : 3 < how
  · have himpl : rangeCompareBoundaryPoints s i how j = .error .notSupportedError := by
      simp [rangeCompareBoundaryPoints, hi, hj, h3]
    rw [himpl, throwIf_pos h3]
    exact eq_comm
  rw [throwIf_neg h3]
  by_cases hroot : root s.tree r.start.node = root s.tree source.start.node
  rotate_left
  · have hS : ¬ SameTree s.tree r.start.node source.start.node := fun h =>
      hroot ((root_eq_root_iff hwf _ _).mpr h)
    have himpl : rangeCompareBoundaryPoints s i how j = .error .wrongDocumentError := by
      simp [rangeCompareBoundaryPoints, hi, hj, h3, hroot]
    rw [himpl, throwIf_pos hS]
    exact eq_comm
  have hS := (root_eq_root_iff hwf _ _).mp hroot
  rw [throwIf_neg (fun h => h hS), eq_comm]
  have hlast := fun {a b : BoundaryPoint} {ad bd : NodeData} ha hb hab =>
    positionResult_iff (t := s.tree) (a := a) (b := b) (ad := ad) (bd := bd) hwf ha hb hab res
  obtain rfl | rfl | rfl | rfl : how = 0 ∨ how = 1 ∨ how = 2 ∨ how = 3 := by omega
  · simp only [compareHowPoints]
    rw [hlast hsd hsd' hroot]
    simp [rangeCompareBoundaryPoints, hi, hj, hroot] <;>
      (generalize bpPosition s.tree _ _ = o; cases o <;> rfl)
  · simp only [compareHowPoints]
    rw [hlast hed hsd' (hse.symm.trans hroot)]
    simp [rangeCompareBoundaryPoints, hi, hj, hroot] <;>
      (generalize bpPosition s.tree _ _ = o; cases o <;> rfl)
  · simp only [compareHowPoints]
    rw [hlast hed hed' (hse.symm.trans (hroot.trans hse'))]
    simp [rangeCompareBoundaryPoints, hi, hj, hroot] <;>
      (generalize bpPosition s.tree _ _ = o; cases o <;> rfl)
  · simp only [compareHowPoints]
    rw [hlast hsd hed' (hroot.trans hse')]
    simp [rangeCompareBoundaryPoints, hi, hj, hroot] <;>
      (generalize bpPosition s.tree _ _ = o; cases o <;> rfl)

end Dom.Spec
