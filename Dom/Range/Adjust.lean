import Dom.Range.BoundaryPoint

/-!
# mutation に伴う boundary point の更新

PLAN §8.2。仕様の live range pre-remove steps と、insert 時の offset 調整を定義する。

どちらも木は変えない。`Dom/Properties/Range.lean` の証明でこの点を使う。
-/

namespace Dom

/-! ## remove に伴う調整 -/

/--
DOM Standard §5.5 "live range pre-remove steps" の step 3-4。

start / end node が `node` の inclusive descendant である range を、
`node` があった位置 `(parent, index)` へ移す。
-/
def rangeMoveOutOfSubtree (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) : BoundaryPoint :=
  if isInclusiveAncestorOf t node bp.node then { node := parent, offset := index } else bp

/--
DOM Standard §5.5 "live range pre-remove steps" の step 5-6。

`parent` を指し、offset が `index` より大きい boundary point の offset を 1 減らす。
-/
def rangeShiftAfterRemove (parent : NodeId) (index : Nat) (bp : BoundaryPoint) : BoundaryPoint :=
  if bp.node = parent ∧ index < bp.offset then { bp with offset := bp.offset - 1 } else bp

/--
DOM Standard §5.5 "live range pre-remove steps"。

`node` の removal の直前に走る。仕様の step 順に、まず部分木の外へ移し、次に offset をずらす。
step 3-4 で移した boundary point の offset はちょうど `index` になるので、
step 5-6 の条件（`index` より大きい）には当てはまらない。
-/
def liveRangePreRemoveBP (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) : BoundaryPoint :=
  rangeShiftAfterRemove parent index (rangeMoveOutOfSubtree t node parent index bp)

def liveRangePreRemoveRange (t : Tree) (node parent : NodeId) (index : Nat)
    (r : RangeState) : RangeState :=
  { start := liveRangePreRemoveBP t node parent index r.start
    «end» := liveRangePreRemoveBP t node parent index r.«end» }

/--
DOM Standard §4.2.3 remove step 3 / move step 10。

`node` に parent が無ければ何もしない（仕様では assert により起こらない）。
-/
def liveRangePreRemove (s : DOMState) (node : NodeId) : DOMState :=
  match parentOf s.tree node with
  | none => s
  | some parent =>
    let index := (index s.tree node).getD 0
    { s with ranges := s.ranges.map (liveRangePreRemoveRange s.tree node parent index) }

/-! ## insert に伴う調整 -/

/--
DOM Standard §4.2.3 insert step 5 / move step 16。

`parent` を指し、offset が挿入位置より大きい boundary point の offset を `count` だけ増やす。
-/
def rangeShiftAfterInsert (parent : NodeId) (index count : Nat)
    (bp : BoundaryPoint) : BoundaryPoint :=
  if bp.node = parent ∧ index < bp.offset then { bp with offset := bp.offset + count } else bp

def liveRangeInsertAdjustRange (parent : NodeId) (index count : Nat)
    (r : RangeState) : RangeState :=
  { start := rangeShiftAfterInsert parent index count r.start
    «end» := rangeShiftAfterInsert parent index count r.«end» }

/--
DOM Standard §4.2.3 insert step 5 / move step 16。

`child` が `none`（末尾への挿入）なら調整は要らない。
仕様も step 5 全体を「If child is non-null」で囲んでいる。
-/
def liveRangeInsertAdjust (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (count : Nat) : DOMState :=
  match child with
  | none => s
  | some c =>
    let idx := (index s.tree c).getD 0
    { s with ranges := s.ranges.map (liveRangeInsertAdjustRange parent idx count) }

/-! ## 調整は boundary point の node を変えない -/

@[simp] theorem rangeShiftAfterInsert_node (parent : NodeId) (index count : Nat)
    (bp : BoundaryPoint) : (rangeShiftAfterInsert parent index count bp).node = bp.node := by
  unfold rangeShiftAfterInsert
  split <;> rfl

/-- 挿入側の調整は offset しか変えない。 -/
theorem liveRangeInsertAdjust_nodes (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (k : Nat) :
    ∀ r ∈ (liveRangeInsertAdjust s parent child k).ranges,
      ∃ r₀ ∈ s.ranges, r.start.node = r₀.start.node ∧ r.«end».node = r₀.«end».node := by
  intro r hr
  unfold liveRangeInsertAdjust at hr
  split at hr
  · exact ⟨r, hr, rfl, rfl⟩
  · obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hr
    exact ⟨r₀, hr₀, by rw [← hrr]; simp [liveRangeInsertAdjustRange],
      by rw [← hrr]; simp [liveRangeInsertAdjustRange]⟩

/-! ## 木を変えないこと -/

@[simp] theorem liveRangePreRemove_tree (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).tree = s.tree := by
  unfold liveRangePreRemove
  split <;> rfl

@[simp] theorem liveRangePreRemove_iterators (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).iterators = s.iterators := by
  unfold liveRangePreRemove
  split <;> rfl

@[simp] theorem liveRangeInsertAdjust_tree (s : DOMState) (p : NodeId) (c : Option NodeId)
    (k : Nat) : (liveRangeInsertAdjust s p c k).tree = s.tree := by
  unfold liveRangeInsertAdjust
  split <;> rfl

@[simp] theorem liveRangeInsertAdjust_iterators (s : DOMState) (p : NodeId) (c : Option NodeId)
    (k : Nat) : (liveRangeInsertAdjust s p c k).iterators = s.iterators := by
  unfold liveRangeInsertAdjust
  split <;> rfl


@[simp] theorem liveRangePreRemove_registrations (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).registrations = s.registrations := by
  unfold liveRangePreRemove; split <;> rfl

@[simp] theorem liveRangePreRemove_observers (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).observers = s.observers := by
  unfold liveRangePreRemove; split <;> rfl

@[simp] theorem liveRangePreRemove_pendingObservers (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).pendingObservers = s.pendingObservers := by
  unfold liveRangePreRemove; split <;> rfl

@[simp] theorem liveRangePreRemove_microtaskQueued (s : DOMState) (n : NodeId) :
    (liveRangePreRemove s n).microtaskQueued = s.microtaskQueued := by
  unfold liveRangePreRemove; split <;> rfl

@[simp] theorem liveRangeInsertAdjust_registrations (s : DOMState) (p : NodeId)
    (c : Option NodeId) (k : Nat) :
    (liveRangeInsertAdjust s p c k).registrations = s.registrations := by
  unfold liveRangeInsertAdjust; cases c <;> rfl

@[simp] theorem liveRangeInsertAdjust_observers (s : DOMState) (p : NodeId)
    (c : Option NodeId) (k : Nat) :
    (liveRangeInsertAdjust s p c k).observers = s.observers := by
  unfold liveRangeInsertAdjust; cases c <;> rfl

end Dom
