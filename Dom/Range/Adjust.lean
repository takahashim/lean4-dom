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

/-! ### `rangeMoveOutOfSubtree` / `rangeShiftAfterRemove` の値 -/

theorem rangeMoveOutOfSubtree_eq (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) :
    rangeMoveOutOfSubtree t node parent index bp =
      if isInclusiveAncestorOf t node bp.node then { node := parent, offset := index }
      else bp := rfl

theorem rangeMoveOutOfSubtree_pos {t : Tree} {node parent : NodeId} {index : Nat}
    {bp : BoundaryPoint} (h : isInclusiveAncestorOf t node bp.node = true) :
    rangeMoveOutOfSubtree t node parent index bp = { node := parent, offset := index } := by
  rw [rangeMoveOutOfSubtree_eq, if_pos h]

theorem rangeMoveOutOfSubtree_neg {t : Tree} {node parent : NodeId} {index : Nat}
    {bp : BoundaryPoint} (h : isInclusiveAncestorOf t node bp.node = false) :
    rangeMoveOutOfSubtree t node parent index bp = bp := by
  rw [rangeMoveOutOfSubtree_eq, if_neg (by rw [h]; simp)]

theorem rangeShiftAfterRemove_eq (parent : NodeId) (index : Nat) (bp : BoundaryPoint) :
    rangeShiftAfterRemove parent index bp =
      if bp.node = parent ∧ index < bp.offset then { bp with offset := bp.offset - 1 }
      else bp := rfl

theorem rangeShiftAfterRemove_pos {parent : NodeId} {index : Nat} {bp : BoundaryPoint}
    (hn : bp.node = parent) (hlt : index < bp.offset) :
    rangeShiftAfterRemove parent index bp = { bp with offset := bp.offset - 1 } := by
  rw [rangeShiftAfterRemove_eq, if_pos ⟨hn, hlt⟩]

theorem rangeShiftAfterRemove_neg {parent : NodeId} {index : Nat} {bp : BoundaryPoint}
    (h : ¬ (bp.node = parent ∧ index < bp.offset)) :
    rangeShiftAfterRemove parent index bp = bp := by
  rw [rangeShiftAfterRemove_eq, if_neg h]

/--
**offset をずらしても boundary point の node は変わらない。**

step 5-6 が step 3-4 の条件に影響しないのはこれが理由である。
`simp` 補題にしてあるので、この二つを合成した証明が合成の順序に依らずに書ける。
-/
@[simp] theorem rangeShiftAfterRemove_node (parent : NodeId) (index : Nat) (bp : BoundaryPoint) :
    (rangeShiftAfterRemove parent index bp).node = bp.node := by
  unfold rangeShiftAfterRemove; split <;> rfl

/--
DOM Standard §5.5 "live range pre-remove steps"。

`node` の removal の直前に走る。仕様の step 順に、まず部分木の外へ移し、次に offset をずらす。
step 3-4 で移した boundary point の offset はちょうど `index` になるので、
step 5-6 の条件（`index` より大きい）には当てはまらない。
-/
def liveRangePreRemoveBP (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) : BoundaryPoint :=
  rangeShiftAfterRemove parent index (rangeMoveOutOfSubtree t node parent index bp)

/-- 削除される部分木の中を指していた点は `(parent, index)` に移る。 -/
theorem liveRangePreRemoveBP_pos {t : Tree} {node parent : NodeId} {index : Nat}
    {bp : BoundaryPoint} (h : isInclusiveAncestorOf t node bp.node = true) :
    liveRangePreRemoveBP t node parent index bp = { node := parent, offset := index } := by
  unfold liveRangePreRemoveBP
  rw [rangeMoveOutOfSubtree_pos h, rangeShiftAfterRemove_eq]
  by_cases hi : index < index
  · omega
  · rw [if_neg (by simp [hi])]

/-- 部分木の外を指していた点には、ずらす調整だけが効く。 -/
theorem liveRangePreRemoveBP_neg {t : Tree} {node parent : NodeId} {index : Nat}
    {bp : BoundaryPoint} (h : isInclusiveAncestorOf t node bp.node = false) :
    liveRangePreRemoveBP t node parent index bp = rangeShiftAfterRemove parent index bp := by
  unfold liveRangePreRemoveBP
  rw [rangeMoveOutOfSubtree_neg h]

/--
**`liveRangePreRemoveBP` が何を返すかを、合成の形に依らずに言ったもの。**

証明はこの補題だけを使えばよく、`unfold` で本体を開く必要が無い。
つまりこれが `liveRangePreRemoveBP` の「interface」で、二つの step をどちらの順で
合成したかは「実装の詳細」になる。本体の書き方を変えたとき、直すのは
この補題の証明だけで済む（`docs/theorems.md` の「証明が定義の形に結合していないか」）。
-/
theorem liveRangePreRemoveBP_eq (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) :
    liveRangePreRemoveBP t node parent index bp =
      if isInclusiveAncestorOf t node bp.node then { node := parent, offset := index }
      else rangeShiftAfterRemove parent index bp := by
  unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
  cases hin : isInclusiveAncestorOf t node bp.node with
  | true => simp [rangeShiftAfterRemove]
  | false => simp

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

/-- 末尾への挿入では range の調整は要らない（step 5 は「If child is non-null」で囲まれている）。 -/
@[simp] theorem liveRangeInsertAdjust_none (s : DOMState) (p : NodeId) (k : Nat) :
    liveRangeInsertAdjust s p none k = s := rfl

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
