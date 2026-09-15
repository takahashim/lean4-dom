import Dom.Spec.Record
import Dom.Basic.Utf16
import Dom.Range.BoundaryPoint

/-!
# `replace data` の関係意味論（§4.10）

`remove` / `insert` と同じ方針。木の形は変えず、
一つの node の data と live range の offset、それに characterData の record を動かす。

step 12（ProcessingInstruction の attribute 更新）と step 13（children changed steps）は
model の対象外である。
-/

namespace Dom.Spec

open Dom

/-- step 3。`offset + count` が length を超えたら、count は length − offset に切り詰める。 -/
def ClampedCount (length offset count c : Nat) : Prop :=
  (length < offset + count ∧ c = length - offset) ∨ (¬(length < offset + count) ∧ c = count)

/--
step 5-7。

`offset` code unit の直後に `data` を入れ、そこから `count` code unit を取り除く。
つまり「前 `offset` 単位」「次の `count` 単位」「残り」に分けて、真ん中を `data` に置き換える。
-/
def DataSpliced (old : String) (offset count : Nat) (data new : String) : Prop :=
  ∃ pre mid post : List Char,
    old.toList = pre ++ mid ++ post ∧ Utf16.lengthOfList pre = offset ∧
      Utf16.lengthOfList mid = count ∧ new.toList = pre ++ data.toList ++ post

/--
step 8-11。boundary point の調整。

* 取り除いた範囲の中を指していたら、その先頭へ寄せる（step 8-9）
* 取り除いた範囲より後ろなら、長さの差だけずらす（step 10-11）
* それ以外は動かない
-/
def DataAdjusted (node : NodeId) (offset count newLen : Nat) (bp bp' : BoundaryPoint) : Prop :=
  (bp.node ≠ node ∧ bp' = bp) ∨
  (bp.node = node ∧ offset < bp.offset ∧ bp.offset ≤ offset + count ∧ bp' = ⟨node, offset⟩) ∨
  (bp.node = node ∧ offset + count < bp.offset ∧
    bp' = ⟨node, bp.offset + newLen - count⟩) ∨
  (bp.node = node ∧ ¬(offset < bp.offset ∧ bp.offset ≤ offset + count) ∧
    ¬(offset + count < bp.offset) ∧ bp' = bp)

/-- 木の効果。`node` の data だけが変わる。 -/
structure DataReplaced (t t' : Tree) (node : NodeId) (new : String) : Prop where
  changed : ∀ d : NodeData, t.get? node = some d → t'.get? node = some { d with data := new }
  others : ∀ m : NodeId, m ≠ node → t'.get? m = t.get? m

/--
**§4.10 "replace data" の関係意味論。**

step 4 の record は **data を変える前の値**を oldValue として積む。
-/
def ReplaceDataSpec (s : DOMState) (node : NodeId) (offset count : Nat) (data : String)
    (s' : DOMState) : Prop :=
  ∃ (d : NodeData) (c : Nat) (new : String) (s₀ : DOMState),
    s.tree.get? node = some d ∧
    d.kind.isCharacterData = true ∧
    offset ≤ d.length ∧
    ClampedCount d.length offset count c ∧
    DataSpliced d.data offset c data new ∧
    -- step 4
    CharacterDataRecordQueued s s₀ node d.data ∧
    -- step 5-7
    DataReplaced s.tree s'.tree node new ∧
    -- step 8-11
    s'.ranges.length = s.ranges.length ∧
    (∀ (i : Nat) (r r' : RangeState), s.ranges[i]? = some r → s'.ranges[i]? = some r' →
      DataAdjusted node offset c (Utf16.length data) r.start r'.start ∧
      DataAdjusted node offset c (Utf16.length data) r.«end» r'.«end») ∧
    -- record 以外の live object は動かない
    s'.observers = s₀.observers ∧ s'.pendingObservers = s₀.pendingObservers ∧
    s'.microtaskQueued = s₀.microtaskQueued ∧ s'.registrations = s.registrations ∧
    s'.iterators = s.iterators

end Dom.Spec
