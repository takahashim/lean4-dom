import Dom.Range.Adjust
import Dom.Observer.Record

/-!
# CharacterData

DOM Standard §4.10 `CharacterData` の `replace data` と、その wrapper を定義する。

`data` の長さは仕様では UTF-16 の code unit 数だが、
Lean の `String.length` は code point 数である。
BMP の範囲では両者は一致するので、本 model は BMP に限って仕様どおりになる。
differential testing の生成器も BMP の文字しか使わない。
-/

namespace Dom

theorem NodeData.length_characterData {d : NodeData} (h : d.kind.isCharacterData = true) :
    d.length = d.data.length := by
  simp [NodeData.length, h]

/-- DOM Standard §4.10 replace data の step 3。count を length − offset で切り詰める。 -/
def adjustedCount (length offset count : Nat) : Nat :=
  if length < offset + count then length - offset else count

theorem adjustedCount_le {length offset count : Nat} (h : offset ≤ length) :
    offset + adjustedCount length offset count ≤ length := by
  unfold adjustedCount
  split <;> omega

/--
DOM Standard §4.10 replace data の step 5-7。

`offset` の直後に `data` を挿入し、そこから `count` 文字を取り除く。
-/
def spliceData (old : String) (offset count : Nat) (data : String) : String :=
  String.ofList (old.toList.take offset ++ data.toList ++ old.toList.drop (offset + count))

theorem length_spliceData {old : String} {offset count : Nat} {data : String}
    (h1 : offset ≤ old.length) (h2 : offset + count ≤ old.length) :
    (spliceData old offset count data).length + count = old.length + data.length := by
  unfold spliceData
  rw [String.length_ofList]
  simp only [List.length_append, List.length_take, List.length_drop, String.length_toList]
  omega

/-- DOM Standard §4.10 replace data の step 8-11。 -/
def replaceDataAdjustBP (n : NodeId) (offset count newLen : Nat) (bp : BoundaryPoint) :
    BoundaryPoint :=
  if bp.node ≠ n then bp
  else if offset < bp.offset ∧ bp.offset ≤ offset + count then { bp with offset := offset }
  else if offset + count < bp.offset then { bp with offset := bp.offset + newLen - count }
  else bp

def replaceDataAdjustRange (n : NodeId) (offset count newLen : Nat) (r : RangeState) :
    RangeState :=
  { start := replaceDataAdjustBP n offset count newLen r.start
    «end» := replaceDataAdjustBP n offset count newLen r.«end» }

/--
DOM Standard §4.10 "replace data"。

仕様の algorithm には node が CharacterData であるという検査は無い。
`CharacterData` interface の method からしか呼ばれないためである。
本 model は node を kind で区別するので、
CharacterData 以外に対しては `invalidNodeTypeError` を返す。

ProcessingInstruction の attribute 更新と children changed steps は扱わない。
-/
def replaceData (s : DOMState) (n : NodeId) (offset count : Nat) (data : String) :
    Except DOMException DOMState :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d =>
    if !d.kind.isCharacterData then .error .invalidNodeTypeError
    -- step 1-2
    else if d.length < offset then .error .indexSizeError
    else
      -- step 3
      let c := adjustedCount d.length offset count
      -- step 4。record は data を変える前に、変える前の値を oldValue として積む。
      let s₀ := queueCharacterDataRecord s n d.data
      -- step 5-9
      .ok { s₀ with
              tree :=
                { s.tree with
                    nodes := s.tree.nodes.insert n
                      { d with data := spliceData d.data offset c data } }
              ranges := s.ranges.map (replaceDataAdjustRange n offset c data.length) }

/-! ## `CharacterData` の method -/

/-- DOM Standard §4.10 `CharacterData.appendData(data)`。 -/
def appendData (s : DOMState) (n : NodeId) (data : String) : Except DOMException DOMState :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d => replaceData s n d.length 0 data

/-- DOM Standard §4.10 `CharacterData.insertData(offset, data)`。 -/
def insertData (s : DOMState) (n : NodeId) (offset : Nat) (data : String) :
    Except DOMException DOMState :=
  replaceData s n offset 0 data

/-- DOM Standard §4.10 `CharacterData.deleteData(offset, count)`。 -/
def deleteData (s : DOMState) (n : NodeId) (offset count : Nat) : Except DOMException DOMState :=
  replaceData s n offset count ""

/-- DOM Standard §4.10 `CharacterData.data` の setter。 -/
def setData (s : DOMState) (n : NodeId) (data : String) : Except DOMException DOMState :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d => replaceData s n 0 d.length data

/--
DOM Standard §4.10 `CharacterData.substringData(offset, count)`。

木も live object も変えないので `Tree` の上に置く。
-/
def substringData (t : Tree) (n : NodeId) (offset count : Nat) : Except DOMException String :=
  match t.get? n with
  | none => .error .notFoundError
  | some d =>
    if !d.kind.isCharacterData then .error .invalidNodeTypeError
    else if d.length < offset then .error .indexSizeError
    else .ok (String.ofList ((d.data.toList.drop offset).take (adjustedCount d.length offset count)))

end Dom
