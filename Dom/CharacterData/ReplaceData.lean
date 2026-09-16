import Dom.Range.Adjust
import Dom.Observer.Record

/-!
# CharacterData

DOM Standard §4.10 `CharacterData` の `replace data` と、その wrapper を定義する。

offset と長さは仕様どおり UTF-16 の code unit で数える（`Dom.Utf16`）。
surrogate pair の途中で文字列を切る操作だけは Lean の `String` で表せないので、
`DOMException.outsideModel` を返して model の対象外であることを示す。
boundary point が pair の途中を指すこと自体は扱える（数値として持つだけで文字列を切らない）。
-/

namespace Dom

theorem NodeData.length_characterData {d : NodeData} (h : d.kind.isCharacterData = true) :
    d.length = Utf16.length d.data := by
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

code unit の `offset` の直後に `data` を挿入し、そこから `count` code unit を取り除く。
`offset` か `offset + count` が surrogate pair の途中なら、
結果は lone surrogate を含む列になり `String` では表せないので `none` を返す。
-/
def spliceData? (old : String) (offset count : Nat) (data : String) : Option String :=
  match Utf16.splitAt? old.toList offset with
  | none => none
  | some (pre, rest) =>
    match Utf16.splitAt? rest count with
    | none => none
    | some (_, post) => some (String.ofList (pre ++ data.toList ++ post))

/--
切れたなら、長さの等式が従う。

Range の保存証明はこの等式だけを使うので、
「pair を割らない」という条件を Range 側へ持ち出す必要はない。
-/
theorem length_spliceData? {old : String} {offset count : Nat} {data : String} {s : String}
    (h : spliceData? old offset count data = some s) :
    Utf16.length s + count = Utf16.length old + Utf16.length data := by
  unfold spliceData? at h
  split at h
  · simp at h
  · next pre rest hpre =>
    split at h
    · simp at h
    · next mid post hmid =>
      rw [← Option.some.inj h]
      have hpre' := Utf16.splitAt?_spec hpre
      have hmid' := Utf16.splitAt?_spec hmid
      have hrest := Utf16.splitAt?_le hmid
      have hold := Utf16.splitAt?_le hpre
      show Utf16.lengthOfList (String.ofList (pre ++ data.toList ++ post)).toList + count = _
      rw [String.toList_ofList, Utf16.lengthOfList_append, Utf16.lengthOfList_append,
        hpre'.2]
      show _ = Utf16.length old + Utf16.length data
      unfold Utf16.length
      omega

/-- DOM Standard §4.10 replace data の step 8-11。 -/
def replaceDataAdjustBP (n : NodeId) (offset count newLen : Nat) (bp : BoundaryPoint) :
    BoundaryPoint :=
  if bp.node ≠ n then bp
  else if offset < bp.offset ∧ bp.offset ≤ offset + count then { bp with offset := offset }
  else if offset + count < bp.offset then { bp with offset := bp.offset + newLen - count }
  else bp

/--
**置き換える範囲のちょうど先頭を指す boundary point は動かない。**

§4.10 step 8 は「start offset が `offset` **より大きく**、`offset + count` 以下」の
range だけを動かす。`offset` ちょうどのものは条件に入らないが、入れたとしても
移す先が `offset` なので結果は同じである。だから実装が条件を `≤` で書いても観測できない。

差分テストで `<` を `≤` に変えても不一致が出ないのはこのためである
（`docs/status.md` の「定理が落ちても観測できるとは限らない」）。
-/
theorem replaceDataAdjustBP_at_start (n : NodeId) (offset count newLen : Nat)
    (bp : BoundaryPoint) (hn : bp.node = n) (ho : bp.offset = offset) :
    replaceDataAdjustBP n offset count newLen bp = bp := by
  unfold replaceDataAdjustBP
  rw [if_neg (by simp [hn])]
  rw [if_neg (by omega), if_neg (by omega)]

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
      match spliceData? d.data offset (adjustedCount d.length offset count) data with
      -- surrogate pair の途中で切る要求。仕様は定義しているが model では表せない。
      | none => .error .outsideModel
      | some spliced =>
        let c := adjustedCount d.length offset count
        -- step 4。record は data を変える前に、変える前の値を oldValue として積む。
        let s₀ := queueCharacterDataRecord s n d.data
        -- step 5-9
        .ok { s₀ with
                tree :=
                  { s.tree with
                      nodes := s.tree.nodes.insert n
                        { d with data := spliced } }
                ranges := s.ranges.map (replaceDataAdjustRange n offset c (Utf16.length data)) }

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
    else
      -- 切り出しも scalar 境界でしか定義できない。
      match Utf16.splitAt? d.data.toList offset with
      | none => .error .outsideModel
      | some (_, rest) =>
        match Utf16.splitAt? rest (adjustedCount d.length offset count) with
        | none => .error .outsideModel
        | some (mid, _) => .ok (String.ofList mid)

end Dom
