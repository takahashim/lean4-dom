import Dom.Spec.RangeQuery
import Dom.Spec.CharacterDataResult

/-!
# `Range.deleteContents()` の関係意味論（§5.5）

`replace` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは `Dom/Spec/RangeDeleteSound.lean` で証明する。

step 9 と step 11 で `ReplaceDataSpec` を、step 10 で `RemoveEachSpec` を composition する。
「contained」と step 5-7 の新しい boundary point は §5.3 の `BPBefore`
（`Dom/Spec/RangeQuery.lean`）と §4.2 の語彙で書き、実行側の `bpPosition` や
`containedInRange` は使わない。

## 前提

仕様の live range は start と end が同じ root にあり、start が end の前か等しい。
step 7 の「parent が null になるまで上る」はその前提で終わる（root は end node の
inclusive ancestor なので、その手前で止まる）。定理はこの前提（`RangeValid`）を仮定する。
-/

namespace Dom.Spec

open Dom

/--
**§5.5 contained。**

node の root が range の root で、(node, 0) が start の after、
(node, node の length) が end の before であること。
-/
def Contained (t : Tree) (r : RangeState) (n : NodeId) : Prop :=
  (∃ d, t.get? n = some d) ∧ root t n = root t r.start.node ∧
    BPBefore t r.start ⟨n, 0⟩ ∧ BPBefore t ⟨n, lengthOf t n⟩ r.«end»

/--
**step 4：nodes to remove。**

range に contained な node のうち、parent も contained なものを除いたものを、tree order で並べた列。
-/
def NodesToRemove (t : Tree) (r : RangeState) (l : List NodeId) : Prop :=
  (∀ n, n ∈ l ↔ Contained t r n ∧ ∀ p, parentOf t n = some p → ¬ Contained t r p) ∧
    l.Pairwise (PrecedesStruct t)

/--
**step 5-7：new node と new offset。**

6. original start node が original end node の inclusive ancestor なら、original start。
7. そうでなければ、reference node を original start node から始めて、parent が
   original end node の inclusive ancestor になるまで上る。new node はその parent、
   new offset は reference node の index + 1。

step 7 の loop が止まる reference node は、「original start node の inclusive ancestor で、
自身は original end node の inclusive ancestor でなく、parent はそうである」ものとして
一つに決まる（start node の inclusive ancestor は一列に並ぶので）。
-/
def DeleteNewBP (t : Tree) (r : RangeState) (bp : BoundaryPoint) : Prop :=
  (InclusiveAncestor t r.start.node r.«end».node ∧ bp = r.start) ∨
  (¬ InclusiveAncestor t r.start.node r.«end».node ∧
    ∃ ref p i, InclusiveAncestor t ref r.start.node ∧ ¬ InclusiveAncestor t ref r.«end».node ∧
      parentOf t ref = some p ∧ InclusiveAncestor t p r.«end».node ∧ index t ref = some i ∧
      bp = ⟨p, i + 1⟩)

/--
step 9 / step 11 の「CharacterData なら replace data」。

CharacterData でなければ何もしない。CharacterData なら replace data の結果をそのまま返す
（失敗も含む）。
-/
def ReplaceDataIfCharacterData (s : DOMState) (n : NodeId) (offset count : Nat) :
    Except DOMException DOMState → Prop
  | res => (¬ IsCharacterData s.tree n ∧ res = .ok s) ∨
    (IsCharacterData s.tree n ∧ ReplaceDataResult s n offset count "" res)

/-- 失敗したらそこで止め、成功したら次へ渡す。 -/
def AndThen (r : Except DOMException DOMState → Prop)
    (next : DOMState → Except DOMException DOMState → Prop) :
    Except DOMException DOMState → Prop
  | res => (∃ e, r (.error e) ∧ res = .error e) ∨ (∃ s₁, r (.ok s₁) ∧ next s₁ res)

/--
**§5.5 `deleteContents()` の、結果まで含めた関係。**

`r` は `this`（`s.ranges` の `i` 番目）である。step 番号は固定版の本文（`docs/spec-version.md`）に合わせる。

step 8 は、step 9-11 より **前に** `this` の start と end を (newNode, newOffset) に置く。
そのあと step 9-11 の replace data と remove が live range を調整するので、`this` もその調整を受ける。
実行関数は step 9-11 を先に走らせてから点を置くが、その点が step 9-11 の調整で動かないので
結果は同じになる（`Dom/Spec/RangeDeleteSound.lean`）。
-/
def DeleteContentsResult (s : DOMState) (i : Nat) (r : RangeState) :
    Except DOMException DOMState → Prop
  | res =>
    -- step 1
    (r.start = r.«end» ∧ res = .ok s) ∨
    -- step 3
    (r.start ≠ r.«end» ∧ r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node ∧
      ReplaceDataResult s r.start.node r.start.offset (r.«end».offset - r.start.offset) "" res) ∨
    (r.start ≠ r.«end» ∧ ¬ (r.start.node = r.«end».node ∧ IsCharacterData s.tree r.start.node) ∧
      ∃ (toRemove : List NodeId) (bp : BoundaryPoint),
        -- step 4
        NodesToRemove s.tree r toRemove ∧
        -- step 5-7
        DeleteNewBP s.tree r bp ∧
        -- step 8 で this を (newNode, newOffset) に置き、step 9 を走らせる
        AndThen (ReplaceDataIfCharacterData { s with ranges := s.ranges.set i ⟨bp, bp⟩ }
            r.start.node r.start.offset (lengthOf s.tree r.start.node - r.start.offset))
          (fun s₁ res₁ =>
            -- step 10
            ∃ s₂, RemoveEachSpec s₁ toRemove false s₂ ∧
              -- step 11
              AndThen (ReplaceDataIfCharacterData s₂ r.«end».node 0 r.«end».offset)
                (fun s₃ res₃ => res₃ = .ok s₃)
                res₁)
          res)

end Dom.Spec
