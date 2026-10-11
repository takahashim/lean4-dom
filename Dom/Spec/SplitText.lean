import Dom.Spec.TextQuery
import Dom.Spec.CharacterDataResult
import Dom.Spec.Create

/-!
# "split a Text node" の関係意味論（§4.11）

step 5 の新しい Text は `CreatesNode` で、step 7.1 の挿入は `InsertSpec`（本文どおり insert で、
pre-insert ではない）で、step 8 は `ReplaceDataResult` で書く。step 7.2-7.5 の live range の調整は
`SplitAdjusted` で書く。どちらも本文の字面どおり、移した先が妥当かを検査しない。
-/

namespace Dom.Spec

open Dom

/--
step 7.2-7.5：一つの boundary point の移し先。`idx` は node の index である。

* node を指し、offset より後ろなら、新しい Text の (offset を引いた位置) へ移す（7.2・7.3）。
* parent を指し、offset が node の index + 1 なら、一つ進める（7.4・7.5）。
* それ以外は動かない。
-/
def SplitAdjusted (node newNode parent : NodeId) (offset idx : Nat) (bp bp' : BoundaryPoint) :
    Prop :=
  (bp.node = node ∧ offset < bp.offset ∧ bp' = ⟨newNode, bp.offset - offset⟩) ∨
  (bp.node = parent ∧ bp.offset = idx + 1 ∧ bp' = ⟨parent, idx + 2⟩) ∨
  (¬ (bp.node = node ∧ offset < bp.offset) ∧ ¬ (bp.node = parent ∧ bp.offset = idx + 1) ∧ bp' = bp)

/-- step 7.2-7.5：live range だけを動かす。 -/
def RangesSplit (s s' : DOMState) (node newNode parent : NodeId) (offset idx : Nat) : Prop :=
  ∃ rs : List RangeState, s' = { s with ranges := rs } ∧ rs.length = s.ranges.length ∧
    ∀ (i : Nat) (r r' : RangeState), s.ranges[i]? = some r → rs[i]? = some r' →
      SplitAdjusted node newNode parent offset idx r.start r'.start ∧
      SplitAdjusted node newNode parent offset idx r.«end» r'.«end»

/--
**§4.11 "split a Text node" の、結果まで含めた関係。** 成功すれば新しい Text と状態を返す。

1-2. offset が length を超えたら IndexSizeError。
3-4. count は length − offset、new data は substring data。
5. new data を data に持つ Text を、node と同じ node document に作る。
6-7. parent があれば、新しい Text を node の next sibling の前に insert し、live range を調整する。
8. node の data を、offset から count 個の code unit を空文字列で置き換えて切る。
-/
def SplitTextResult (s : DOMState) (node : NodeId) (offset : Nat) :
    Except DOMException (NodeId × DOMState) → Prop
  | res => ∃ d, s.tree.get? node = some d ∧ d.kind.isText = true ∧
    -- step 1-2
    ((d.length < offset ∧ res = .error .indexSizeError) ∨
     (offset ≤ d.length ∧
      -- step 3-4
      ((∃ e, SubstringResult s.tree node offset (d.length - offset) (.error e) ∧ res = .error e) ∨
       (∃ newData newNode s₁, SubstringResult s.tree node offset (d.length - offset) (.ok newData) ∧
         -- step 5
         CreatesNode s newNode s₁ { kind := .text, ownerDocument := d.ownerDocument, data := newData } ∧
         ∃ s₃, ((parentOf s.tree node = none ∧ s₃ = s₁) ∨
           -- step 7
           (∃ p s₂ idx, parentOf s.tree node = some p ∧
             InsertSpec s₁ newNode p (nextSibling s₁.tree node) false s₂ ∧
             index s₂.tree node = some idx ∧
             RangesSplit s₂ s₃ node newNode p offset idx)) ∧
         -- step 8
         ((∃ e, ReplaceDataResult s₃ node offset (d.length - offset) "" (.error e) ∧ res = .error e) ∨
          (∃ s', ReplaceDataResult s₃ node offset (d.length - offset) "" (.ok s') ∧
            res = .ok (newNode, s')))))))

end Dom.Spec
