import Dom.Spec.RangeDelete

/-!
# `Range.insertNode(node)` の関係意味論（§5.5 insert）

step 6 で `PreInsertValidity` を、step 9 で `RemoveSpec` を、step 12 で `PreInsertResult` を
composition する。

## model の対象外

step 7（start node が Text なら start offset で split する）は Text を分割して新しい node を
作るので、model の対象外である。関係は step 6 の validity までを書き、それを通れば
`outsideModel` を返すとする。「Text node」は CDATASection を含む（`IsText`）。

## step 10-11 の newOffset

newOffset は step 9 の removal の後、step 12 の pre-insert の前の木で決まる
（reference node の index か、reference node が null なら parent の length に、
入る node の数を足したもの）。
-/

namespace Dom.Spec

open Dom

/-- step 4：`n` の子のうち index が `offset` のもの。無ければ null。 -/
def ChildAtOffset (t : Tree) (n : NodeId) (offset : Nat) : Option NodeId → Prop
  | some c => parentOf t c = some n ∧ index t c = some offset
  | none => ∀ c, parentOf t c = some n → index t c ≠ some offset

/--
step 10-11：newOffset。

reference node が null なら parent の length、そうでなければ reference node の index。
そこに、node が DocumentFragment ならその length を、そうでなければ 1 を足す。
-/
def NewOffset (t : Tree) (parent : NodeId) (ref : Option NodeId) (node : NodeId)
    (n : Nat) : Prop :=
  ∃ base, ((ref = none ∧ base = lengthOf t parent) ∨
      (∃ c, ref = some c ∧ index t c = some base)) ∧
    ((KindIs t node .documentFragment ∧ n = base + lengthOf t node) ∨
      (¬ KindIs t node .documentFragment ∧ n = base + 1))

/-- step 1 の条件。 -/
def InsertNodeHierarchyError (t : Tree) (start node : NodeId) : Prop :=
  KindIs t start .processingInstruction ∨ KindIs t start .comment ∨
    (IsText t start ∧ parentOf t start = none) ∨ start = node

/--
step 8-13（start node が Text でないとき）。

8. node が reference node なら、reference node をその next sibling にする。
9. node に parent があれば外す。
10-11. newOffset を決める。
12. node を parent の reference node の前に pre-insert する。
13. range が collapsed なら、end を (parent, newOffset) にする。
-/
def InsertNodeTail (s : DOMState) (i : Nat) (parent node : NodeId) (ref : Option NodeId) :
    Except DOMException DOMState → Prop
  | res =>
    ∃ ref', ((ref = some node ∧ ref' = nextSibling s.tree node) ∨
        (ref ≠ some node ∧ ref' = ref)) ∧
      ∃ s₁, ((parentOf s.tree node = none ∧ s₁ = s) ∨
          ((∃ p, parentOf s.tree node = some p) ∧ RemoveSpec s node false s₁)) ∧
        ∃ newOffset, NewOffset s₁.tree parent ref' node newOffset ∧
          AndThen (PreInsertResult s₁ node parent ref')
            (fun s₂ res₂ => ∃ r₂, s₂.ranges[i]? = some r₂ ∧
              ((r₂.start = r₂.«end» ∧
                  res₂ = .ok { s₂ with
                    ranges := s₂.ranges.set i { r₂ with «end» := ⟨parent, newOffset⟩ } }) ∨
                (r₂.start ≠ r₂.«end» ∧ res₂ = .ok s₂)))
            res

/--
**§5.5 `insertNode(node)` の、結果まで含めた関係。**

`r` は `this`（`s.ranges` の `i` 番目）である。
-/
def InsertNodeResult (s : DOMState) (i : Nat) (r : RangeState) (node : NodeId) :
    Except DOMException DOMState → Prop
  | res =>
    -- step 1
    (InsertNodeHierarchyError s.tree r.start.node node ∧ res = .error .hierarchyRequestError) ∨
    (¬ InsertNodeHierarchyError s.tree r.start.node node ∧
      -- step 3-7：start node が Text
      ((IsText s.tree r.start.node ∧ ∃ p, parentOf s.tree r.start.node = some p ∧
          ((∃ e, PreInsertValidity s.tree node p (some r.start.node) [] (.error e) ∧
              res = .error e) ∨
            (PreInsertValidity s.tree node p (some r.start.node) [] (.ok ()) ∧
              res = .error .outsideModel))) ∨
        -- step 4-6, 8-13：start node が Text でない
        (¬ IsText s.tree r.start.node ∧ ∃ ref, ChildAtOffset s.tree r.start.node r.start.offset ref ∧
          ((∃ e, PreInsertValidity s.tree node r.start.node ref [] (.error e) ∧ res = .error e) ∨
            (PreInsertValidity s.tree node r.start.node ref [] (.ok ()) ∧
              InsertNodeTail s i r.start.node node ref res)))))

end Dom.Spec
