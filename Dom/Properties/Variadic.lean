import Dom.Mutation.Variadic

/-!
# 引数が node 一つなら、可変長の method は既存の一引数の method と同じである

"convert nodes into a node" は、引数が node 一つなら何もせずにそれを返す（step 2）。
だから `before(n)` などは、変換済みの node を受け取る既存の実行関数（`before` ほか、
`Dom/Mutation/Api.lean`）と同じ結果になる。既存の関係（`BeforeResult` ほか）はこの場合にそのまま使える。
-/

namespace Dom

theorem convertNodesIntoNode_single (s : DOMState) (n doc : NodeId) :
    convertNodesIntoNode s [.node n] doc = .ok (n, [], s) := rfl

theorem afterConvert_nil (s : DOMState) (k : DOMState → Except DOMException DOMState) :
    afterConvert [] s k = withState s (k s) := by
  unfold afterConvert withState
  cases k s <;> rfl

theorem beforeNodes_single (s : DOMState) (this n : NodeId) :
    beforeNodes s this [.node n] = withState s (before s this n) := by
  unfold beforeNodes before
  cases parentOf s.tree this with
  | none => rfl
  | some parent =>
    simp only [convertNodesIntoNode_single, afterConvert_nil]
    rfl

theorem afterNodes_single (s : DOMState) (this n : NodeId) :
    afterNodes s this [.node n] = withState s (after s this n) := by
  unfold afterNodes after
  cases parentOf s.tree this with
  | none => rfl
  | some parent =>
    simp only [convertNodesIntoNode_single, afterConvert_nil]
    rfl

theorem replaceWithNodes_single (s : DOMState) (this n : NodeId) :
    replaceWithNodes s this [.node n] = withState s (replaceWith s this n) := by
  unfold replaceWithNodes replaceWith
  cases hp : parentOf s.tree this with
  | none => rfl
  | some parent =>
    simp only [convertNodesIntoNode_single, afterConvert_nil, hp]
    rfl

theorem appendNodes_single {s : DOMState} {this : NodeId} {td : NodeData}
    (ht : s.tree.get? this = some td) (n : NodeId) :
    appendNodes s this [.node n] = withState s (append s n this) := by
  unfold appendNodes
  simp only [ht, Option.isNone_some, Bool.false_eq_true, if_false, convertNodesIntoNode_single,
    afterConvert_nil]

theorem replaceChildrenNodes_single {s : DOMState} {this : NodeId} {td : NodeData}
    (ht : s.tree.get? this = some td) (n : NodeId) :
    replaceChildrenNodes s this [.node n] = withState s (replaceChildren s this (some n)) := by
  unfold replaceChildrenNodes
  simp only [ht, Option.isNone_some, Bool.false_eq_true, if_false, convertNodesIntoNode_single,
    afterConvert_nil]

end Dom
