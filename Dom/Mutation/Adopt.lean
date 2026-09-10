import Dom.Basic.Exception
import Dom.Basic.WellFormed

/-!
# primitive mutation：node document の付け替え

PLAN §5.1 の三つの primitive のうち、木を変えずに node document だけを変えるもの。

仕様の adopt（DOM Standard §4.5 "adopt"）は「parent があれば remove する」を含むが、
その remove は Range や NodeIterator の調整を伴う完全な remove である。
そのため Phase 2 の primitive は木だけを変える `setOwnerDocument` にとどめ、
仕様どおりの adopt は Phase 3 で組み立てる。
-/

namespace Dom

/--
`n` とその inclusive descendant の node document を `doc` に付け替える。木は変えない。

DOM Standard §4.5 adopt の step 3（"set node's node document to document"）に対応する。
-/
def setOwnerDocument (t : Tree) (n doc : NodeId) : Tree :=
  { nodes :=
      t.nodes.mapValues fun m d =>
        if m ∈ preorder t n then { d with ownerDocument := doc } else d }

theorem get?_setOwnerDocument (t : Tree) (n doc m : NodeId) :
    (setOwnerDocument t n doc).get? m =
      (t.get? m).map fun d => if m ∈ preorder t n then { d with ownerDocument := doc } else d :=
  NodeStore.get?_mapValues t.nodes _ m

end Dom
