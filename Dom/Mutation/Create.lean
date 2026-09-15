import Dom.Basic.Fresh
import Dom.Basic.State
import Dom.Attribute.Name

/-!
# node を作る（§4.5）

`Document` の factory method。model はこれまで node を作らず、初期状態として
与えられた木を動かすだけだった。ここから作れるようにする。

**新しい id は木から導く**（`Dom/Basic/Fresh.lean`）。状態に allocator を足さないので、
`AdmissibleDOMState` の成分は増えない。

受け手が Document でないときは `TypeError` を返す。仕様では `Document` の method
なので受け手は必ず Document だが、model は id を受け取るので、
WebIDL の受け手検査に当たるものをここで行う
（attribute の method が Element を要求するのと同じ扱い。
`docs/threats-to-validity.md` の「WebIDL の TypeError」を参照）。

`createProcessingInstruction` と `createCDATASection` はまだ無い。前者の target は
仕様が Name production を参照しており、model はその production を持たない。
-/

namespace Dom

/-- store に node を一つ足す。 -/
def Tree.insertNode (t : Tree) (n : NodeId) (d : NodeData) : Tree :=
  ⟨t.nodes.insert n d⟩

@[simp] theorem get?_insertNode_self (t : Tree) (n : NodeId) (d : NodeData) :
    (t.insertNode n d).get? n = some d := by
  simp [Tree.insertNode, Tree.get?]

theorem get?_insertNode_ne (t : Tree) {n m : NodeId} (h : m ≠ n) (d : NodeData) :
    (t.insertNode n d).get? m = t.get? m := by
  simp [Tree.insertNode, Tree.get?, NodeStore.get?_insert_ne _ h.symm]

/-- 受け手が Document であることを確かめる。 -/
def requireDocument (t : Tree) (doc : NodeId) : Except DOMException NodeData :=
  match t.get? doc with
  | none => .error .typeError
  | some dd => if dd.kind == .document then .ok dd else .error .typeError

/-- 作った node を木に入れて、id と新しい状態を返す。 -/
def withFresh (s : DOMState) (d : NodeData) : NodeId × DOMState :=
  let n := freshId s.tree
  (n, s.withTree (s.tree.insertNode n d))

/-! ## 名前を持たない node -/

/-- DOM Standard §4.5 `createTextNode(data)`。 -/
def createTextNode (s : DOMState) (doc : NodeId) (data : String) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ => .ok (withFresh s { kind := .text, ownerDocument := doc, data := data })

/-- DOM Standard §4.5 `createComment(data)`。 -/
def createComment (s : DOMState) (doc : NodeId) (data : String) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ => .ok (withFresh s { kind := .comment, ownerDocument := doc, data := data })

/-- DOM Standard §4.5 `createDocumentFragment()`。 -/
def createDocumentFragment (s : DOMState) (doc : NodeId) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ => .ok (withFresh s { kind := .documentFragment, ownerDocument := doc })

/-! ## element -/

/--
DOM Standard §4.5 `createElement(localName)`。

step 2 の ASCII lowercase と step 4 の namespace は、どちらも
「this が HTML document か」で決まる。custom element（step 3 と step 5 の `is`）は
model の対象外である。
-/
def createElement (s : DOMState) (doc : NodeId) (localName : String) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok dd =>
    -- step 1
    if !isValidElementLocalName localName then .error .invalidCharacterError
    else
      -- step 2 と step 4。どちらも「this が HTML document か」で決まる。
      .ok (withFresh s
        { kind := .element, ownerDocument := doc,
          «namespace» := if dd.isHTMLDocument then some htmlNamespace else none,
          localName := if dd.isHTMLDocument then asciiLowercase localName else localName })

/--
DOM Standard §4.5 `createElementNS(namespace, qualifiedName)`。

§1.3 "validate and extract"（context は "element"）を通してから element を作る。
-/
def createElementNS (s : DOMState) (doc : NodeId) («namespace» : Option String)
    (qualifiedName : String) : Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match validateAndExtractElement «namespace» qualifiedName with
    | .error e => .error e
    | .ok (ns, pfx, localName) =>
      .ok (withFresh s
        { kind := .element, ownerDocument := doc, «namespace» := ns, «prefix» := pfx,
          localName := localName })

end Dom
