import Dom.Mutation.Api
import Dom.Mutation.Create
import Dom.CharacterData.ReplaceData

/-!
# `textContent` と `nodeValue` の setter（§4.4）

"set text content" と "string replace all"、`nodeValue` の setter。`Attr` の枝は
"set an existing attribute value"（`Dom/Attribute/AsNode.lean` の `setAttrValue`）で、harness が
`Attr` を受け手にした `setTextContent`・`setNodeValue` をそちらへ読み替える。
-/

namespace Dom

/--
DOM Standard §4.4 "string replace all"。文字列が空でなければ、parent の node document を node document に
持つ Text を作り（step 2）、それで replace all する（step 3）。空なら null で replace all する。
-/
def stringReplaceAll (s : DOMState) (string : String) (parent : NodeId) :
    Except DOMException DOMState :=
  match s.tree.get? parent with
  | none => .error .notFoundError
  | some d =>
    if string.isEmpty then replaceAll s none parent
    else
      match createTextNode s d.ownerDocument string with
      | .error e => .error e
      | .ok (n, s₁) => replaceAll s₁ (some n) parent

/--
DOM Standard §4.4 "set text content"（`Attr` 以外）。DocumentFragment と Element は string replace all、
CharacterData は replace data（offset 0、length、value）、それ以外（Document・DocumentType）は何もしない。
-/
def setTextContent (s : DOMState) (n : NodeId) (value : String) : Except DOMException DOMState :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d =>
    if d.kind == .documentFragment || d.kind == .element then stringReplaceAll s value n
    else if d.kind.isCharacterData then replaceData s n 0 d.length value
    else .ok s

/--
DOM Standard §4.4 `nodeValue` の setter（`Attr` 以外）。CharacterData は replace data（offset 0、length、value）、
それ以外は何もしない。
-/
def setNodeValue (s : DOMState) (n : NodeId) (value : String) : Except DOMException DOMState :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d => if d.kind.isCharacterData then replaceData s n 0 d.length value else .ok s

end Dom
