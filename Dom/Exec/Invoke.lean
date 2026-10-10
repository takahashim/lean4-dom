import Dom.Exec.Types
import Dom.Attribute.Reflect
import Dom.Attribute.AsNode

/-!
# method を呼ぶ層の WebIDL の検査

DOM の method は WebIDL を通して呼ばれる。method steps に入る前に、WebIDL は次を行う。

* **this の検査**：this が method を持つ interface を実装していなければ `TypeError`。
* **引数の変換**：`Node` を取る引数に null を渡す、`Attr` を取る引数に `Attr` でないものを渡す、
  などは `TypeError`。

この検査は method steps より前に起きるので、algorithm の結果より優先する。たとえば
`Range.setStart(null, 木より大きい offset)` は `IndexSizeError` ではなく `TypeError` になる。

algorithm の層（`applyOperation` が呼ぶ実行関数）は `DOMException` だけを返す。この層を通れば、
algorithm の側に残した interface の guard（`requireElement` ほか）は効かない。

対象は model の操作が呼ぶ method に限る。interface の判定は node の kind で行う。
木に無い id は WebIDL の問題ではなく model の都合なので、ここでは通し、algorithm の層が
`NotFoundError` にする。
-/

namespace Dom.Exec

open Dom

/-- this か引数の node が、interface を実装しているか。木に無い id はここでは問わない。 -/
def implementsIface (t : Tree) (n : Nat) (p : NodeData → Bool) : Bool :=
  match t.get? ⟨n⟩ with
  | none => true
  | some d => p d

/-- `ParentNode`（Document・DocumentFragment・Element）。 -/
def isParentNode (d : NodeData) : Bool := d.kind.canHaveChildren

/-- `ChildNode`（Element・CharacterData・DocumentType）。 -/
def isChildNode (d : NodeData) : Bool :=
  d.kind == .element || d.kind.isCharacterData || d.kind == .documentType

/-- `Element`。 -/
def isElement (d : NodeData) : Bool := d.kind == .element

/-- `Document`。 -/
def isDocument (d : NodeData) : Bool := d.kind == .document

/-- `NonElementParentNode`（Document・DocumentFragment）。 -/
def isNonElementParentNode (d : NodeData) : Bool :=
  d.kind == .document || d.kind == .documentFragment

/-- `getElementsByClassName()` を持つもの（Document・Element）。 -/
def isDocumentOrElement (d : NodeData) : Bool := d.kind == .document || d.kind == .element

/-- reflect する IDL attribute を持つ Element。持たない object では property が undefined になる。 -/
def hasReflected (r : ReflectSpec) (d : NodeData) : Bool := isElement d && r.iface.applies d

/--
**WebIDL の検査を通るか。** 通らなければ、method を呼ぶ層は `TypeError` を返す。

`observe` の step 3-6 の TypeError は WebIDL ではなく method steps のものなので、ここには入れない
（`MutationObserver.observeMethod`）。
-/
def idlCheck (s : DOMState) : Operation → Bool
  -- ParentNode の method
  | .moveBefore p _ _ => implementsIface s.tree p isParentNode
  | .replaceChildren p _ => implementsIface s.tree p isParentNode
  | .prepend p _ => implementsIface s.tree p isParentNode
  | .append p _ => implementsIface s.tree p isParentNode
  -- ChildNode の method
  | .before t _ => implementsIface s.tree t isChildNode
  | .after t _ => implementsIface s.tree t isChildNode
  | .replaceWith t _ => implementsIface s.tree t isChildNode
  | .querySelector n _ => implementsIface s.tree n isParentNode
  | .querySelectorAll n _ => implementsIface s.tree n isParentNode
  | .childrenNamedItem n _ => implementsIface s.tree n isParentNode
  -- Element の method
  | .matchesSelector e _ => implementsIface s.tree e isElement
  | .closest e _ => implementsIface s.tree e isElement
  | .setAttribute e _ _ => implementsIface s.tree e isElement
  | .setAttributeNS e _ _ _ => implementsIface s.tree e isElement
  | .removeAttribute e _ => implementsIface s.tree e isElement
  | .removeAttributeNS e _ _ => implementsIface s.tree e isElement
  | .toggleAttribute e _ _ => implementsIface s.tree e isElement
  | .getAttributeNode e _ => implementsIface s.tree e isElement
  | .getAttributeNodeNS e _ _ => implementsIface s.tree e isElement
  -- 引数の `Attr` も変換する。`Attr` でなければ TypeError。
  | .setAttributeNode e a => implementsIface s.tree e isElement && (findAttr s ⟨a⟩).isSome
  | .removeAttributeNode e _ => implementsIface s.tree e isElement
  | .removeNamedItem e _ => implementsIface s.tree e isElement
  | .classListAdd e _ => implementsIface s.tree e isElement
  | .classListRemove e _ => implementsIface s.tree e isElement
  | .classListToggle e _ _ => implementsIface s.tree e isElement
  | .classListReplace e _ _ => implementsIface s.tree e isElement
  | .classListContains e _ => implementsIface s.tree e isElement
  -- reflect と dataset は、その IDL attribute を持つ Element に限る
  | .getReflected e _ r => implementsIface s.tree e (hasReflected r)
  | .setReflected e _ r _ => implementsIface s.tree e (hasReflected r)
  | .setReflectedBool e _ r _ => implementsIface s.tree e (hasReflected r)
  | .datasetGet e _ => implementsIface s.tree e (hasReflected ⟨"", .string, .htmlOrSvg⟩)
  | .datasetSet e _ _ => implementsIface s.tree e (hasReflected ⟨"", .string, .htmlOrSvg⟩)
  | .datasetDelete e _ => implementsIface s.tree e (hasReflected ⟨"", .string, .htmlOrSvg⟩)
  | .datasetKeys e => implementsIface s.tree e (hasReflected ⟨"", .string, .htmlOrSvg⟩)
  -- Document の method
  | .createElement d _ => implementsIface s.tree d isDocument
  | .createElementNS d _ _ => implementsIface s.tree d isDocument
  | .createTextNode d _ => implementsIface s.tree d isDocument
  | .createComment d _ => implementsIface s.tree d isDocument
  | .createDocumentFragment d => implementsIface s.tree d isDocument
  -- options の `(boolean or ImportNodeOptions)` への変換（`customElementRegistry` があれば TypeError）
  | .importNode d _ o => implementsIface s.tree d isDocument && (Idl.toImportNodeOptions o).isSome
  | .adoptNode d _ => implementsIface s.tree d isDocument
  | .createAttribute d _ => implementsIface s.tree d isDocument
  | .createAttributeNS d _ _ => implementsIface s.tree d isDocument
  | .adoptAttr d _ => implementsIface s.tree d isDocument
  | .importAttr d _ => implementsIface s.tree d isDocument
  | .getElementsByName n _ => implementsIface s.tree n isDocument
  | .getElementById n _ => implementsIface s.tree n isNonElementParentNode
  | .getElementsByClassName n _ => implementsIface s.tree n isDocumentOrElement
  -- options の `(AddEventListenerOptions or boolean)` への変換（`signal` があれば TypeError）
  | .addEventListener _ _ _ o => (Idl.toAddEventListenerOptions o).isSome
  -- `Range` の method の `Node` 引数（null は TypeError）
  | .rangeSetStart _ n _ => n.isSome
  | .rangeSetEnd _ n _ => n.isSome
  | .rangeSetStartSibling _ n _ => n.isSome
  | .rangeSetEndSibling _ n _ => n.isSome
  | .rangeSelectNode _ n => n.isSome
  | .rangeSelectNodeContents _ n => n.isSome
  | .rangeIsPointInRange _ n _ => n.isSome
  | .rangeIntersectsNode _ n => n.isSome
  | .rangeComparePoint _ n _ => n.isSome
  | .rangeInsertNode _ n => n.isSome
  -- interface 型への引数の変換の失敗
  | .argumentTypeError _ => false
  | _ => true

/--
**op の method が必須とする引数の個数**（scenario の op 名で引く）（固定版の IDL の、`optional` でも可変長でもない引数の数）。
`argc` を書ける op だけを挙げる。`Node?` のような nullable の引数も、`optional` でなければ必須である。
-/
def requiredArgs : String → Option Nat
  | "appendChild" | "removeChild" | "adoptNode" | "importNode" => some 1
  | "insertBefore" | "replaceChild" | "moveBefore" => some 2
  | "replaceData" => some 3
  | "insertData" | "deleteData" | "substringData" => some 2
  | "appendData" => some 1
  | "createElement" | "createTextNode" | "createComment" | "createAttribute" => some 1
  | "createElementNS" | "createAttributeNS" => some 2
  | "cloneNode" | "normalize" | "rangeCollapse" => some 0
  | "getAttribute" | "hasAttribute" | "removeAttribute" | "getAttributeNode" | "toggleAttribute" => some 1
  | "setAttribute" | "removeAttributeNS" | "getAttributeNodeNS" => some 2
  | "setAttributeNS" => some 3
  | "setAttributeNode" | "removeAttributeNode" => some 1
  | "querySelector" | "querySelectorAll" | "matches" | "closest" => some 1
  | "getElementById" | "getElementsByClassName" | "getElementsByName" => some 1
  | "lookupNamespaceURI" | "lookupPrefix" | "isDefaultNamespace" => some 1
  | "compareDocumentPosition" | "nodeContains" | "isEqualNode" => some 1
  | "addEventListener" | "removeEventListener" => some 2
  | "classListToggle" | "classListContains" => some 1
  | "classListReplace" => some 2
  | "observe" => some 1
  | "rangeSetStart" | "rangeSetEnd" | "rangeIsPointInRange" | "rangeComparePoint"
  | "rangeCompareBoundaryPoints" => some 2
  | "rangeSetStartBefore" | "rangeSetStartAfter" | "rangeSetEndBefore" | "rangeSetEndAfter"
  | "rangeSelectNode" | "rangeSelectNodeContents" | "rangeIntersectsNode" | "rangeInsertNode" => some 1
  | _ => none

end Dom.Exec
