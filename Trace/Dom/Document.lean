import Trace.Basic
import Dom
import Dom.Exec.Invoke

/-!
# §4.5 Interface `Document`（§4.5.1 `DOMImplementation`）、§4.6 `DocumentType`、
# §4.7 `DocumentFragment`、§4.8 `ShadowRoot`
-/

namespace Trace.Dom.Document

open Trace

-- 受け手が Document でないときの WebIDL の TypeError は、method を呼ぶ層の `Dom.Exec.idlCheck` が
-- algorithm より先に返す（`DOMException` とは別の型 `IdlException.typeError`）。実行関数に残る受け手の
-- guard は model の都合（不正な id）で、その経路は WebIDL の検査を通った後には通らない。

def entries : List Entry := [
  /- §4.5 -/
  { alg := "dom-document-compatmode"
    impl := [``Dom.inQuirksModeOf] },
  { alg := "dom-document-documentelement"
    impl := [``Dom.documentElement] },
  { alg := "dom-document-getelementsbyclassname"
    impl := [``Dom.getElementsByClassName, ``Dom.orderedSetParse, ``Dom.elementClassesOf,
             ``Dom.receiverInQuirksMode]
    approx := [("*", "live な HTMLCollection ではなく、呼んだ時点の element の列を返す")] },
  { alg := "dom-document-createelement"
    impl := [``Dom.createElement, ``Dom.isValidElementLocalName, ``Dom.Exec.idlCheck]
    omitted := [("3", .customElements)]
    approx := [("4", "content type を持たないので、namespace は「HTML document なら HTML namespace、そうでなければ null」で決める。content type が application/xhtml+xml の XML document でも null になる。runner は HTML document しか作れないので、XML document の側は差分テストで比べていない"),
               ("5", "create an element を呼ばず、`NodeData` を直に作る（is・synchronous custom elements flag・registry は無い）")] },
  { alg := "internal-createelementns-steps"
    impl := [``Dom.createElementNS, ``Dom.validateAndExtractElement]
    omitted := [("2", .customElements)]
    approx := [("3", "create an element を呼ばず、`NodeData` を直に作る（is・registry は無い）")] },
  { alg := "dom-document-createelementns"
    impl := [``Dom.createElementNS, ``Dom.Exec.idlCheck]
    approx := [("*", "options を受けない")] },
  { alg := "dom-document-createdocumentfragment"
    impl := [``Dom.createDocumentFragment] },
  { alg := "dom-document-createtextnode"
    impl := [``Dom.createTextNode] },
  { alg := "dom-document-createcomment"
    impl := [``Dom.createComment] },
  { alg := "dom-document-importnode"
    impl := [``Dom.importNode, ``Dom.importAttr, ``Dom.cloneNodeIn, ``Dom.Exec.idlCheck]
    omitted := [("3", .customElements), ("5.1", .todo "ImportNodeOptions の dictionary の形を受けない（boolean の形だけ）"),
             ("5.2-5.3", .customElements), ("6", .customElements)]
    approx := [("1", "Document だけを弾く。shadow root は model に無いので検査しない"),
               ("7", "fallbackRegistry を渡さない（custom element registry が無い）")] },
  { alg := "concept-node-adopt"
    impl := [``Dom.adopt, ``Dom.setOwnerDocument, ``Dom.NodeData.withOwnerDocument, ``Dom.adoptAttr]
    spec := [``Dom.Spec.AdoptSpec]
    omitted := [("3.2", .shadow), ("3.3.2", .customElements), ("3.3.3", .customElements),
             ("3.4", .hook)]
    approx := [("3", "shadow-including inclusive descendant ではなく inclusive descendant をたどる（shadow tree が無いので同じ集合）")] },
  { alg := "dom-document-adoptnode"
    impl := [``Dom.adoptNode, ``Dom.adoptAttr, ``Dom.Exec.idlCheck]
    omitted := [("2", .shadow)] },
  { alg := "dom-document-createattribute"
    impl := [``Dom.createAttribute, ``Dom.isValidAttributeLocalName, ``Dom.createAttributeIn] },
  { alg := "dom-document-createattributens"
    impl := [``Dom.createAttributeNS, ``Dom.validateAndExtractAttribute, ``Dom.createAttributeIn] },
  /- §4.7 -/
  { alg := "concept-tree-host-including-inclusive-ancestor"
    impl := [``Dom.isInclusiveAncestorOf]
    approx := [("*", "host を見ない。shadow root が無いので inclusive ancestor と同じ")] },
  { alg := "create-a-document-fragment"
    impl := [``Dom.createDocumentFragment] }
]

def exclusions : List Exclusion := [
  /- §4.5 -/
  { target := "create-a-document",
    reason := .todo "Document を作る関数が無い（clone a single node の step 3 だけは `cloneSingle` が `NodeData` を写して作る）。harness の document は scenario が与える" },
  { target := "dom-document-document", reason := .host },
  { target := "dom-document-implementation", reason := .todo "DOMImplementation object を持たない" },
  { target := "dom-document-url", reason := .todo "document の URL を持たない" },
  { target := "dom-document-documenturi", reason := .todo "document の URL を持たない" },
  { target := "dom-document-characterset", reason := .todo "document の encoding を持たない" },
  { target := "dom-document-charset", reason := .todo "document の encoding を持たない" },
  { target := "dom-document-inputencoding", reason := .todo "document の encoding を持たない" },
  { target := "dom-document-contenttype",
    reason := .todo "document の content type を持たない（type は `isHTMLDocument` で持つ）" },
  { target := "dom-document-doctype", reason := .todo "doctype の子を返す関数が無い" },
  { target := "dom-document-getelementsbytagname", reason := .todo "list of elements with qualified name が無い" },
  { target := "dom-document-getelementsbytagnamens",
    reason := .todo "list of elements with namespace and local name が無い" },
  { target := "flatten-element-creation-options", reason := .customElements },
  { target := "dom-document-createcdatasection", reason := .todo "createCDATASection が無い（`Dom/Mutation/Create.lean` の注）" },
  { target := "dom-document-createprocessinginstruction",
    reason := .todo "createProcessingInstruction が無い。target の Name production と ProcessingInstruction の target を model が持たない" },
  { target := "concept-node-adopt-ext", reason := .hook },
  { target := "dom-document-createevent",
    reason := .todo "Event object を作る API が無い（`dispatchEvent` が型・bubbles・cancelable から event を組む）。step 7 の timeStamp は host" },
  { target := "dom-document-createrange",
    reason := .todo "Range object を作る API が無い（range は scenario が与える。`Dom/Range/Api.lean` の注）" },
  { target := "dom-document-createnodeiterator", reason := .todo "NodeIterator を作る API が無い（iterator は scenario が与える）" },
  { target := "dom-document-createtreewalker", reason := .todo "TreeWalker を作る API が無い（walker は scenario が与える）" },
  /- §4.5.1 -/
  { target := "interface-domimplementation",
    reason := .todo "DOMImplementation（createDocumentType・createDocument・createHTMLDocument）が無い。document を作る関数も、DocumentType の name・public ID・system ID も model に無い" },
  { target := "dom-domimplementation-hasfeature", reason := .legacy },
  /- §4.6 -/
  { target := "interface-documenttype",
    reason := .todo "DocumentType の name・public ID・system ID を持たない（create a doctype と三つの getter）" },
  /- §4.7 -/
  { target := "exclusive-documentfragment-node",
    reason := .shadow },
  { target := "dom-documentfragment-documentfragment", reason := .host },
  /- §4.8 -/
  { target := "interface-shadowroot", reason := .shadow }
]

end Trace.Dom.Document
