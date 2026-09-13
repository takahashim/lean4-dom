import Lean.Data.Json
import Dom.Exec.Types

/-!
# scenario の入出力

PLAN §7.1 と §7.2 の JSON 形式を読み書きする。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
外部 library ではなく Lean の配布物なので、PLAN §2.1 の依存方針の範囲に収まる。
`Lean` への依存はこの file に閉じている。操作列の型は `Dom/Exec/Types.lean`、
評価は `Dom/Exec/Eval.lean` にあり、どちらも `Lean.Data.Json` を import しない。

## 入力形式

```json
{
  "nodes": [
    {"id": 0, "kind": "document"},
    {"id": 1, "kind": "element", "parent": 0},
    {"id": 2, "kind": "text", "parent": 1, "data": "abc"},
    {"id": 3, "kind": "element"}
  ],
  "ranges": [],
  "iterators": [],
  "walkers": [],
  "operations": [
    {"op": "insertBefore", "parent": 1, "node": 3, "child": null},
    {"op": "removeChild", "parent": 1, "node": 2}
  ]
}
```

* `nodes` の並び順が children の順序を決める。同じ `parent` を持つ node は、
  配列に現れた順に children へ並ぶ。
* `ownerDocument` は省略できる。省略した場合、kind が `document` の node は自分自身、
  それ以外は配列中の最初の `document` node を node document とする。
* `data` は CharacterData 以外では無視する。
* `ranges` は `{"start": {"node": 1, "offset": 0}, "end": {"node": 1, "offset": 2}}` の形。
* `iterators` は `{"root": 1, "reference": 2, "pointerBeforeReference": true}` の形。
* `walkers` は `{"root": 1, "current": 2, "whatToShow": 128}` の形。
  `current` を省略すると `root` になる（`createTreeWalker` の初期値）。

## 出力形式

```json
{
  "initial": {"nodes": [...], "ranges": [], "iterators": [], "walkers": []},
  "steps": [
    {"ok": true, "nodes": [...], "ranges": [], "iterators": [], "walkers": []},
    {"ok": false, "exception": "NotFoundError"}
  ]
}
```

例外が起きた step で評価を打ち切る（PLAN §7.2）。
-/


namespace Dom.Exec

open Lean (Json)

/-! ## kind の名前 -/

/-- JSON での kind の名前。 -/
def kindName : NodeKind → String
  | .document => "document"
  | .documentType => "documentType"
  | .documentFragment => "documentFragment"
  | .element => "element"
  | .text => "text"
  | .cdataSection => "cdataSection"
  | .processingInstruction => "processingInstruction"
  | .comment => "comment"

def kindOfName? (s : String) : Option NodeKind :=
  [NodeKind.document, .documentType, .documentFragment, .element,
    .text, .cdataSection, .processingInstruction, .comment].find? (kindName · == s)

/-! ## JSON からの復号 -/

private def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

private def natField (j : Json) (k : String) : Except String Nat :=
  match field? j k with
  | none => .error s!"必須の field `{k}` がない"
  | some v => v.getNat?

private def natField? (j : Json) (k : String) : Except String (Option Nat) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getNat?).map some

private def strField (j : Json) (k : String) (dflt : String) : Except String String :=
  match field? j k with
  | none => .ok dflt
  | some v => v.getStr?

private def strField? (j : Json) (k : String) : Except String (Option String) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getStr?).map some

private def boolField? (j : Json) (k : String) : Except String (Option Bool) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getBool?).map some

private def strListField? (j : Json) (k : String) : Except String (Option (List String)) :=
  match field? j k with
  | none => .ok none
  | some v => do
    let arr ← v.getArr?
    return some (← arr.toList.mapM (·.getStr?))

def attrOfJson (j : Json) : Except String Attr := do
  return { «namespace» := ← strField? j "namespace"
           «prefix» := ← strField? j "prefix"
           localName := ← strField j "localName" ""
           value := ← strField j "value" "" }

/-- `MutationObserverInit` の読み取り。省略と `false` は区別する（`observe` step 1-2）。 -/
def observerInitOfJson (j : Json) : Except String MutationObserverInit := do
  let flag (name : String) : Except String Bool :=
    match field? j name with
    | none => pure false
    | some v => v.getBool?
  return { childList := ← flag "childList"
           subtree := ← flag "subtree"
           attributes := ← boolField? j "attributes"
           attributeOldValue := ← flag "attributeOldValue"
           attributeFilter := ← strListField? j "attributeFilter"
           characterData := ← boolField? j "characterData"
           characterDataOldValue := ← flag "characterDataOldValue" }

def nodeSpecOfJson (j : Json) : Except String NodeSpec := do
  let id ← natField j "id"
  let kindStr ← strField j "kind" ""
  let some kind := kindOfName? kindStr
    | .error s!"未知の kind `{kindStr}`（node {id}）"
  let parent ← natField? j "parent"
  let ownerDocument ← natField? j "ownerDocument"
  let data ← strField j "data" ""
  let attributes ← match field? j "attributes" with
    | none => pure ([] : List Attr)
    | some v => do (← v.getArr?).toList.mapM attrOfJson
  let «namespace» ← strField? j "namespace"
  let «prefix» ← strField? j "prefix"
  let localName ← strField? j "localName"
  let isHTMLDocument ← boolField? j "isHTMLDocument"
  return { id, kind, parent, ownerDocument, data, attributes,
           «namespace», «prefix», localName, isHTMLDocument }

def operationOfJson (j : Json) : Except String Operation := do
  let op ← strField j "op" ""
  match op with
  | "appendChild" => return .appendChild (← natField j "parent") (← natField j "node")
  | "insertBefore" =>
    return .insertBefore (← natField j "parent") (← natField j "node") (← natField? j "child")
  | "replaceChild" =>
    return .replaceChild (← natField j "parent") (← natField j "node") (← natField j "child")
  | "removeChild" => return .removeChild (← natField j "parent") (← natField j "node")
  | "replaceChildren" => return .replaceChildren (← natField j "parent") (← natField? j "node")
  | "before" => return .before (← natField j "target") (← natField j "node")
  | "after" => return .after (← natField j "target") (← natField j "node")
  | "replaceWith" => return .replaceWith (← natField j "target") (← natField j "node")
  | "remove" => return .remove (← natField j "target")
  | "moveBefore" =>
    return .moveBefore (← natField j "parent") (← natField j "node") (← natField? j "child")
  | "iteratorNext" => return .iteratorNext (← natField j "iterator")
  | "iteratorPrevious" => return .iteratorPrevious (← natField j "iterator")
  | "replaceData" =>
    return .replaceData (← natField j "node") (← natField j "offset") (← natField j "count")
      (← strField j "data" "")
  | "appendData" => return .appendData (← natField j "node") (← strField j "data" "")
  | "insertData" =>
    return .insertData (← natField j "node") (← natField j "offset") (← strField j "data" "")
  | "deleteData" =>
    return .deleteData (← natField j "node") (← natField j "offset") (← natField j "count")
  | "setData" => return .setData (← natField j "node") (← strField j "data" "")
  | "normalize" => return .normalize (← natField j "target")
  | "rangeSetStart" =>
    return .rangeSetStart (← natField j "range") (← natField j "node") (← natField j "offset")
  | "rangeSetEnd" =>
    return .rangeSetEnd (← natField j "range") (← natField j "node") (← natField j "offset")
  | "rangeSetStartBefore" =>
    return .rangeSetStartSibling (← natField j "range") (← natField j "node") false
  | "rangeSetStartAfter" =>
    return .rangeSetStartSibling (← natField j "range") (← natField j "node") true
  | "rangeSetEndBefore" =>
    return .rangeSetEndSibling (← natField j "range") (← natField j "node") false
  | "rangeSetEndAfter" =>
    return .rangeSetEndSibling (← natField j "range") (← natField j "node") true
  | "rangeCollapse" =>
    return .rangeCollapse (← natField j "range") ((← boolField? j "toStart").getD false)
  | "rangeSelectNode" => return .rangeSelectNode (← natField j "range") (← natField j "node")
  | "rangeSelectNodeContents" =>
    return .rangeSelectNodeContents (← natField j "range") (← natField j "node")
  | "rangeIsPointInRange" =>
    return .rangeIsPointInRange (← natField j "range") (← natField j "node")
      (← natField j "offset")
  | "rangeIntersectsNode" =>
    return .rangeIntersectsNode (← natField j "range") (← natField j "node")
  | "rangeCompareBoundaryPoints" =>
    return .rangeCompareBoundaryPoints (← natField j "range") (← natField j "how")
      (← natField j "source")
  | "rangeComparePoint" =>
    return .rangeComparePoint (← natField j "range") (← natField j "node")
      (← natField j "offset")
  | "rangeDeleteContents" => return .rangeDeleteContents (← natField j "range")
  | "rangeInsertNode" => return .rangeInsertNode (← natField j "range") (← natField j "node")
  | "walkerParentNode" => return .walkerMove (← natField j "walker") .parentNode
  | "walkerFirstChild" => return .walkerMove (← natField j "walker") .firstChild
  | "walkerLastChild" => return .walkerMove (← natField j "walker") .lastChild
  | "walkerPreviousSibling" => return .walkerMove (← natField j "walker") .previousSibling
  | "walkerNextSibling" => return .walkerMove (← natField j "walker") .nextSibling
  | "walkerPreviousNode" => return .walkerMove (← natField j "walker") .previousNode
  | "walkerNextNode" => return .walkerMove (← natField j "walker") .nextNode
  | "rangeToString" => return .rangeToString (← natField j "range")
  | "compareDocumentPosition" =>
    return .compareDocumentPosition (← natField j "node") (← natField j "other")
  | "nodeContains" => return .nodeContains (← natField j "node") (← natField j "other")
  | "getRootNode" => return .getRootNode (← natField j "node")
  | "isEqualNode" => return .isEqualNode (← natField j "node") (← natField j "other")
  | "getTextContent" => return .getTextContent (← natField j "node")
  | "getNodeValue" => return .getNodeValue (← natField j "node")
  | "substringData" =>
    return .substringData (← natField j "node") (← natField j "offset") (← natField j "count")
  | "getAttribute" => return .getAttribute (← natField j "element") (← strField j "name" "")
  | "hasAttribute" => return .hasAttribute (← natField j "element") (← strField j "name" "")
  | "getAttributeNames" => return .getAttributeNames (← natField j "element")
  | "lookupNamespaceURI" =>
    return .lookupNamespaceURI (← natField j "node") (← strField? j "prefix")
  | "lookupPrefix" => return .lookupPrefix (← natField j "node") (← strField? j "namespace")
  | "isDefaultNamespace" =>
    return .isDefaultNamespace (← natField j "node") (← strField? j "namespace")
  | "addEventListener" =>
    return .addEventListener (← natField j "target") (← strField j "type" "")
      (← natField j "source") ((← boolField? j "capture").getD false)
      ((← boolField? j "once").getD false)
  | "removeEventListener" =>
    return .removeEventListener (← natField j "target") (← strField j "type" "")
      (← natField j "callback") ((← boolField? j "capture").getD false)
  | "dispatchEvent" =>
    return .dispatchEvent (← natField j "target") (← strField j "type" "")
      ((← boolField? j "bubbles").getD false) ((← boolField? j "cancelable").getD false)
  | "setAttribute" =>
    return .setAttribute (← natField j "element") (← strField j "name" "")
      (← strField j "value" "")
  | "setAttributeNS" =>
    return .setAttributeNS (← natField j "element") (← strField? j "namespace")
      (← strField j "name" "") (← strField j "value" "")
  | "removeAttribute" =>
    return .removeAttribute (← natField j "element") (← strField j "name" "")
  | "removeAttributeNS" =>
    return .removeAttributeNS (← natField j "element") (← strField? j "namespace")
      (← strField j "name" "")
  | "toggleAttribute" =>
    return .toggleAttribute (← natField j "element") (← strField j "name" "")
      (← boolField? j "force")
  | "observe" =>
    return .observe (← natField j "observer") (← natField j "target") (← observerInitOfJson j)
  | "disconnect" => return .disconnect (← natField j "observer")
  | "takeRecords" => return .takeRecords (← natField j "observer")
  | "notify" => return .notify
  | _ => .error s!"未知の op `{op}`"

def boundaryPointOfJson (j : Json) : Except String BoundaryPoint := do
  return { node := ⟨← natField j "node"⟩, offset := ← natField j "offset" }

def iteratorOfJson (j : Json) : Except String IteratorState := do
  let pb ← match field? j "pointerBeforeReference" with
    | none => pure false
    | some (Json.bool b) => pure b
    | some _ => .error "pointerBeforeReference は boolean でなければならない"
  let whatToShow ← match field? j "whatToShow" with
    | none => pure 0xFFFFFFFF
    | some v => v.getNat?
  return { root := ⟨← natField j "root"⟩, reference := ⟨← natField j "reference"⟩,
           pointerBeforeReference := pb, whatToShow }

/--
`TreeWalker` の読み取り。

`current` を省略すると `root` になる（`createTreeWalker` が置く初期値）。
-/
def walkerOfJson (j : Json) : Except String WalkerState := do
  let root ← natField j "root"
  let current ← match field? j "current" with
    | none => pure root
    | some v => v.getNat?
  let whatToShow ← match field? j "whatToShow" with
    | none => pure 0xFFFFFFFF
    | some v => v.getNat?
  return { root := ⟨root⟩, current := ⟨current⟩, whatToShow }

/--
listener の callback の代わりの副作用。

文字列なら引数の無いもの、object なら `kind` と引数を読む。
-/
def listenerActionOfJson (j : Option Json) : Except String ListenerAction :=
  match j with
  | none => .ok .none
  | some (Json.str "none") => .ok .none
  | some (Json.str "stopPropagation") => .ok .stopPropagation
  | some (Json.str "stopImmediatePropagation") => .ok .stopImmediatePropagation
  | some (Json.str "preventDefault") => .ok .preventDefault
  | some (Json.obj o) => do
    let j := Json.obj o
    let some (Json.str kind) := field? j "kind" | .error "action に `kind` がない"
    match kind with
    | "removeListener" => return .removeListener (← natField j "index")
    | "addListener" =>
      return .addListener (← natField j "target") (← strField j "type" "")
        (← natField j "source") ((← boolField? j "capture").getD false)
    | k => .error s!"知らない listener action: {k}"
  | some _ => .error "action は文字列か object でなければならない"

/-- scenario の listener。`callback` を省略すると宣言順の番号になる。 -/
def listenerOfJson (j : Json) (index : Nat) : Except String EventListener := do
  let action ← listenerActionOfJson (field? j "action")
  return { target := ⟨← natField j "target"⟩
           «type» := ← strField j "type" ""
           callback := (← natField? j "callback").getD index
           capture := (← boolField? j "capture").getD false
           once := (← boolField? j "once").getD false
           action := action }

def rangeOfJson (j : Json) : Except String RangeState := do
  let some st := field? j "start" | .error "range に `start` がない"
  let some en := field? j "end" | .error "range に `end` がない"
  return { start := ← boundaryPointOfJson st, «end» := ← boundaryPointOfJson en }

def observerOfJson (j : Json) : Except String ObserverSpec := do
  let target ← natField? j "target"
  let flag (name : String) : Except String Bool :=
    match field? j name with
    | none => pure false
    | some v => v.getBool?
  return { target
           subtree := ← flag "subtree"
           childList := ← flag "childList"
           attributes := ← flag "attributes"
           attributeOldValue := ← flag "attributeOldValue"
           attributeFilter := ← strListField? j "attributeFilter"
           characterData := ← flag "characterData"
           characterDataOldValue := ← flag "characterDataOldValue" }

def scenarioOfJson (j : Json) : Except String Scenario := do
  let nodesJson ← match field? j "nodes" with
    | none => .error "`nodes` がない"
    | some v => v.getArr?
  let opsJson ← match field? j "operations" with
    | none => pure #[]
    | some v => v.getArr?
  let rangesJson ← match field? j "ranges" with
    | none => pure #[]
    | some v => v.getArr?
  let itersJson ← match field? j "iterators" with
    | none => pure #[]
    | some v => v.getArr?
  let walkersJson ← match field? j "walkers" with
    | none => pure #[]
    | some v => v.getArr?
  let listenersJson ← match field? j "listeners" with
    | none => pure #[]
    | some v => v.getArr?
  let obsJson ← match field? j "observers" with
    | none => pure #[]
    | some v => v.getArr?
  let nodes ← nodesJson.toList.mapM nodeSpecOfJson
  let ranges ← rangesJson.toList.mapM rangeOfJson
  let iterators ← itersJson.toList.mapM iteratorOfJson
  let walkers ← walkersJson.toList.mapM walkerOfJson
  let listeners ← listenersJson.toList.zipIdx.mapM fun (l, i) => listenerOfJson l i
  let observers ← obsJson.toList.mapM observerOfJson
  let operations ← opsJson.toList.mapM operationOfJson
  return { nodes, ranges, iterators, walkers, listeners, observers, operations }

def scenarioOfString (s : String) : Except String Scenario := do
  scenarioOfJson (← Json.parse s)

/-! ## JSON への符号化 -/

private def natJson (n : Nat) : Json := Json.num (Int.ofNat n)

private def optNatJson : Option NodeId → Json
  | none => Json.null
  | some n => natJson n.id

/--
観測できる node の外部表現。

`Dom/Observation.lean` の `ObservedNode` の各 field をそのまま並べる。
-/
def optStrJson : Option String → Json
  | none => Json.null
  | some v => Json.str v

def attrJson (a : Attr) : Json :=
  Json.mkObj
    [ ("namespace", optStrJson a.namespace)
    , ("prefix", optStrJson a.prefix)
    , ("localName", Json.str a.localName)
    , ("value", Json.str a.value) ]

def observedNodeJson (n : ObservedNode) : Json :=
  Json.mkObj
    [ ("id", natJson n.id.id)
    , ("kind", Json.str (kindName n.kind))
    , ("parent", optNatJson n.parent)
    , ("children", Json.arr (n.children.map fun c => natJson c.id).toArray)
    , ("nodeDocument", natJson n.nodeDocument.id)
    , ("data", Json.str n.data)
    , ("attributes", Json.arr (n.attributes.map attrJson).toArray)
    , ("namespace", optStrJson n.namespace)
    , ("prefix", optStrJson n.prefix)
    , ("localName", Json.str n.localName)
    , ("tagName", optStrJson n.tagName) ]

def boundaryPointJson (bp : BoundaryPoint) : Json :=
  Json.mkObj [("node", natJson bp.node.id), ("offset", natJson bp.offset)]

def rangeJson (r : RangeState) : Json :=
  Json.mkObj [("start", boundaryPointJson r.start), ("end", boundaryPointJson r.«end»)]

def iteratorJson (it : IteratorState) : Json :=
  Json.mkObj
    [ ("root", natJson it.root.id)
    , ("reference", natJson it.reference.id)
    , ("pointerBeforeReference", Json.bool it.pointerBeforeReference)
    , ("whatToShow", natJson it.whatToShow) ]

def walkerJson (w : WalkerState) : Json :=
  Json.mkObj
    [ ("root", natJson w.root.id)
    , ("current", natJson w.current.id)
    , ("whatToShow", natJson w.whatToShow) ]

def invocationJson (v : Invocation) : Json :=
  Json.mkObj
    [ ("callback", natJson v.callback)
    , ("currentTarget", natJson v.currentTarget.id)
    , ("eventPhase", natJson v.eventPhase) ]

def recordTypeName : RecordType → String
  | .attributes => "attributes"
  | .childList => "childList"
  | .characterData => "characterData"

def recordJson (r : MutationRecord) : Json :=
  Json.mkObj
    [ ("type", Json.str (recordTypeName r.type))
    , ("target", natJson r.target.id)
    , ("addedNodes", Json.arr (r.addedNodes.map fun n => natJson n.id).toArray)
    , ("removedNodes", Json.arr (r.removedNodes.map fun n => natJson n.id).toArray)
    , ("previousSibling", optNatJson r.previousSibling)
    , ("nextSibling", optNatJson r.nextSibling)
    , ("attributeName", optStrJson r.attributeName)
    , ("attributeNamespace", optStrJson r.attributeNamespace)
    , ("oldValue", optStrJson r.oldValue) ]

/--
戻り値の外部表現。

`kind` を添えるのは、`undefined` と `null` を返す操作を取り違えないためである
（`removeChild` が null を返したら不一致、`remove()` が undefined を返すのは正しい）。
-/
def returnValueJson : ReturnValue → Json
  | .unit => Json.mkObj [("kind", Json.str "undefined")]
  | .node n => Json.mkObj [("kind", Json.str "node"), ("node", optNatJson n)]
  | .bool b => Json.mkObj [("kind", Json.str "boolean"), ("value", Json.bool b)]
  | .records rs =>
    Json.mkObj [("kind", Json.str "records"),
                ("records", Json.arr (rs.map recordJson).toArray)]
  | .int i => Json.mkObj [("kind", Json.str "number"), ("value", Json.num (.fromInt i))]
  | .str s =>
    Json.mkObj [("kind", Json.str "string"),
                ("value", match s with | none => Json.null | some x => Json.str x)]
  | .strs l =>
    Json.mkObj [("kind", Json.str "strings"),
                ("value", Json.arr (l.map Json.str).toArray)]

/--
`Observation` の外部表現。

`result` は `ok` / `exception` として並べる。
JSON は `Observation` の serialize であり、
比較の意味は「同じ `Observation` に落ちること」である（roadmap §9）。
-/
def observationFields (o : Observation) : List (String × Json) :=
  let resultFields : List (String × Json) :=
    match o.result with
    | .ok => [("ok", Json.bool true)]
    | .failed e => [("ok", Json.bool false), ("exception", Json.str e.name)]
  -- 失敗した操作に戻り値は無いので、その step では field ごと出さない。
  let returnedFields : List (String × Json) :=
    match o.result with
    | .ok => [("returned", returnValueJson o.returned)]
    | .failed _ => []
  resultFields ++ returnedFields ++
    [ ("nodes", Json.arr (o.nodes.map observedNodeJson).toArray)
    , ("ranges", Json.arr (o.ranges.map rangeJson).toArray)
    , ("iterators", Json.arr (o.iterators.map iteratorJson).toArray)
    , ("walkers", Json.arr (o.walkers.map walkerJson).toArray)
    , ("observers", Json.arr
        (o.records.map fun rs => Json.arr (rs.map recordJson).toArray).toArray)
    , ("invocations", Json.arr (o.invocations.map invocationJson).toArray)
    , ("delivered", Json.arr (o.delivered.map fun p =>
        Json.mkObj [("observer", natJson p.1),
                    ("records", Json.arr (p.2.map recordJson).toArray)]).toArray) ]

def observationJson (o : Observation) : Json :=
  Json.mkObj (observationFields o)

/-- 初期状態の観測。まだ操作していないので `ok` / `exception` は出さない。 -/
def stateJson (s : DOMState) : Json :=
  Json.mkObj ((observationFields (observe s .ok)).filter fun p =>
    p.1 ≠ "ok" && p.1 ≠ "returned")

def stepJson : StepResult → Json
  | .ok s delivered returned invoked =>
    observationJson (observe s .ok delivered returned invoked)
  | .failed before e => observationJson (observe before (.failed e))

end Dom.Exec
