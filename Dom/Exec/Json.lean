import Lean.Data.Json
import Dom.Mutation.Api
import Dom.Range.Adjust
import Dom.Traversal.NodeIterator
import Dom.CharacterData.ReplaceData
import Dom.Observation
import Dom.Observer.Deliver

/-!
# scenario の入出力

PLAN §7.1 と §7.2 の JSON 形式を読み書きする。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
外部 library ではなく Lean の配布物なので、PLAN §2.1 の依存方針の範囲に収まる。
`Lean` への依存はこの `Dom/Exec/` に閉じており、`Dom/Properties/` からは import しない。

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

## 出力形式

```json
{
  "initial": {"nodes": [...], "ranges": [], "iterators": []},
  "steps": [
    {"ok": true, "nodes": [...], "ranges": [], "iterators": []},
    {"ok": false, "exception": "NotFoundError"}
  ]
}
```

例外が起きた step で評価を打ち切る（PLAN §7.2）。
-/

namespace Dom.Exec

open Lean (Json)

/-! ## scenario の表現 -/

/-- 初期状態の node 一つぶんの記述。 -/
structure NodeSpec where
  id : Nat
  kind : NodeKind
  parent : Option Nat := none
  ownerDocument : Option Nat := none
  data : String := ""
deriving Repr

/-- scenario が並べる操作。Phase 3 までの public API に対応する。 -/
inductive Operation where
  | appendChild (parent node : Nat)
  | insertBefore (parent node : Nat) (child : Option Nat)
  | replaceChild (parent node child : Nat)
  | removeChild (parent node : Nat)
  | replaceChildren (parent : Nat) (node : Option Nat)
  | before (target node : Nat)
  | after (target node : Nat)
  | replaceWith (target node : Nat)
  | remove (target : Nat)
  | moveBefore (parent node : Nat) (child : Option Nat)
  | iteratorNext (index : Nat)
  | iteratorPrevious (index : Nat)
  | replaceData (node : Nat) (offset count : Nat) (data : String)
  | appendData (node : Nat) (data : String)
  | insertData (node : Nat) (offset : Nat) (data : String)
  | deleteData (node : Nat) (offset count : Nat)
  | setData (node : Nat) (data : String)
  /-- `MutationObserver.observe(target, options)`。 -/
  | observe (observer : Nat) (target : Nat) (opts : MutationObserverInit)
  /-- `MutationObserver.disconnect()`。 -/
  | disconnect (observer : Nat)
  /-- `MutationObserver.takeRecords()`。 -/
  | takeRecords (observer : Nat)
  /-- microtask checkpoint。"notify mutation observers" を走らせる。 -/
  | notify
deriving Repr

/--
scenario での MutationObserver。

一つの observer が一つの node を観測する形だけを扱う。
仕様の `observe(target, options)` を一度だけ呼んだ状態にあたる。
-/
structure ObserverSpec where
  /--
  `observe(target, options)` を一度呼んだ状態にする。

  `none` なら registration を持たない observer を作るだけである。
  scenario 側で `observe` 操作を使う場合はこちらを指定する。
  -/
  target : Option Nat := none
  subtree : Bool := false
  childList : Bool := false
  characterData : Bool := false
  characterDataOldValue : Bool := false
deriving Repr

/-- 一つの scenario。 -/
structure Scenario where
  nodes : List NodeSpec
  ranges : List RangeState := []
  iterators : List IteratorState := []
  observers : List ObserverSpec := []
  operations : List Operation
deriving Repr

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

def nodeSpecOfJson (j : Json) : Except String NodeSpec := do
  let id ← natField j "id"
  let kindStr ← strField j "kind" ""
  let some kind := kindOfName? kindStr
    | .error s!"未知の kind `{kindStr}`（node {id}）"
  let parent ← natField? j "parent"
  let ownerDocument ← natField? j "ownerDocument"
  let data ← strField j "data" ""
  return { id, kind, parent, ownerDocument, data }

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
  | "observe" =>
    let flag (name : String) : Except String Bool :=
      match field? j name with
      | none => pure false
      | some v => v.getBool?
    return .observe (← natField j "observer") (← natField j "target")
      { childList := ← flag "childList"
        subtree := ← flag "subtree"
        characterData := ← flag "characterData"
        characterDataOldValue := ← flag "characterDataOldValue" }
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
  return { root := ⟨← natField j "root"⟩, reference := ⟨← natField j "reference"⟩,
           pointerBeforeReference := pb }

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
  let obsJson ← match field? j "observers" with
    | none => pure #[]
    | some v => v.getArr?
  let nodes ← nodesJson.toList.mapM nodeSpecOfJson
  let ranges ← rangesJson.toList.mapM rangeOfJson
  let iterators ← itersJson.toList.mapM iteratorOfJson
  let observers ← obsJson.toList.mapM observerOfJson
  let operations ← opsJson.toList.mapM operationOfJson
  return { nodes, ranges, iterators, observers, operations }

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
def observedNodeJson (n : ObservedNode) : Json :=
  Json.mkObj
    [ ("id", natJson n.id.id)
    , ("kind", Json.str (kindName n.kind))
    , ("parent", optNatJson n.parent)
    , ("children", Json.arr (n.children.map fun c => natJson c.id).toArray)
    , ("nodeDocument", natJson n.nodeDocument.id)
    , ("data", Json.str n.data) ]

def boundaryPointJson (bp : BoundaryPoint) : Json :=
  Json.mkObj [("node", natJson bp.node.id), ("offset", natJson bp.offset)]

def rangeJson (r : RangeState) : Json :=
  Json.mkObj [("start", boundaryPointJson r.start), ("end", boundaryPointJson r.«end»)]

def iteratorJson (it : IteratorState) : Json :=
  Json.mkObj
    [ ("root", natJson it.root.id)
    , ("reference", natJson it.reference.id)
    , ("pointerBeforeReference", Json.bool it.pointerBeforeReference) ]

def recordTypeName : RecordType → String
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
    , ("oldValue", match r.oldValue with | none => Json.null | some v => Json.str v) ]

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
  resultFields ++
    [ ("nodes", Json.arr (o.nodes.map observedNodeJson).toArray)
    , ("ranges", Json.arr (o.ranges.map rangeJson).toArray)
    , ("iterators", Json.arr (o.iterators.map iteratorJson).toArray)
    , ("observers", Json.arr
        (o.records.map fun rs => Json.arr (rs.map recordJson).toArray).toArray)
    , ("delivered", Json.arr (o.delivered.map fun p =>
        Json.mkObj [("observer", natJson p.1),
                    ("records", Json.arr (p.2.map recordJson).toArray)]).toArray) ]

def observationJson (o : Observation) : Json :=
  Json.mkObj (observationFields o)

/-- 初期状態の観測。まだ操作していないので `ok` / `exception` は出さない。 -/
def stateJson (s : DOMState) : Json :=
  Json.mkObj ((observationFields (observe s .ok)).filter fun p => p.1 ≠ "ok")

/--
一 step の結果。

例外で失敗した step でも、**変わっていない状態**を観測として出す。
Dommy は木をその場で書き換えるので、失敗した操作が状態を変えていないことも比較対象になる。
-/
inductive StepResult where
  | ok (s : DOMState) (delivered : List (Nat × List MutationRecord))
  | failed (before : DOMState) (e : DOMException)

def stepJson : StepResult → Json
  | .ok s delivered => observationJson (observe s .ok delivered)
  | .failed before e => observationJson (observe before (.failed e))

end Dom.Exec
