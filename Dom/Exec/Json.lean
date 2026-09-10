import Lean.Data.Json
import Dom.Mutation.Api
import Dom.Range.Adjust

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
* `iterators` は Phase 6 で使う。形式だけ予約する。

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
deriving Repr

/-- 一つの scenario。 -/
structure Scenario where
  nodes : List NodeSpec
  ranges : List RangeState := []
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
  | _ => .error s!"未知の op `{op}`"

def boundaryPointOfJson (j : Json) : Except String BoundaryPoint := do
  return { node := ⟨← natField j "node"⟩, offset := ← natField j "offset" }

def rangeOfJson (j : Json) : Except String RangeState := do
  let some st := field? j "start" | .error "range に `start` がない"
  let some en := field? j "end" | .error "range に `end` がない"
  return { start := ← boundaryPointOfJson st, «end» := ← boundaryPointOfJson en }

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
  let nodes ← nodesJson.toList.mapM nodeSpecOfJson
  let ranges ← rangesJson.toList.mapM rangeOfJson
  let operations ← opsJson.toList.mapM operationOfJson
  return { nodes, ranges, operations }

def scenarioOfString (s : String) : Except String Scenario := do
  scenarioOfJson (← Json.parse s)

/-! ## JSON への符号化 -/

private def natJson (n : Nat) : Json := Json.num (Int.ofNat n)

private def optNatJson : Option NodeId → Json
  | none => Json.null
  | some n => natJson n.id

/--
一つの node の観測可能な状態。

PLAN §7.2 の比較対象のうち、parent と children をここに出す。
tree order は children から導けるので出力には含めず、比較 script 側で導出する。
-/
def nodeJson (t : Tree) (n : NodeId) (d : NodeData) : Json :=
  Json.mkObj
    [ ("id", natJson n.id)
    , ("kind", Json.str (kindName d.kind))
    , ("parent", optNatJson d.parent)
    , ("children", Json.arr ((childrenOf t n).map fun c => natJson c.id).toArray)
    , ("data", Json.str d.data) ]

def boundaryPointJson (bp : BoundaryPoint) : Json :=
  Json.mkObj [("node", natJson bp.node.id), ("offset", natJson bp.offset)]

def rangeJson (r : RangeState) : Json :=
  Json.mkObj [("start", boundaryPointJson r.start), ("end", boundaryPointJson r.«end»)]

/-- 状態全体の観測可能な部分。node は id の昇順に並べる。 -/
def stateJson (s : DOMState) : Json :=
  let ids := (s.tree.nodes.keys.map (·.id)).mergeSort (· ≤ ·)
  Json.mkObj
    [ ("nodes", Json.arr (ids.filterMap fun i =>
        (s.tree.get? ⟨i⟩).map fun d => nodeJson s.tree ⟨i⟩ d).toArray)
    , ("ranges", Json.arr (s.ranges.map rangeJson).toArray)
    , ("iterators", Json.arr #[]) ]

/-- 一 step の結果。 -/
inductive StepResult where
  | ok (s : DOMState)
  | failed (e : DOMException)

def stepJson : StepResult → Json
  | .ok s =>
    match stateJson s with
    | Json.obj fields => Json.obj (fields.insert "ok" (Json.bool true))
    | other => other
  | .failed e =>
    Json.mkObj [("ok", Json.bool false), ("exception", Json.str e.name)]

end Dom.Exec
