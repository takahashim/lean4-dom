import Dom.Exec.Json

/-!
# 操作列の評価

PLAN §7。scenario を読み込んで初期状態を組み立て、操作を順に適用して各 step の状態を出力する。

各 step の後で `checkWellFormed` を実行し、invariant が破れていないか実行時にも確認する
（PLAN §3.5）。破れていればその step 番号を出力に含める。
証明済みの preservation 定理があるので本来は起こらないが、
oracle の組み立て（初期状態の構築や操作の割り当て）の誤りはこれで検出できる。
-/

namespace Dom.Exec

open Lean (Json)

/-! ## 初期状態の構築 -/

/--
scenario の `nodes` から木を組み立てる。

children の順序は配列の並び順で決まる。
組み立てた木が `WellFormed` でなければ拒否する（PLAN §7.1）。
-/
def buildTree (specs : List NodeSpec) : Except String Tree := do
  let ids := specs.map (·.id)
  unless Dom.ListUtil.nodupB ids do
    throw "node の id が重複している"
  let defaultDoc? := (specs.find? (·.kind == .document)).map (·.id)
  let entry (s : NodeSpec) : Except String (NodeId × NodeData) := do
    let owner ←
      match s.ownerDocument with
      | some o => pure o
      | none =>
        if s.kind == .document then pure s.id
        else
          match defaultDoc? with
          | some d => pure d
          | none => throw s!"document node が無いので node {s.id} の ownerDocument を決められない"
    let children := (specs.filter (fun c => c.parent == some s.id)).map fun c => NodeId.mk c.id
    -- `data` は CharacterData 以外では空とする（`NodeData` の doc comment のとおり）。
    return (⟨s.id⟩,
      { kind := s.kind
        parent := s.parent.map NodeId.mk
        children
        ownerDocument := ⟨owner⟩
        data := if s.kind.isCharacterData then s.data else "" })
  let entries ← specs.mapM entry
  let t : Tree := { nodes := entries.foldl (fun st p => st.insert p.1 p.2) NodeStore.empty }
  unless t.checkWellFormed do
    throw "初期状態が WellFormed を満たしていない"
  return t

/-! ## 操作の適用 -/

/-- 一つの操作を public API に割り当てる。 -/
def applyOperation (t : Tree) : Operation → Except DOMException Tree
  | .appendChild p n => appendChild t ⟨p⟩ ⟨n⟩
  | .insertBefore p n c => insertBefore t ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)
  | .replaceChild p n c => replaceChild t ⟨p⟩ ⟨n⟩ ⟨c⟩
  | .removeChild p n => removeChild t ⟨p⟩ ⟨n⟩
  | .replaceChildren p n => replaceChildren t ⟨p⟩ (n.map NodeId.mk)
  | .before tgt n => before t ⟨tgt⟩ ⟨n⟩
  | .after tgt n => after t ⟨tgt⟩ ⟨n⟩
  | .replaceWith tgt n => replaceWith t ⟨tgt⟩ ⟨n⟩
  | .remove tgt => nodeRemove t ⟨tgt⟩
  | .moveBefore p n c => moveBefore t ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)

/--
操作列を順に適用する。例外が起きた step で打ち切る（PLAN §7.2）。

返り値の第二成分は、invariant が破れた step の番号（0 始まり）。
-/
def runOperations : Tree → List Operation → Nat → List StepResult × Option Nat
  | _, [], _ => ([], none)
  | t, op :: ops, i =>
    match applyOperation t op with
    | .error e => ([.failed e], none)
    | .ok t' =>
      if !t'.checkWellFormed then ([.ok t'], some i)
      else
        let (rest, viol) := runOperations t' ops (i + 1)
        (.ok t' :: rest, viol)

/-! ## scenario 全体の評価 -/

/-- scenario を評価して出力 JSON を作る。 -/
def runScenario (sc : Scenario) : Except String Json := do
  let t ← buildTree sc.nodes
  let (steps, viol) := runOperations t sc.operations 0
  let base : List (String × Json) :=
    [("initial", treeJson t), ("steps", Json.arr (steps.map stepJson).toArray)]
  return Json.mkObj <|
    match viol with
    | none => base
    | some i => base ++ [("invariantViolation", Json.num (Int.ofNat i))]

/-- 文字列で与えられた scenario を評価する。 -/
def runScenarioString (s : String) : Except String String := do
  let sc ← scenarioOfString s
  return (← runScenario sc).compress

end Dom.Exec
