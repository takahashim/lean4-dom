import Dom.Exec.Json

/-!
# 操作列の評価

PLAN §7。scenario を読み込んで初期状態を組み立て、操作を順に適用して各 step の状態を出力する。

各 step の後で `checkWellFormed` と `checkRangesValid` を実行し、
invariant が破れていないか実行時にも確認する（PLAN §3.5, §8）。
破れていればその step 番号を出力に含める。
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

/-- 初期状態を組み立てる。range の両端が木の中にあることも検査する。 -/
def buildState (sc : Scenario) : Except String DOMState := do
  let t ← buildTree sc.nodes
  let s : DOMState := { tree := t, ranges := sc.ranges }
  unless checkRangesValid s do
    throw "初期状態の range が valid でない"
  return s

/-- 一つの操作を public API に割り当てる。 -/
def applyOperation (s : DOMState) : Operation → Except DOMException DOMState
  | .appendChild p n => appendChild s ⟨p⟩ ⟨n⟩
  | .insertBefore p n c => insertBefore s ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)
  | .replaceChild p n c => replaceChild s ⟨p⟩ ⟨n⟩ ⟨c⟩
  | .removeChild p n => removeChild s ⟨p⟩ ⟨n⟩
  | .replaceChildren p n => replaceChildren s ⟨p⟩ (n.map NodeId.mk)
  | .before tgt n => before s ⟨tgt⟩ ⟨n⟩
  | .after tgt n => after s ⟨tgt⟩ ⟨n⟩
  | .replaceWith tgt n => replaceWith s ⟨tgt⟩ ⟨n⟩
  | .remove tgt => nodeRemove s ⟨tgt⟩
  | .moveBefore p n c => moveBefore s ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)

/--
操作列を順に適用する。例外が起きた step で打ち切る（PLAN §7.2）。

返り値の第二成分は、invariant が破れた step の番号（0 始まり）。
-/
def runOperations : DOMState → List Operation → Nat → List StepResult × Option (Nat × String)
  | _, [], _ => ([], none)
  | s, op :: ops, i =>
    match applyOperation s op with
    | .error e => ([.failed e], none)
    | .ok s' =>
      if !s'.tree.checkWellFormed then ([.ok s'], some (i, "wellFormed"))
      else if !checkRangesValid s' then ([.ok s'], some (i, "rangesValid"))
      else
        let (rest, viol) := runOperations s' ops (i + 1)
        (.ok s' :: rest, viol)

/-! ## scenario 全体の評価 -/

/-- scenario を評価して出力 JSON を作る。 -/
def runScenario (sc : Scenario) : Except String Json := do
  let s ← buildState sc
  let (steps, viol) := runOperations s sc.operations 0
  let base : List (String × Json) :=
    [("initial", stateJson s), ("steps", Json.arr (steps.map stepJson).toArray)]
  return Json.mkObj <|
    match viol with
    | none => base
    | some (i, what) =>
      base ++ [("invariantViolation",
        Json.mkObj [("step", Json.num (Int.ofNat i)), ("invariant", Json.str what)])]

/-- 文字列で与えられた scenario を評価する。 -/
def runScenarioString (s : String) : Except String String := do
  let sc ← scenarioOfString s
  return (← runScenario sc).compress

end Dom.Exec
