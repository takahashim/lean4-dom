import Dom.Exec.Json
import Dom.Validity.State

/-!
# 操作列の評価

PLAN §7。scenario を読み込んで初期状態を組み立て、操作を順に適用して各 step の状態を出力する。

各 step の後で `checkAdmissibleDOMState` を実行し、
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

/--
初期状態を組み立てる。range と iterator が valid であることも検査する。

要求するのは **admissible な状態**（`AdmissibleDOMState`）であることである。
range については両端が木の中にあることだけを見る。
順序（`BoundaryLE`）は仕様の invariant ではないので要求しない
（`notes/research-foundation-roadmap.md` §4。反例探索のために loader は
admissible な状態を広く受理してよい）。

ただし differential testing に使う scenario は、Dommy 側が
`setStart` / `setEnd` で range を組み立てる以上、順序の付いたものに限る必要がある。
それは loader の制約ではなく harness の制約なので、生成器の側で守る。
-/
def buildState (sc : Scenario) : Except String DOMState := do
  let t ← buildTree sc.nodes
  let observers : List ObserverState := sc.observers.map fun _ => {}
  let registrations : List Registration := sc.observers.zipIdx.map fun (o, i) =>
    { node := ⟨o.target⟩, observer := i, subtree := o.subtree, childList := o.childList,
      characterData := o.characterData, characterDataOldValue := o.characterDataOldValue }
  let s : DOMState := { tree := t, ranges := sc.ranges, iterators := sc.iterators,
                        observers, registrations }
  unless checkStructurallyValid t do
    throw "初期状態が構造上の制約（leaf に children、Document に parent など）を満たしていない"
  unless checkNodeDocumentsValid t do
    throw "初期状態の node document が整合していない"
  unless checkDocumentTreesValid t do
    throw "初期状態の Document の children が仕様の制約を満たしていない"
  unless checkRangeEndpointsValid s do
    throw "初期状態の range の端点が木の中にない"
  unless checkIteratorsValid s do
    throw "初期状態の iterator が valid でない"
  return s

/--
`nextNode()` / `previousNode()` を i 番目の iterator に適用する。

collection の端で `null` が返る場合、仕様では iterator は変わらない。
index が範囲外の場合も何もしない。
-/
def stepIterator (s : DOMState) (i : Nat)
    (f : Tree → IteratorState → Option (NodeId × IteratorState)) : DOMState :=
  match s.iterators[i]? with
  | none => s
  | some it =>
    match f s.tree it with
    | none => s
    | some (_, it') => { s with iterators := s.iterators.set i it' }

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
  | .iteratorNext i => .ok (stepIterator s i nextNode)
  | .iteratorPrevious i => .ok (stepIterator s i previousNode)
  | .replaceData n o c d => replaceData s ⟨n⟩ o c d
  | .appendData n d => appendData s ⟨n⟩ d
  | .insertData n o d => insertData s ⟨n⟩ o d
  | .deleteData n o c => deleteData s ⟨n⟩ o c
  | .setData n d => setData s ⟨n⟩ d

/--
操作列を順に適用する。例外が起きた step で打ち切る（PLAN §7.2）。

返り値の第二成分は、invariant が破れた step の番号（0 始まり）。

range については **両端が木の中にあること** だけを invariant とする。
順序（start ≤ end）は仕様の invariant ではない。木を変える algorithm の側には
`setStart` / `setEnd` のような正規化が無く、insert step 5（offset の調整）が
step 7 の adopt→remove より前に走るせいで、順序は実際に逆転しうる。
`test/scenarios/range-order-broken-by-insert.json` がその最小例である。
-/
def runOperations : DOMState → List Operation → Nat → List StepResult × Option (Nat × String)
  | _, [], _ => ([], none)
  | s, op :: ops, i =>
    match applyOperation s op with
    | .error e => ([.failed s e], none)
    | .ok s' =>
      if !s'.tree.checkWellFormed then ([.ok s'], some (i, "wellFormed"))
      else if !checkStructurallyValid s'.tree then ([.ok s'], some (i, "structurallyValid"))
      else if !checkNodeDocumentsValid s'.tree then ([.ok s'], some (i, "nodeDocumentsValid"))
      else if !checkDocumentTreesValid s'.tree then ([.ok s'], some (i, "documentTreesValid"))
      else if !checkRangeEndpointsValid s' then ([.ok s'], some (i, "rangeEndpointsValid"))
      else if !checkIteratorsValid s' then ([.ok s'], some (i, "iteratorsValid"))
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

/--
scenario を評価して、invariant 違反があればその step 番号と名前を返す。

`Dom/Exec/Invariant.lean` の `runOperations_no_violation` により、
初期状態が admissible ならこれは必ず `none` である。
`some` が返るのは harness 側（初期状態の構築や操作の割り当て）の誤りを意味する。
-/
def checkScenario (sc : Scenario) : Except String (Option (Nat × String)) := do
  let s ← buildState sc
  return (runOperations s sc.operations 0).2

def checkScenarioString (s : String) : Except String (Option (Nat × String)) := do
  checkScenario (← scenarioOfString s)

end Dom.Exec
