import Dom.Exec.Eval
import Dom.Exec.Json

/-!
# scenario 一つを走らせる入口

`Dom/Exec/Eval.lean` の評価と `Dom/Exec/Json.lean` の入出力をつなぐ。
ここだけが両方を知っている。
-/

namespace Dom.Exec

open Lean (Json)

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

def checkScenarioString (s : String) : Except String (Option (Nat × String)) := do
  checkScenario (← scenarioOfString s)

end Dom.Exec
