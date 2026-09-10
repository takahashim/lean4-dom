import Dom
import Dom.Exec.Scenario

/-!
# `lake exe dom-model`

引数なしで起動すると、Phase 1-3 の定義が小さな木の上で動くことを確認する demo を実行する。
scenario file の path を渡すと、それを評価して結果の JSON を標準出力に書く（PLAN §7）。

```sh
lake exe dom-model                          # demo
lake exe dom-model test/scenarios/x.json    # scenario 一つを評価して標準出力へ
lake exe dom-model --batch DIR              # DIR/*.json をまとめて評価し DIR/*.lean.json へ書く
```
-/

namespace Dom.Demo

def doc : NodeId := ⟨0⟩
def html : NodeId := ⟨1⟩
def head : NodeId := ⟨2⟩
def body : NodeId := ⟨3⟩
def hello : NodeId := ⟨4⟩
def dtype : NodeId := ⟨5⟩
def frag : NodeId := ⟨6⟩
def e1 : NodeId := ⟨7⟩
def e2 : NodeId := ⟨8⟩
def orphan : NodeId := ⟨9⟩
def loose : NodeId := ⟨10⟩
def dtype2 : NodeId := ⟨11⟩
def otherDoc : NodeId := ⟨12⟩

/--
`doc` を root とする木。`frag` は木から切り離された DocumentFragment、
`otherDoc` は別の木の root である。
-/
def sample : Tree :=
  { nodes :=
      NodeStore.empty
        |>.insert doc { kind := .document, children := [dtype, html], ownerDocument := doc }
        |>.insert dtype { kind := .documentType, parent := some doc, ownerDocument := doc }
        |>.insert html
            { kind := .element, parent := some doc, children := [head, body],
              ownerDocument := doc }
        |>.insert head { kind := .element, parent := some html, ownerDocument := doc }
        |>.insert body
            { kind := .element, parent := some html, children := [hello], ownerDocument := doc }
        |>.insert hello
            { kind := .text, parent := some body, ownerDocument := doc, data := "hello" }
        |>.insert frag
            { kind := .documentFragment, children := [e1, e2], ownerDocument := doc }
        |>.insert e1 { kind := .element, parent := some frag, ownerDocument := doc }
        |>.insert e2 { kind := .element, parent := some frag, ownerDocument := doc }
        |>.insert orphan { kind := .element, ownerDocument := doc }
        |>.insert loose { kind := .text, ownerDocument := doc, data := "x" }
        |>.insert dtype2 { kind := .documentType, ownerDocument := doc }
        |>.insert otherDoc { kind := .document, ownerDocument := otherDoc } }

/-- `sample` を初期状態とする `DOMState`。range と iterator を一つずつ持たせてある。 -/
def state : DOMState :=
  { tree := sample
    ranges := [{ start := { node := body, offset := 0 }, «end» := { node := body, offset := 1 } }]
    iterators := [{ root := html, reference := html, pointerBeforeReference := true }] }

/-- children の並びだけを見た木の要約。 -/
def summary (t : Tree) : String :=
  String.intercalate " " <|
    [doc, html, body, frag].map fun n => s!"{n}:{reprStr (childrenOf t n)}"

def rangeSummary (s : DOMState) : String :=
  String.intercalate "," <| s.ranges.map fun r =>
    s!"({r.start.node},{r.start.offset})-({r.end.node},{r.end.offset})"

def describe : Except DOMException DOMState → String
  | .error e => s!"error {e}"
  | .ok s => s!"ok wf={s.tree.checkWellFormed} {summary s.tree}"

def describeRange : Except DOMException DOMState → String
  | .error e => s!"error {e}"
  | .ok s => s!"ok ranges={rangeSummary s} valid={checkRangesValid s}"

def iterSummary (s : DOMState) : String :=
  String.intercalate "," <| s.iterators.map fun it =>
    s!"(root={it.root} ref={it.reference} before={it.pointerBeforeReference})"

def describeIter : Except DOMException DOMState → String
  | .error e => s!"error {e}"
  | .ok s => s!"ok {iterSummary s} valid={checkIteratorsValid s}"

/-- iterator を `n` 回進めた状態。 -/
def advance (s : DOMState) : Nat → DOMState
  | 0 => s
  | k + 1 =>
    match s.iterators.head? with
    | none => s
    | some it =>
      match nextNode s.tree it with
      | none => s
      | some (_, it') => advance { s with iterators := [it'] } k

end Dom.Demo

open Dom Dom.Demo

def demo : IO Unit := do
  IO.println "-- Phase 1: tree model --"
  IO.println s!"checkWellFormed sample = {sample.checkWellFormed}"
  IO.println s!"preorder doc           = {reprStr (preorder sample doc)}"
  IO.println s!"root hello             = {reprStr (root sample hello)}"
  IO.println s!"ancestors hello        = {reprStr (ancestors sample hello)}"
  IO.println s!"precedes head body     = {precedes sample head body}"
  IO.println ""
  IO.println "-- Phase 2: primitive mutation --"
  IO.println s!"detach hello           : {describe ((detach sample hello).map state.withTree)}"
  IO.println s!"insertAt body/orphan   : {describe ((insertAt sample body orphan none).map state.withTree)}"
  IO.println s!"insertAt cycle         : {describe ((insertAt sample hello body none).map state.withTree)}"
  IO.println ""
  IO.println "-- Phase 3: WHATWG mutation algorithms --"
  IO.println s!"appendChild body orphan     : {describe (appendChild state body orphan)}"
  IO.println s!"removeChild html hello      : {describe (removeChild state html hello)}"
  IO.println s!"replaceChild html orphan hd : {describe (replaceChild state html orphan head)}"
  IO.println s!"replaceChildren body orphan : {describe (replaceChildren state body (some orphan))}"
  IO.println s!"before hello orphan         : {describe (before state hello orphan)}"
  IO.println s!"after hello orphan          : {describe (after state hello orphan)}"
  IO.println ""
  IO.println "-- DocumentFragment の展開 --"
  IO.println s!"appendChild body frag       : {describe (appendChild state body frag)}"
  IO.println s!"appendChild doc frag        : {describe (appendChild state doc frag)}"
  IO.println ""
  IO.println "-- Document の子に対する制約 --"
  IO.println s!"appendChild doc orphan (2nd element) : {describe (appendChild state doc orphan)}"
  IO.println s!"appendChild doc loose  (text)        : {describe (appendChild state doc loose)}"
  IO.println s!"appendChild doc dtype2 (2nd doctype) : {describe (appendChild state doc dtype2)}"
  IO.println s!"insertBefore doc dtype2 before html  : {describe (insertBefore state doc dtype2 (some html))}"
  IO.println s!"insertBefore doc orphan before dtype : {describe (insertBefore state doc orphan (some dtype))}"
  IO.println ""
  IO.println "-- moveBefore --"
  IO.println s!"moveBefore body head none    : {describe (moveBefore state body head none)}"
  IO.println s!"moveBefore head hello none   : {describe (moveBefore state head hello none)}"
  IO.println s!"moveBefore otherDoc head none: {describe (moveBefore state otherDoc head none)}"
  IO.println s!"moveBefore body orphan none  : {describe (moveBefore state body orphan none)}"
  IO.println s!"moveBefore body html none    : {describe (moveBefore state body html none)}"
  IO.println ""
  IO.println "-- Phase 5: Range の追随 --"
  IO.println s!"初期 range                   : {rangeSummary state}"
  IO.println s!"removeChild body hello       : {describeRange (removeChild state body hello)}"
  IO.println s!"appendChild body orphan      : {describeRange (appendChild state body orphan)}"
  IO.println s!"insertBefore body orphan @0  : {describeRange (insertBefore state body orphan (some hello))}"
  IO.println s!"removeChild html body        : {describeRange (removeChild state html body)}"
  IO.println ""
  IO.println "-- Phase 6: NodeIterator の追随 --"
  IO.println s!"初期 iterator                : {iterSummary state}"
  IO.println s!"nextNode x1                  : {iterSummary (advance state 1)}"
  IO.println s!"nextNode x2                  : {iterSummary (advance state 2)}"
  IO.println s!"nextNode x3                  : {iterSummary (advance state 3)}"
  IO.println s!"x2 の後で removeChild html head : {describeIter (removeChild (advance state 2) html head)}"
  IO.println s!"x3 の後で removeChild html body : {describeIter (removeChild (advance state 3) html body)}"

/-- scenario file 一つを評価して、結果の JSON を返す。 -/
def evalFile (path : System.FilePath) : IO (Except String String) := do
  let src ← IO.FS.readFile path
  return Dom.Exec.runScenarioString src

/-- 出力 file（`*.lean.json` / `*.dommy.json`）は入力として扱わない。 -/
def isScenarioFile (p : System.FilePath) : Bool :=
  let name := p.fileName.getD ""
  name.endsWith ".json" && !name.endsWith ".lean.json" && !name.endsWith ".dommy.json"

/--
`DIR/*.json` をまとめて評価し、それぞれ `DIR/<base>.lean.json` に書く。

differential testing の driver は、oracle の起動回数を減らすためにこの mode を使う。
-/
def runBatch (dir : System.FilePath) : IO UInt32 := do
  let entries ← dir.readDir
  let mut failed : UInt32 := 0
  for e in entries.qsort (fun a b => a.fileName < b.fileName) do
    if isScenarioFile e.path then
      match ← evalFile e.path with
      | .error msg =>
        IO.eprintln s!"{e.path}: {msg}"
        failed := 1
      | .ok out =>
        let base : String := (e.fileName.dropEnd 5).toString
        IO.FS.writeFile (dir / (System.FilePath.mk (base ++ ".lean.json"))) out
  return failed

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => demo; return 0
  | ["--batch", dir] => runBatch dir
  | [path] =>
    match ← evalFile path with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      return 1
    | .ok out =>
      IO.println out
      return 0
  | _ =>
    IO.eprintln "usage: dom-model [SCENARIO.json | --batch DIR]"
    return 2
