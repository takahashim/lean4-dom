import Dom

/-!
# `lake exe dom-model`

Phase 1-3 の定義が小さな木の上で動くことを確認する demo。
Phase 4 で scenario file の評価（PLAN §7）をここに足す。
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

/-- children の並びだけを見た木の要約。 -/
def summary (t : Tree) : String :=
  String.intercalate " " <|
    [doc, html, body, frag].map fun n => s!"{n}:{reprStr (childrenOf t n)}"

def describe : Except DOMException Tree → String
  | .error e => s!"error {e}"
  | .ok t => s!"ok wf={t.checkWellFormed} {summary t}"

end Dom.Demo

open Dom Dom.Demo

def main : IO Unit := do
  IO.println "-- Phase 1: tree model --"
  IO.println s!"checkWellFormed sample = {sample.checkWellFormed}"
  IO.println s!"preorder doc           = {reprStr (preorder sample doc)}"
  IO.println s!"root hello             = {reprStr (root sample hello)}"
  IO.println s!"ancestors hello        = {reprStr (ancestors sample hello)}"
  IO.println s!"precedes head body     = {precedes sample head body}"
  IO.println ""
  IO.println "-- Phase 2: primitive mutation --"
  IO.println s!"detach hello           : {describe (detach sample hello)}"
  IO.println s!"insertAt body/orphan   : {describe (insertAt sample body orphan none)}"
  IO.println s!"insertAt cycle         : {describe (insertAt sample hello body none)}"
  IO.println ""
  IO.println "-- Phase 3: WHATWG mutation algorithms --"
  IO.println s!"appendChild body orphan     : {describe (appendChild sample body orphan)}"
  IO.println s!"removeChild html hello      : {describe (removeChild sample html hello)}"
  IO.println s!"replaceChild html orphan hd : {describe (replaceChild sample html orphan head)}"
  IO.println s!"replaceChildren body orphan : {describe (replaceChildren sample body (some orphan))}"
  IO.println s!"before hello orphan         : {describe (before sample hello orphan)}"
  IO.println s!"after hello orphan          : {describe (after sample hello orphan)}"
  IO.println ""
  IO.println "-- DocumentFragment の展開 --"
  IO.println s!"appendChild body frag       : {describe (appendChild sample body frag)}"
  IO.println s!"appendChild doc frag        : {describe (appendChild sample doc frag)}"
  IO.println ""
  IO.println "-- Document の子に対する制約 --"
  IO.println s!"appendChild doc orphan (2nd element) : {describe (appendChild sample doc orphan)}"
  IO.println s!"appendChild doc loose  (text)        : {describe (appendChild sample doc loose)}"
  IO.println s!"appendChild doc dtype2 (2nd doctype) : {describe (appendChild sample doc dtype2)}"
  IO.println s!"insertBefore doc dtype2 before html  : {describe (insertBefore sample doc dtype2 (some html))}"
  IO.println s!"insertBefore doc orphan before dtype : {describe (insertBefore sample doc orphan (some dtype))}"
  IO.println ""
  IO.println "-- moveBefore --"
  IO.println s!"moveBefore body head none    : {describe (moveBefore sample body head none)}"
  IO.println s!"moveBefore head hello none   : {describe (moveBefore sample head hello none)}"
  IO.println s!"moveBefore otherDoc head none: {describe (moveBefore sample otherDoc head none)}"
  IO.println s!"moveBefore body orphan none  : {describe (moveBefore sample body orphan none)}"
  IO.println s!"moveBefore body html none    : {describe (moveBefore sample body html none)}"
