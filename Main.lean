import Dom

/-!
# `lake exe dom-model`

Phase 1 では、小さな木に対して走査が動くことを確認するだけの demo を実行する。
Phase 4 で scenario file の評価（PLAN §7）をここに足す。
-/

namespace Dom.Demo

/-- `document → html → (head, body → "hello")` という木。 -/
def doc : NodeId := ⟨0⟩
def html : NodeId := ⟨1⟩
def head : NodeId := ⟨2⟩
def body : NodeId := ⟨3⟩
def hello : NodeId := ⟨4⟩

def sample : Tree :=
  { nodes :=
      NodeStore.empty
        |>.insert doc { kind := .document, children := [html], ownerDocument := doc }
        |>.insert html
            { kind := .element, parent := some doc, children := [head, body],
              ownerDocument := doc }
        |>.insert head { kind := .element, parent := some html, ownerDocument := doc }
        |>.insert body
            { kind := .element, parent := some html, children := [hello], ownerDocument := doc }
        |>.insert hello
            { kind := .text, parent := some body, ownerDocument := doc, data := "hello" } }

/-- `hello` を木から外した状態。`parent` と `children` の整合が崩れるので well-formed でない。 -/
def broken : Tree :=
  { sample with
      nodes := sample.nodes.insert body
        { kind := .element, parent := some html, children := [hello, hello],
          ownerDocument := doc } }

end Dom.Demo

open Dom Dom.Demo

def main : IO Unit := do
  IO.println s!"checkWellFormed sample  = {sample.checkWellFormed}"
  IO.println s!"checkWellFormed broken  = {broken.checkWellFormed}"
  IO.println s!"preorder sample doc     = {reprStr (preorder sample doc)}"
  IO.println s!"treeOrder sample hello  = {reprStr (treeOrder sample hello)}"
  IO.println s!"root sample hello       = {reprStr (root sample hello)}"
  IO.println s!"ancestors sample hello  = {reprStr (ancestors sample hello)}"
  IO.println s!"depth sample hello      = {depth sample hello}"
  IO.println s!"index sample body       = {reprStr (index sample body)}"
  IO.println s!"precedes head body      = {precedes sample head body}"
  IO.println s!"precedes body head      = {precedes sample body head}"
  IO.println s!"precedes html hello     = {precedes sample html hello}"
