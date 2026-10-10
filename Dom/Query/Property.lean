import Dom.Query.NodeQuery
import Dom.Attribute.Algorithms
import Dom.Selector.Match

/-!
# 値を読むだけの getter（§4.2.6、§4.2.8、§4.4、§4.5、§4.9、§4.10）

木を変えずに値を返す IDL attribute の getter。harness は `getProperty` でこれらを読み、
実装の同じ getter と比べる。引数も例外も無く、受け手の interface に無い getter は
JavaScript では undefined になるので、値の型は `Dom/Exec` の側で `ReturnValue` に写す。
-/

namespace Dom

/-- §4.4 `nodeName`。 -/
def nodeName (t : Tree) (n : NodeId) : Option String :=
  match t.get? n with
  | none => none
  | some d =>
    match d.kind with
    | .element => tagName t n
    | .text => some "#text"
    | .cdataSection => some "#cdata-section"
    | .processingInstruction => some d.piTarget
    | .comment => some "#comment"
    | .document => some "#document"
    | .documentType => some d.doctypeName
    | .documentFragment => some "#document-fragment"

/-- §4.4 `isConnected`：shadow-including root が document である（shadow tree は無いので root）。 -/
def isConnected (t : Tree) (n : NodeId) : Bool :=
  kindOf t (root t n) == some NodeKind.document

/-- §4.2.6 `firstElementChild`。 -/
def firstElementChild (t : Tree) (n : NodeId) : Option NodeId :=
  (elementChildrenOf t n).head?

/-- §4.2.6 `lastElementChild`。 -/
def lastElementChild (t : Tree) (n : NodeId) : Option NodeId :=
  (elementChildrenOf t n).getLast?

/-- §4.2.6 `childElementCount`。 -/
def childElementCount (t : Tree) (n : NodeId) : Nat :=
  (elementChildrenOf t n).length

/-- §4.2.8 `previousElementSibling`：前の兄弟のうち最も近い element。 -/
def previousElementSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => none
    | some (before, _) => (before.filter (isElementNode t)).getLast?

/-- §4.2.8 `nextElementSibling`：後ろの兄弟のうち最も近い element。 -/
def nextElementSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match Dom.ListUtil.splitAt? (childrenOf t p) n with
    | none => none
    | some (_, after) => (after.filter (isElementNode t)).head?

/-- §4.5 `doctype`：document の子である doctype。 -/
def doctypeOf (t : Tree) (n : NodeId) : Option NodeId :=
  (childrenOf t n).find? fun c => kindOf t c == some NodeKind.documentType

/-- §4.5 `compatMode`。 -/
def compatMode (t : Tree) (n : NodeId) : Option String :=
  match t.get? n with
  | none => none
  | some d => if inQuirksModeOf t d then some "BackCompat" else some "CSS1Compat"

end Dom
