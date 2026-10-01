import Dom.Selector.Match
import Dom.Mutation.Create

/-!
# id・class・name で element を引く method

`getElementById()`（DOM §4.2.4 `NonElementParentNode`）、`getElementsByClassName()`
（DOM §4.5・§4.9 "list of elements with class names"）、`getElementsByName()`（HTML §3.1.5）。
どれも selector ではなく **attribute の値との比較** で定まる。

木も live object も変えないので、どれも `Tree` の上の純関数である。差分テストでは操作の
戻り値としてだけ観測する。返す collection は live だが、操作した時点の中身を比べれば足りる。

## quirks mode

`getElementsByClassName()` は、受け手の node document が quirks mode なら class を
ASCII case-insensitive に比べる。`getElementById()` は mode に依らず identical に比べる
（DOM は ID の比較を case-sensitive と定め、quirks mode の扱いを持つのは selector と
class の一覧だけである）。
-/

namespace Dom

/-! ## receiver の種別 -/

/-- `getElementById()` は `NonElementParentNode`、つまり Document と DocumentFragment の method である。 -/
def requireNonElementParentNode (t : Tree) (node : NodeId) : Except DOMException Unit :=
  match t.get? node with
  | some d => if d.kind == .document || d.kind == .documentFragment then .ok () else .error .typeError
  | none => .error .typeError

/-- `getElementsByClassName()` は Document と Element の method である。 -/
def requireDocumentOrElement (t : Tree) (node : NodeId) : Except DOMException Unit :=
  match t.get? node with
  | some d => if d.kind == .document || d.kind == .element then .ok () else .error .typeError
  | none => .error .typeError

/-- `node` の descendant である element を tree order に並べる。 -/
def descendantElements (t : Tree) (node : NodeId) : List NodeId :=
  (preorder t node).filter (fun e => e != node && isElementNode t e)

/-! ## `getElementById()` -/

/--
DOM §4.9 の element の ID。namespace の無い `id` attribute の値で、空文字列なら ID は無い
（"attribute change steps to update an element's ID"）。
-/
def elementIdOf (t : Tree) (e : NodeId) : Option String :=
  match t.get? e with
  | none => none
  | some d =>
    match plainAttr d "id" with
    | some v => if v.isEmpty then none else some v
    | none => none

/-- DOM §4.2.4 "get an element by ID"。descendant のうち、ID が `elementId` である最初の element。 -/
def getElementById (t : Tree) (node : NodeId) (elementId : String) :
    Except DOMException (Option NodeId) :=
  match requireNonElementParentNode t node with
  | .error e => .error e
  | .ok _ => .ok ((descendantElements t node).find? (fun e => elementIdOf t e == some elementId))

/-! ## `getElementsByClassName()` -/

/-- DOM §2.3 の ordered set parser。ASCII whitespace で区切り、重複を落とす。 -/
def orderedSetParse (s : String) : List String :=
  ((splitWsAux [] s.toList).map String.ofList).eraseDups

/-- DOM §4.9 の element の classes。namespace の無い `class` attribute を ordered set parser で読む。 -/
def elementClassesOf (t : Tree) (e : NodeId) : List String :=
  match t.get? e with
  | none => []
  | some d =>
    match plainAttr d "class" with
    | some v => orderedSetParse v
    | none => []

/-- 受け手 `node` の node document が quirks mode か。 -/
def receiverInQuirksMode (t : Tree) (node : NodeId) : Bool :=
  match t.get? node with
  | none => false
  | some d => inQuirksModeOf t d

/--
DOM "list of elements with class names"。`classNames` を ordered set parser で読み、空なら空。
そうでなければ、descendant のうち、そのすべての class を持つ element。受け手の node document が
quirks mode なら、class の比較は ASCII case-insensitive である。
-/
def getElementsByClassName (t : Tree) (node : NodeId) (classNames : String) :
    Except DOMException (List NodeId) :=
  match requireDocumentOrElement t node with
  | .error e => .error e
  | .ok _ =>
    let classes := orderedSetParse classNames
    let q := receiverInQuirksMode t node
    if classes.isEmpty then .ok []
    else .ok ((descendantElements t node).filter (fun e =>
      classes.all (fun c => (elementClassesOf t e).any (fun c' =>
        quirksFold q c'.toList == quirksFold q c.toList))))

/-! ## `getElementsByName()` -/

/--
HTML §3.1.5 `getElementsByName()`。document の中の **HTML element** のうち、
namespace の無い `name` attribute の値が `elementName` と同じものを tree order に並べる。
-/
def getElementsByName (t : Tree) (node : NodeId) (elementName : String) :
    Except DOMException (List NodeId) :=
  -- `getElementsByName()` は Document の method である（`Dom/Mutation/Create.lean` の検査を使う）。
  match requireDocument t node with
  | .error e => .error e
  | .ok _ =>
    .ok ((descendantElements t node).filter (fun e =>
      match t.get? e with
      | none => false
      | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some elementName))

end Dom
