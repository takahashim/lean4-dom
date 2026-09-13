import Dom.Mutation.Api
import Dom.Attribute.Algorithms
import Dom.Range.Adjust
import Dom.Traversal.NodeIterator
import Dom.CharacterData.ReplaceData
import Dom.Observation
import Dom.Observer.Deliver

/-!
# scenario の型

固定 scenario の入力（初期状態と操作列）と、一 step の結果を表す型。

**入出力形式から切り離してある。** これらは JSON とは独立した概念で、
操作列に沿った状態遷移の証明（`Dom/Exec/Invariant.lean`、`Dom/Properties/Counterexample.lean`）が
`Lean.Data.Json` に依存しないようにするためである。
JSON との変換は `Dom/Exec/Json.lean`、評価は `Dom/Exec/Eval.lean` にある。
-/

namespace Dom.Exec

/-! ## scenario の表現 -/

/-- 初期状態の node 一つぶんの記述。 -/
structure NodeSpec where
  id : Nat
  kind : NodeKind
  parent : Option Nat := none
  ownerDocument : Option Nat := none
  data : String := ""
  /-- 初期 attribute list。Element 以外に置くと loader が拒否する。 -/
  attributes : List Attr := []
  /--
  Element の namespace / namespace prefix / local name。

  省略すると HTML namespace の `div` になる。差分テストの相手（Dommy）の
  `document.createElement("div")` がそうだからで、既存の scenario はこれで動く。
  -/
  «namespace» : Option String := none
  «prefix» : Option String := none
  localName : Option String := none
  /-- Document の type が "html" か。省略すると true（Dommy の `Window` の document）。 -/
  isHTMLDocument : Option Bool := none
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
  | iteratorNext (index : Nat)
  | iteratorPrevious (index : Nat)
  | replaceData (node : Nat) (offset count : Nat) (data : String)
  | appendData (node : Nat) (data : String)
  | insertData (node : Nat) (offset : Nat) (data : String)
  | deleteData (node : Nat) (offset count : Nat)
  | setData (node : Nat) (data : String)
  /-- `Node.normalize()`。 -/
  | normalize (target : Nat)
  /-- `Element.setAttribute(qualifiedName, value)`。 -/
  | setAttribute (element : Nat) (qualifiedName value : String)
  /-- `Element.setAttributeNS(namespace, qualifiedName, value)`。 -/
  | setAttributeNS (element : Nat) («namespace» : Option String) (qualifiedName value : String)
  /-- `Element.removeAttribute(qualifiedName)`。 -/
  | removeAttribute (element : Nat) (qualifiedName : String)
  /-- `Element.removeAttributeNS(namespace, localName)`。 -/
  | removeAttributeNS (element : Nat) («namespace» : Option String) (localName : String)
  /-- `Element.toggleAttribute(qualifiedName, force)`。 -/
  | toggleAttribute (element : Nat) (qualifiedName : String) (force : Option Bool)
  /-- `MutationObserver.observe(target, options)`。 -/
  | observe (observer : Nat) (target : Nat) (opts : MutationObserverInit)
  /-- `MutationObserver.disconnect()`。 -/
  | disconnect (observer : Nat)
  /-- `MutationObserver.takeRecords()`。 -/
  | takeRecords (observer : Nat)
  /-- microtask checkpoint。"notify mutation observers" を走らせる。 -/
  | notify
deriving Repr

/--
scenario での MutationObserver。

一つの observer が一つの node を観測する形だけを扱う。
仕様の `observe(target, options)` を一度だけ呼んだ状態にあたる。
-/
structure ObserverSpec where
  /--
  `observe(target, options)` を一度呼んだ状態にする。

  `none` なら registration を持たない observer を作るだけである。
  scenario 側で `observe` 操作を使う場合はこちらを指定する。
  -/
  target : Option Nat := none
  subtree : Bool := false
  childList : Bool := false
  attributes : Bool := false
  attributeOldValue : Bool := false
  attributeFilter : Option (List String) := none
  characterData : Bool := false
  characterDataOldValue : Bool := false
deriving Repr

/-- 一つの scenario。 -/
structure Scenario where
  nodes : List NodeSpec
  ranges : List RangeState := []
  iterators : List IteratorState := []
  observers : List ObserverSpec := []
  operations : List Operation
deriving Repr

/--
一 step の結果。

例外で失敗した step でも、**変わっていない状態**を観測として出す。
Dommy は木をその場で書き換えるので、失敗した操作が状態を変えていないことも比較対象になる。
-/
inductive StepResult where
  | ok (s : DOMState) (delivered : List (Nat × List MutationRecord)) (returned : ReturnValue)
  | failed (before : DOMState) (e : DOMException)

end Dom.Exec
