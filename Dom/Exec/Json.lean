import Lean.Data.Json
import Dom.Exec.Types
import Dom.Exec.Invoke

/-!
# scenario の入出力

PLAN §7.1 と §7.2 の JSON 形式を読み書きする。

JSON の parse と serialize には toolchain 同梱の `Lean.Data.Json` を使う。
外部 library ではなく Lean の配布物なので、PLAN §2.1 の依存方針の範囲に収まる。
`Lean` への依存はこの file に閉じている。操作列の型は `Dom/Exec/Types.lean`、
評価は `Dom/Exec/Eval.lean` にあり、どちらも `Lean.Data.Json` を import しない。

## 入力形式

```json
{
  "nodes": [
    {"id": 0, "kind": "document"},
    {"id": 1, "kind": "element", "parent": 0},
    {"id": 2, "kind": "text", "parent": 1, "data": "abc"},
    {"id": 3, "kind": "element"}
  ],
  "ranges": [],
  "iterators": [],
  "walkers": [],
  "operations": [
    {"op": "insertBefore", "parent": 1, "node": 3, "child": null},
    {"op": "removeChild", "parent": 1, "node": 2}
  ]
}
```

* `nodes` の並び順が children の順序を決める。同じ `parent` を持つ node は、
  配列に現れた順に children へ並ぶ。
* `ownerDocument` は省略できる。省略した場合、kind が `document` の node は自分自身、
  それ以外は配列中の最初の `document` node を node document とする。
* `data` は CharacterData 以外では無視する。
* `ranges` は `{"start": {"node": 1, "offset": 0}, "end": {"node": 1, "offset": 2}}` の形。
* `iterators` は `{"root": 1, "reference": 2, "pointerBeforeReference": true}` の形。
* `walkers` は `{"root": 1, "current": 2, "whatToShow": 128}` の形。
  `current` を省略すると `root` になる（`createTreeWalker` の初期値）。

## 出力形式

```json
{
  "initial": {"nodes": [...], "ranges": [], "iterators": [], "walkers": []},
  "steps": [
    {"ok": true, "nodes": [...], "ranges": [], "iterators": [], "walkers": []},
    {"ok": false, "exception": "NotFoundError"}
  ]
}
```

例外が起きた step で評価を打ち切る（PLAN §7.2）。
-/


namespace Dom.Exec

open Lean (Json)

/-! ## kind の名前 -/

/-- JSON での kind の名前。 -/
def kindName : NodeKind → String
  | .document => "document"
  | .documentType => "documentType"
  | .documentFragment => "documentFragment"
  | .element => "element"
  | .text => "text"
  | .cdataSection => "cdataSection"
  | .processingInstruction => "processingInstruction"
  | .comment => "comment"

def kindOfName? (s : String) : Option NodeKind :=
  [NodeKind.document, .documentType, .documentFragment, .element,
    .text, .cdataSection, .processingInstruction, .comment].find? (kindName · == s)

/-! ## JSON からの復号 -/

private def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

/--
JavaScript の値（WebIDL の変換の前の値）。JSON の null・真偽値・数・文字列・object をそのまま写す。
配列は組み込みの `Array` として写す。
-/
partial def jsValueOfJson : Json → Except String Idl.JsValue
  | .null => pure .null
  | .bool b => pure (.bool b)
  | .num n => pure (.number ⟨n.mantissa, n.exponent⟩)
  | .str s => pure (.string s)
  | .obj kvs => do
    let props ← kvs.toList.mapM fun (k, v) => do pure (k, ← jsValueOfJson v)
    pure (.object props)
  | .arr xs => do
    let elems ← xs.toList.mapM jsValueOfJson
    pure (.array elems)

/--
`observe` の options。`options` があればその値、無ければ `MutationObserverInit` の member の名前の field
のうち書いてあるものだけを持つ object とみなす（`observe` の step 1-2 は member が存在するかで分岐するので、
書いていない member を補ってはいけない）。
-/
private def observeOptionsField (j : Json) : Except String Idl.JsValue := do
  match field? j "options" with
  | some v => jsValueOfJson v
  | none =>
    let keys := ["childList", "subtree", "attributes", "attributeOldValue", "attributeFilter",
      "characterData", "characterDataOldValue"]
    let props ← keys.filterMapM fun k => do
      match field? j k with
      | none => pure none
      | some v => pure (some (k, ← jsValueOfJson v))
    pure (.object props)

/--
listener の options。`options` があればその値、無ければ `capture`・`once`・`passive` の field を
持つ object とみなす（どれも無ければ空の object で、既定値と同じになる）。
-/
private def listenerOptionsField (j : Json) : Except String Idl.JsValue := do
  match field? j "options" with
  | some v => jsValueOfJson v
  | none =>
    let props ← ["capture", "once", "passive"].filterMapM fun k => do
      match field? j k with
      | none => pure none
      | some v => pure (some (k, ← jsValueOfJson v))
    pure (.object props)

/-- WebIDL の変換の結果を読み取りの結果にする。model の対象外の値（桁の多い数）は読み取りの失敗にする。 -/
private def idlValue {α : Type} (k : String) : Except IdlException α → Except String α
  | .ok a => .ok a
  | .error e => .error s!"field `{k}` の値は WebIDL の変換で {e} になる（model の対象外）"

/--
可変長の `(Node or DOMString)` 引数。`nodes` の配列の数は node の id、文字列はそのまま文字列である。
`nodes` が無ければ `node`（一つの id、または null で空）を読む。
-/
private def nodeArgsField (j : Json) : Except String (List NodeArg) := do
  match field? j "nodes" with
  | some (.arr xs) =>
    xs.toList.mapM fun x =>
      match x with
      | .str d => pure (.string d)
      | .num n =>
        if n.exponent == 0 && n.mantissa ≥ 0 then pure (.node n.mantissa.toNat)
        else throw "nodes の数は node の id（0 以上の整数）でなければならない"
      | .obj kvs =>
        if kvs.contains "attr" then throw "nodes の要素に Attr を渡す形は扱わない"
        else do pure (.string (← idlValue "nodes" (Idl.toDOMString (← jsValueOfJson x))))
      -- `(Node or DOMString)` の union への変換：node でない値は DOMString になる（null は "null"）。
      | x => do pure (.string (← idlValue "nodes" (Idl.toDOMString (← jsValueOfJson x))))
  | some _ => throw "nodes は配列でなければならない"
  | none =>
    match field? j "node" with
    | none | some .null => pure []
    | some (.num n) =>
      if n.exponent == 0 && n.mantissa ≥ 0 then pure [.node n.mantissa.toNat]
      else throw "node は node の id（0 以上の整数）でなければならない"
    | some _ => throw "node は node の id でなければならない"

private def natField (j : Json) (k : String) : Except String Nat :=
  match field? j k with
  | none => .error s!"必須の field `{k}` がない"
  | some v => v.getNat?

/-- `Node` を受ける field。数なら node、`{"attr": id}` なら `Attr`。 -/
private def refField (j : Json) (k : String) : Except String RefArg :=
  match field? j k with
  | none => .error s!"必須の field `{k}` がない"
  | some v =>
    match v.getNat? with
    | .ok n => .ok (.node n)
    | .error _ =>
      match v.getObjVal? "attr" with
      | .ok a => (a.getNat?).map .attr
      | .error _ => .error ("field `" ++ k ++ "` は node の id か {\"attr\": id} でなければならない")

private def natField? (j : Json) (k : String) : Except String (Option Nat) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getNat?).map some

/--
WebIDL の non-nullable な `Node` 引数。

JSON の `null` と、数でも `{"attr": id}` でもない値は「Node でないもの」を表し、`none` になる。field そのものが無いのは
scenario の書き誤りなので error にする（省略できる引数とは別物である）。
-/
private def nodeField (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => .error s!"必須の field `{k}` がない"
  | .ok v =>
    match v.getNat? with
    | .ok n => .ok (some n)
    | .error _ =>
      match v.getObjVal? "attr" with
      | .ok _ => .error s!"field `{k}` に Attr を渡す形は Range の操作では扱わない"
      | .error _ => .ok none

/-!
### interface 型（`Node`・`Attr`）の引数

JSON の数は node の id、`{"attr": id}` は `Attr` である。それ以外の値（null、文字列、真偽値、普通の object、
配列）は JavaScript では node でない値で、`Node` への変換は TypeError になる。`Node?` は null（と field が無い
こと）を null として受ける。
-/

/-- `Node` の引数。node でない値なら `none`（TypeError）。field が無いのは scenario の書き誤り。 -/
private def nodeArg? (j : Json) (k : String) : Except String (Option RefArg) :=
  match j.getObjVal? k with
  | .error _ => .error s!"必須の field `{k}` がない"
  | .ok v =>
    match v.getNat? with
    | .ok n => .ok (some (.node n))
    | .error _ =>
      match v with
      | .obj _ =>
        match v.getObjVal? "attr" with
        | .ok a => (a.getNat?).map (some ∘ .attr)
        | .error _ => .ok none
      | _ => .ok none

/-- `Node?` の引数の読み取りの結果。 -/
private inductive NullableArg where
  | null
  | node (r : RefArg)
  | notANode

/-- `Node?` の引数。field が無いか null なら null。 -/
private def nullableNodeArg (j : Json) (k : String) : Except String NullableArg :=
  match j.getObjVal? k with
  | .error _ => .ok .null
  | .ok .null => .ok .null
  | .ok _ => do
    match ← nodeArg? j k with
    | some r => pure (.node r)
    | none => pure .notANode

/-- `Attr` の引数。数は `Attr` の id で、それ以外は `Attr` でない値（TypeError）。 -/
private def attrArg? (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => .error s!"必須の field `{k}` がない"
  | .ok v =>
    match v.getNat? with
    | .ok n => .ok (some n)
    | .error _ => .ok none

/-- node の id だけを受ける操作で、`Attr` を渡したもの。model の対象外として読み取りを失敗させる。 -/
private def onlyNode (k : String) : RefArg → Except String Nat
  | .node n => .ok n
  | .attr _ => .error s!"field `{k}` に Attr を渡す形はこの操作では扱わない"

private def strField (j : Json) (k : String) (dflt : String) : Except String String :=
  match field? j k with
  | none => .ok dflt
  | some v => v.getStr?

private def strField? (j : Json) (k : String) : Except String (Option String) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getStr?).map some

/-!
### DOMString の引数

DOMString の引数は、JSON の任意の値を JavaScript の値として受け、scenario を読むときに WebIDL の変換を行う。
model が表す値の DOMString への変換は TypeError を投げず副作用も無い（`Idl.toDOMString_error`）ので、
method を呼ぶときに変換するのと観測は変わらない。field が無ければ既定値（多くは空文字列）を使う。
これは scenario の約束で、JavaScript の undefined を渡すこととは違う。
-/

/-- `DOMString` の引数。 -/
private def domStrField (j : Json) (k : String) (dflt : String) : Except String String :=
  match j.getObjVal? k with
  | .error _ => .ok dflt
  | .ok v => do idlValue k (Idl.toDOMString (← jsValueOfJson v))

/-- `DOMString?` の引数。field が無いか null なら null。 -/
private def nullableDomStrField (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok v => do idlValue k (Idl.toNullableDOMString (← jsValueOfJson v))

/-- `[LegacyNullToEmptyString] DOMString` の引数。null は空文字列。 -/
private def legacyNullDomStrField (j : Json) (k : String) (dflt : String) : Except String String :=
  match j.getObjVal? k with
  | .error _ => .ok dflt
  | .ok v => do idlValue k (Idl.toLegacyNullDOMString (← jsValueOfJson v))

/-!
### 整数型の引数

`unsigned long` と `unsigned short` の引数は、JSON の任意の値を受け、ToNumber で Number の値にする
（`Dom/Idl/ToNumber.lean`）。ToNumber は失敗も副作用も無いので読むときに変換してよく、ConvertToInt の残りは
`applyOperation` が行う。結果が一つに決まらない値（有効数字が 20 桁を超える十進表記など）は model の対象外で、
読み取りの失敗にする。field が無いのも失敗である（必須の引数）。
-/

private def numArgField (j : Json) (k : String) : Except String Idl.JsNum :=
  match j.getObjVal? k with
  | .error _ => throw s!"field `{k}` が無い"
  | .ok v => do
    match (← jsValueOfJson v).toNumber with
    | some x => pure x
    | none => throw s!"field `{k}` の値は ToNumber の結果が一つに決まらない（model の対象外）"

/-!
### boolean の引数

boolean の引数も JSON の任意の値を受け、ECMAScript の ToBoolean で変換する。ToBoolean は失敗も副作用も無いので、
DOMString と同じく読むときに変換してよい。field が無ければ引数を省略したことにする（`optional` なら既定値、
既定値が無ければ `none`）。null は省略ではなく、false を渡したことになる。
-/

/-- 既定値の無い `optional boolean` の引数。 -/
private def boolArgField? (j : Json) (k : String) : Except String (Option Bool) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok v => do pure (some (← jsValueOfJson v).toBoolean)

/-- 既定値のある `optional boolean` の引数（と dictionary の boolean の member）。 -/
private def boolArgField (j : Json) (k : String) (dflt : Bool) : Except String Bool := do
  pure ((← boolArgField? j k).getD dflt)

/--
`importNode` の options。`options` があればその値、無ければ `deep` の値、どちらも無ければ引数の既定値の false。
-/
private def importOptionsField (j : Json) : Except String Idl.JsValue :=
  match j.getObjVal? "options" with
  | .ok v => jsValueOfJson v
  | .error _ =>
    match j.getObjVal? "deep" with
    | .ok v => jsValueOfJson v
    | .error _ => pure (.bool false)

/-- 可変長の `DOMString...` の引数。配列の要素をそれぞれ DOMString に変換する。 -/
private def domStrListField (j : Json) (k : String) : Except String (List String) :=
  match field? j k with
  | none => .ok []
  | some v => do
    let arr ← v.getArr?
    arr.toList.mapM fun x => do idlValue k (Idl.toDOMString (← jsValueOfJson x))

private def boolField? (j : Json) (k : String) : Except String (Option Bool) :=
  match field? j k with
  | none => .ok none
  | some v => (v.getBool?).map some

private def strListField? (j : Json) (k : String) : Except String (Option (List String)) :=
  match field? j k with
  | none => .ok none
  | some v => do
    let arr ← v.getArr?
    return some (← arr.toList.mapM (·.getStr?))

/--
初期状態の attribute を読む。

`id` は scenario には書かない。`buildTree` が **node の id の昇順・node の中では
list 順**に振り直す（`numberAttributes`）ので、ここでは仮に 0 を置く。
-/
def attrOfJson (j : Json) : Except String Attr := do
  -- node document は loader が element（detach された `Attr` なら既定の document）から決める。
  return { id := ⟨0⟩
           ownerDocument := ⟨0⟩
           «namespace» := ← strField? j "namespace"
           «prefix» := ← strField? j "prefix"
           localName := ← strField j "localName" ""
           value := ← strField j "value" "" }

def nodeSpecOfJson (j : Json) : Except String NodeSpec := do
  let id ← natField j "id"
  let kindStr ← strField j "kind" ""
  let some kind := kindOfName? kindStr
    | .error s!"未知の kind `{kindStr}`（node {id}）"
  let parent ← natField? j "parent"
  let ownerDocument ← natField? j "ownerDocument"
  let data ← strField j "data" ""
  let attributes ← match field? j "attributes" with
    | none => pure ([] : List Attr)
    | some v => do (← v.getArr?).toList.mapM attrOfJson
  let «namespace» ← strField? j "namespace"
  let «prefix» ← strField? j "prefix"
  let localName ← strField? j "localName"
  let isHTMLDocument ← boolField? j "isHTMLDocument"
  let mode ← match ← strField? j "mode" with
    | none | some "no-quirks" => pure DocumentMode.noQuirks
    | some "quirks" => pure .quirks
    | some "limited-quirks" => pure .limitedQuirks
    | some m => .error s!"未知の mode `{m}`（node {id}）"
  return { id, kind, parent, ownerDocument, data, attributes,
           «namespace», «prefix», localName, isHTMLDocument, mode }

def operationOfJson (j : Json) : Except String Operation := do
  let op ← strField j "op" ""
  -- WebIDL の overload resolution：渡した引数（`argc`）が必須の個数より少なければ TypeError。
  -- `argc` が無ければ、すべての引数を渡したことにする。必須の個数以上なら、渡さなかった後ろの引数は
  -- field を書かない（省略した引数の既定値になる）約束である。
  match j.getObjVal? "argc" with
  | .ok v =>
    let argc ← v.getNat?
    match requiredArgs op with
    | none => throw s!"op `{op}` には argc を書けない"
    | some r => if argc < r then return .argumentTypeError op
  | .error _ => pure ()
  match op with
  | "appendChild" =>
    let p ← refField j "parent"
    match ← nodeArg? j "node" with
    | none => return .argumentTypeError "appendChild"
    | some n =>
      match p, n with
      | .node p, .node n => return .appendChild p n
      | p, n => return .appendChildRef p n
  | "insertBefore" =>
    let parent ← natField j "parent"
    match ← nodeArg? j "node", ← nullableNodeArg j "child" with
    | none, _ | _, .notANode => return .argumentTypeError "insertBefore"
    | some n, .null => return .insertBefore parent (← onlyNode "node" n) none
    | some n, .node c => return .insertBefore parent (← onlyNode "node" n) (some (← onlyNode "child" c))
  | "replaceChild" =>
    let parent ← natField j "parent"
    match ← nodeArg? j "node", ← nodeArg? j "child" with
    | some n, some c => return .replaceChild parent (← onlyNode "node" n) (← onlyNode "child" c)
    | _, _ => return .argumentTypeError "replaceChild"
  | "removeChild" =>
    let parent ← natField j "parent"
    match ← nodeArg? j "node" with
    | some n => return .removeChild parent (← onlyNode "node" n)
    | none => return .argumentTypeError "removeChild"
  | "replaceChildren" => return .replaceChildren (← natField j "parent") (← nodeArgsField j)
  | "prepend" => return .prepend (← natField j "parent") (← nodeArgsField j)
  | "append" => return .append (← natField j "parent") (← nodeArgsField j)
  | "before" => return .before (← natField j "target") (← nodeArgsField j)
  | "after" => return .after (← natField j "target") (← nodeArgsField j)
  | "replaceWith" => return .replaceWith (← natField j "target") (← nodeArgsField j)
  | "remove" => return .remove (← natField j "target")
  | "moveBefore" =>
    let parent ← natField j "parent"
    match ← nodeArg? j "node", ← nullableNodeArg j "child" with
    | none, _ | _, .notANode => return .argumentTypeError "moveBefore"
    | some n, .null => return .moveBefore parent (← onlyNode "node" n) none
    | some n, .node c => return .moveBefore parent (← onlyNode "node" n) (some (← onlyNode "child" c))
  | "iteratorNext" => return .iteratorNext (← natField j "iterator")
  | "iteratorPrevious" => return .iteratorPrevious (← natField j "iterator")
  | "replaceData" =>
    return .replaceData (← natField j "node") (← numArgField j "offset") (← numArgField j "count")
      (← domStrField j "data" "")
  | "appendData" => return .appendData (← natField j "node") (← domStrField j "data" "")
  | "insertData" =>
    return .insertData (← natField j "node") (← numArgField j "offset") (← domStrField j "data" "")
  | "deleteData" =>
    return .deleteData (← natField j "node") (← numArgField j "offset") (← numArgField j "count")
  | "setData" => return .setData (← natField j "node") (← legacyNullDomStrField j "data" "")
  | "normalize" => return .normalize (← natField j "target")
  | "createElement" =>
    return .createElement (← natField j "document") (← domStrField j "localName" "")
  | "createElementNS" =>
    return .createElementNS (← natField j "document") (← nullableDomStrField j "namespace")
      (← domStrField j "name" "")
  | "createTextNode" =>
    return .createTextNode (← natField j "document") (← domStrField j "data" "")
  | "createComment" =>
    return .createComment (← natField j "document") (← domStrField j "data" "")
  | "createDocumentFragment" => return .createDocumentFragment (← natField j "document")
  | "cloneNode" =>
    match ← refField j "node" with
    | .node n => return .cloneNode n (← boolArgField j "deep" false)
    | .attr a => return .cloneAttr a
  | "importNode" =>
    let doc ← natField j "document"
    match ← nodeArg? j "node" with
    | none => return .argumentTypeError "importNode"
    | some (.node n) => return .importNode doc n (← importOptionsField j)
    | some (.attr a) => return .importAttr doc a
  | "adoptNode" =>
    let doc ← natField j "document"
    match ← nodeArg? j "node" with
    | none => return .argumentTypeError "adoptNode"
    | some (.node n) => return .adoptNode doc n
    | some (.attr a) => return .adoptAttr doc a
  | "createAttribute" =>
    return .createAttribute (← natField j "document") (← domStrField j "name" "")
  | "createAttributeNS" =>
    return .createAttributeNS (← natField j "document") (← nullableDomStrField j "namespace")
      (← domStrField j "name" "")
  | "getAttributeNode" =>
    return .getAttributeNode (← natField j "element") (← domStrField j "name" "")
  | "getAttributeNodeNS" =>
    return .getAttributeNodeNS (← natField j "element") (← nullableDomStrField j "namespace")
      (← domStrField j "name" "")
  | "setAttributeNode" =>
    let e ← natField j "element"
    match ← attrArg? j "attr" with
    | some a => return .setAttributeNode e a
    | none => return .argumentTypeError "setAttributeNode"
  | "removeAttributeNode" =>
    let e ← natField j "element"
    match ← attrArg? j "attr" with
    | some a => return .removeAttributeNode e a
    | none => return .argumentTypeError "removeAttributeNode"
  | "removeNamedItem" =>
    return .removeNamedItem (← natField j "element") (← domStrField j "name" "")
  | "rangeSetStart" =>
    return .rangeSetStart (← natField j "range") (← nodeField j "node") (← numArgField j "offset")
  | "rangeSetEnd" =>
    return .rangeSetEnd (← natField j "range") (← nodeField j "node") (← numArgField j "offset")
  | "rangeSetStartBefore" =>
    return .rangeSetStartSibling (← natField j "range") (← nodeField j "node") false
  | "rangeSetStartAfter" =>
    return .rangeSetStartSibling (← natField j "range") (← nodeField j "node") true
  | "rangeSetEndBefore" =>
    return .rangeSetEndSibling (← natField j "range") (← nodeField j "node") false
  | "rangeSetEndAfter" =>
    return .rangeSetEndSibling (← natField j "range") (← nodeField j "node") true
  | "rangeCollapse" =>
    return .rangeCollapse (← natField j "range") (← boolArgField j "toStart" false)
  | "rangeSelectNode" => return .rangeSelectNode (← natField j "range") (← nodeField j "node")
  | "rangeSelectNodeContents" =>
    return .rangeSelectNodeContents (← natField j "range") (← nodeField j "node")
  | "rangeIsPointInRange" =>
    return .rangeIsPointInRange (← natField j "range") (← nodeField j "node")
      (← numArgField j "offset")
  | "rangeIntersectsNode" =>
    return .rangeIntersectsNode (← natField j "range") (← nodeField j "node")
  | "rangeCompareBoundaryPoints" =>
    return .rangeCompareBoundaryPoints (← natField j "range") (← numArgField j "how")
      (← natField j "source")
  | "rangeComparePoint" =>
    return .rangeComparePoint (← natField j "range") (← nodeField j "node")
      (← numArgField j "offset")
  | "rangeDeleteContents" => return .rangeDeleteContents (← natField j "range")
  | "rangeInsertNode" => return .rangeInsertNode (← natField j "range") (← nodeField j "node")
  | "walkerParentNode" => return .walkerMove (← natField j "walker") .parentNode
  | "walkerFirstChild" => return .walkerMove (← natField j "walker") .firstChild
  | "walkerLastChild" => return .walkerMove (← natField j "walker") .lastChild
  | "walkerPreviousSibling" => return .walkerMove (← natField j "walker") .previousSibling
  | "walkerNextSibling" => return .walkerMove (← natField j "walker") .nextSibling
  | "walkerPreviousNode" => return .walkerMove (← natField j "walker") .previousNode
  | "walkerNextNode" => return .walkerMove (← natField j "walker") .nextNode
  | "rangeToString" => return .rangeToString (← natField j "range")
  | "compareDocumentPosition" =>
    let n ← refField j "node"
    match n, ← nodeArg? j "other" with
    | _, none => return .argumentTypeError "compareDocumentPosition"
    | .node n, some (.node o) => return .compareDocumentPosition n o
    | n, some o => return .compareDocumentPositionRef n o
  | "nodeContains" =>
    let n ← refField j "node"
    match n, ← nullableNodeArg j "other" with
    | _, .notANode => return .argumentTypeError "contains"
    | n, .null => return .nodeContainsNull n
    | .node n, .node (.node o) => return .nodeContains n o
    | n, .node o => return .nodeContainsRef n o
  | "getRootNode" =>
    match ← refField j "node" with
    | .node n => return .getRootNode n
    | .attr a => return .attrQuery a .getRootNode
  | "isEqualNode" =>
    let n ← refField j "node"
    match n, ← nullableNodeArg j "other" with
    | _, .notANode => return .argumentTypeError "isEqualNode"
    | n, .null => return .isEqualNodeNull n
    | .node n, .node (.node o) => return .isEqualNode n o
    | n, .node o => return .isEqualNodeRef n o
  | "getTextContent" =>
    match ← refField j "node" with
    | .node n => return .getTextContent n
    | .attr a => return .attrQuery a .textContent
  | "getNodeValue" =>
    match ← refField j "node" with
    | .node n => return .getNodeValue n
    | .attr a => return .attrQuery a .nodeValue
  | "attrQuery" =>
    let q ← match ← strField j "query" "" with
      | "ownerDocument" => pure AttrQuery.ownerDocument
      | "parentNode" => pure .parentNode
      | "parentElement" => pure .parentElement
      | "ownerElement" => pure .ownerElement
      | "getRootNode" => pure .getRootNode
      | "nodeName" => pure .nodeName
      | "nodeValue" => pure .nodeValue
      | "textContent" => pure .textContent
      | "isConnected" => pure .isConnected
      | "hasChildNodes" => pure .hasChildNodes
      | "firstChild" => pure .firstChild
      | other => throw s!"未知の attrQuery `{other}`"
    return .attrQuery (← natField j "attr") q
  | "setAttrValue" =>
    let via ← match ← strField j "via" "value" with
      | "value" => pure AttrSetter.value
      | "nodeValue" => pure .nodeValue
      | "textContent" => pure .textContent
      | other => throw s!"未知の setter `{other}`"
    -- `Attr.value` は `DOMString`、`nodeValue` と `textContent` は `DOMString?` で、Attr の setter は null を
    -- 空文字列として扱う。
    let value ← match via with
      | .value => domStrField j "value" ""
      | _ => do pure ((← nullableDomStrField j "value").getD "")
    return .setAttrValue (← natField j "attr") value via
  | "substringData" =>
    return .substringData (← natField j "node") (← numArgField j "offset") (← numArgField j "count")
  | "getAttribute" => return .getAttribute (← natField j "element") (← domStrField j "name" "")
  | "hasAttribute" => return .hasAttribute (← natField j "element") (← domStrField j "name" "")
  | "getAttributeNames" => return .getAttributeNames (← natField j "element")
  | "querySelector" => return .querySelector (← natField j "node") (← domStrField j "selectors" "")
  | "querySelectorAll" =>
    return .querySelectorAll (← natField j "node") (← domStrField j "selectors" "")
  | "matches" => return .matchesSelector (← natField j "element") (← domStrField j "selectors" "")
  | "closest" => return .closest (← natField j "element") (← domStrField j "selectors" "")
  | "getElementById" =>
    return .getElementById (← natField j "node") (← domStrField j "elementId" "")
  | "getElementsByClassName" =>
    return .getElementsByClassName (← natField j "node") (← domStrField j "classNames" "")
  | "getElementsByName" =>
    return .getElementsByName (← natField j "node") (← domStrField j "elementName" "")
  | "lookupNamespaceURI" =>
    match ← refField j "node" with
    | .node n => return .lookupNamespaceURI n (← nullableDomStrField j "prefix")
    | .attr a => return .attrLookupNamespaceURI a (← nullableDomStrField j "prefix")
  | "lookupPrefix" =>
    match ← refField j "node" with
    | .node n => return .lookupPrefix n (← nullableDomStrField j "namespace")
    | .attr a => return .attrLookupPrefix a (← nullableDomStrField j "namespace")
  | "isDefaultNamespace" =>
    match ← refField j "node" with
    | .node n => return .isDefaultNamespace n (← nullableDomStrField j "namespace")
    | .attr a => return .attrIsDefaultNamespace a (← nullableDomStrField j "namespace")
  | "addEventListener" =>
    return .addEventListener (← natField j "target") (← domStrField j "type" "")
      (← natField j "source") (← listenerOptionsField j)
  | "removeEventListener" =>
    return .removeEventListener (← natField j "target") (← domStrField j "type" "")
      (← natField j "callback") (← listenerOptionsField j)
  | "dispatchEvent" =>
    return .dispatchEvent (← natField j "target") (← domStrField j "type" "")
      (← boolArgField j "bubbles" false) (← boolArgField j "cancelable" false)
  | "setAttribute" =>
    return .setAttribute (← natField j "element") (← domStrField j "name" "")
      (← domStrField j "value" "")
  | "setAttributeNS" =>
    return .setAttributeNS (← natField j "element") (← nullableDomStrField j "namespace")
      (← domStrField j "name" "") (← domStrField j "value" "")
  | "removeAttribute" =>
    return .removeAttribute (← natField j "element") (← domStrField j "name" "")
  | "removeAttributeNS" =>
    return .removeAttributeNS (← natField j "element") (← nullableDomStrField j "namespace")
      (← domStrField j "name" "")
  | "toggleAttribute" =>
    return .toggleAttribute (← natField j "element") (← domStrField j "name" "")
      (← boolArgField? j "force")
  | "getReflected" =>
    let p ← strField j "property" ""
    match reflectSpec p with
    | some r => return .getReflected (← natField j "element") p r
    | none => throw s!"model が持たない reflect `{p}`"
  | "setReflected" =>
    let p ← strField j "property" ""
    match reflectSpec p with
    | some r =>
      match r.kind with
      | .string => return .setReflected (← natField j "element") p r (← domStrField j "value" "")
      | .boolean =>
        match ← boolArgField? j "value" with
        | some b => return .setReflectedBool (← natField j "element") p r b
        | none => throw s!"boolean の reflect `{p}` には boolean の value が要る"
    | none => throw s!"model が持たない reflect `{p}`"
  | "datasetGet" => return .datasetGet (← natField j "element") (← domStrField j "name" "")
  | "datasetSet" =>
    return .datasetSet (← natField j "element") (← domStrField j "name" "") (← domStrField j "value" "")
  | "datasetDelete" => return .datasetDelete (← natField j "element") (← domStrField j "name" "")
  | "datasetKeys" => return .datasetKeys (← natField j "element")
  | "classListAdd" =>
    return .classListAdd (← natField j "element") (← domStrListField j "tokens")
  | "classListRemove" =>
    return .classListRemove (← natField j "element") (← domStrListField j "tokens")
  | "classListToggle" =>
    return .classListToggle (← natField j "element") (← domStrField j "token" "")
      (← boolArgField? j "force")
  | "classListReplace" =>
    return .classListReplace (← natField j "element") (← domStrField j "token" "")
      (← domStrField j "newToken" "")
  | "classListContains" =>
    return .classListContains (← natField j "element") (← domStrField j "token" "")
  | "childrenNamedItem" =>
    return .childrenNamedItem (← natField j "node") (← domStrField j "key" "")
  | "observe" =>
    let mo ← natField j "observer"
    match ← nodeArg? j "target" with
    | some t => return .observe mo (← onlyNode "target" t) (← observeOptionsField j)
    | none => return .argumentTypeError "observe"
  | "disconnect" => return .disconnect (← natField j "observer")
  | "takeRecords" => return .takeRecords (← natField j "observer")
  | "notify" => return .notify
  | _ => .error s!"未知の op `{op}`"

def boundaryPointOfJson (j : Json) : Except String BoundaryPoint := do
  return { node := ⟨← natField j "node"⟩, offset := ← natField j "offset" }

def iteratorOfJson (j : Json) : Except String IteratorState := do
  let pb ← match field? j "pointerBeforeReference" with
    | none => pure false
    | some (Json.bool b) => pure b
    | some _ => .error "pointerBeforeReference は boolean でなければならない"
  let whatToShow ← match field? j "whatToShow" with
    | none => pure 0xFFFFFFFF
    | some v => v.getNat?
  return { root := ⟨← natField j "root"⟩, reference := ⟨← natField j "reference"⟩,
           pointerBeforeReference := pb, whatToShow }

/--
`TreeWalker` の読み取り。

`current` を省略すると `root` になる（`createTreeWalker` が置く初期値）。
-/
def walkerOfJson (j : Json) : Except String WalkerState := do
  let root ← natField j "root"
  let current ← match field? j "current" with
    | none => pure root
    | some v => v.getNat?
  let whatToShow ← match field? j "whatToShow" with
    | none => pure 0xFFFFFFFF
    | some v => v.getNat?
  return { root := ⟨root⟩, current := ⟨current⟩, whatToShow }

/--
listener の callback の代わりの副作用。

文字列なら引数の無いもの、object なら `kind` と引数を読む。
-/
def listenerActionOfJson (j : Option Json) : Except String ListenerAction :=
  match j with
  | none => .ok .none
  | some (Json.str "none") => .ok .none
  | some (Json.str "stopPropagation") => .ok .stopPropagation
  | some (Json.str "stopImmediatePropagation") => .ok .stopImmediatePropagation
  | some (Json.str "preventDefault") => .ok .preventDefault
  | some (Json.obj o) => do
    let j := Json.obj o
    let some (Json.str kind) := field? j "kind" | .error "action に `kind` がない"
    match kind with
    | "removeListener" => return .removeListener (← natField j "index")
    | "addListener" =>
      return .addListener (← natField j "target") (← strField j "type" "")
        (← natField j "source") ((← boolField? j "capture").getD false)
    | k => .error s!"知らない listener action: {k}"
  | some _ => .error "action は文字列か object でなければならない"

/--
scenario の listener と、その passive（無ければ default passive value にする）。
`callback` を省略すると宣言順の番号になる。
-/
def listenerOfJson (j : Json) (index : Nat) : Except String (EventListener × Option Bool) := do
  let action ← listenerActionOfJson (field? j "action")
  return ({ target := ⟨← natField j "target"⟩
            «type» := ← strField j "type" ""
            callback := (← natField? j "callback").getD index
            capture := (← boolField? j "capture").getD false
            once := (← boolField? j "once").getD false
            action := action }, ← boolField? j "passive")

def rangeOfJson (j : Json) : Except String RangeState := do
  let some st := field? j "start" | .error "range に `start` がない"
  let some en := field? j "end" | .error "range に `end` がない"
  return { start := ← boundaryPointOfJson st, «end» := ← boundaryPointOfJson en }

def observerOfJson (j : Json) : Except String ObserverSpec := do
  let target ← natField? j "target"
  let flag (name : String) : Except String Bool :=
    match field? j name with
    | none => pure false
    | some v => v.getBool?
  return { target
           subtree := ← flag "subtree"
           childList := ← flag "childList"
           attributes := ← flag "attributes"
           attributeOldValue := ← flag "attributeOldValue"
           attributeFilter := ← strListField? j "attributeFilter"
           characterData := ← flag "characterData"
           characterDataOldValue := ← flag "characterDataOldValue" }

def scenarioOfJson (j : Json) : Except String Scenario := do
  let nodesJson ← match field? j "nodes" with
    | none => .error "`nodes` がない"
    | some v => v.getArr?
  let opsJson ← match field? j "operations" with
    | none => pure #[]
    | some v => v.getArr?
  let rangesJson ← match field? j "ranges" with
    | none => pure #[]
    | some v => v.getArr?
  let itersJson ← match field? j "iterators" with
    | none => pure #[]
    | some v => v.getArr?
  let walkersJson ← match field? j "walkers" with
    | none => pure #[]
    | some v => v.getArr?
  let listenersJson ← match field? j "listeners" with
    | none => pure #[]
    | some v => v.getArr?
  let obsJson ← match field? j "observers" with
    | none => pure #[]
    | some v => v.getArr?
  let nodes ← nodesJson.toList.mapM nodeSpecOfJson
  let ranges ← rangesJson.toList.mapM rangeOfJson
  let iterators ← itersJson.toList.mapM iteratorOfJson
  let walkers ← walkersJson.toList.mapM walkerOfJson
  let listenersWithPassive ← listenersJson.toList.zipIdx.mapM fun (l, i) => listenerOfJson l i
  let listeners := listenersWithPassive.map (·.1)
  let listenerPassive := listenersWithPassive.map (·.2)
  let observers ← obsJson.toList.mapM observerOfJson
  let operations ← opsJson.toList.mapM operationOfJson
  return { nodes, ranges, iterators, walkers, listeners, listenerPassive, observers, operations }

def scenarioOfString (s : String) : Except String Scenario := do
  scenarioOfJson (← Json.parse s)

/-! ## JSON への符号化 -/

private def natJson (n : Nat) : Json := Json.num (Int.ofNat n)

private def optNatJson : Option NodeId → Json
  | none => Json.null
  | some n => natJson n.id

/--
観測できる node の外部表現。

`Dom/Observation.lean` の `ObservedNode` の各 field をそのまま並べる。
-/
def optStrJson : Option String → Json
  | none => Json.null
  | some v => Json.str v

def attrJson (a : Attr) : Json :=
  Json.mkObj
    [ ("id", natJson a.id.id)
    , ("namespace", optStrJson a.namespace)
    , ("prefix", optStrJson a.prefix)
    , ("localName", Json.str a.localName)
    , ("value", Json.str a.value) ]

def observedNodeJson (n : ObservedNode) : Json :=
  Json.mkObj
    [ ("id", natJson n.id.id)
    , ("kind", Json.str (kindName n.kind))
    , ("parent", optNatJson n.parent)
    , ("children", Json.arr (n.children.map fun c => natJson c.id).toArray)
    , ("nodeDocument", natJson n.nodeDocument.id)
    , ("data", Json.str n.data)
    , ("attributes", Json.arr (n.attributes.map attrJson).toArray)
    , ("namespace", optStrJson n.namespace)
    , ("prefix", optStrJson n.prefix)
    , ("localName", Json.str n.localName)
    , ("tagName", optStrJson n.tagName) ]

def boundaryPointJson (bp : BoundaryPoint) : Json :=
  Json.mkObj [("node", natJson bp.node.id), ("offset", natJson bp.offset)]

def rangeJson (r : RangeState) : Json :=
  Json.mkObj [("start", boundaryPointJson r.start), ("end", boundaryPointJson r.«end»)]

def iteratorJson (it : IteratorState) : Json :=
  Json.mkObj
    [ ("root", natJson it.root.id)
    , ("reference", natJson it.reference.id)
    , ("pointerBeforeReference", Json.bool it.pointerBeforeReference)
    , ("whatToShow", natJson it.whatToShow) ]

def walkerJson (w : WalkerState) : Json :=
  Json.mkObj
    [ ("root", natJson w.root.id)
    , ("current", natJson w.current.id)
    , ("whatToShow", natJson w.whatToShow) ]

def invocationJson (v : Invocation) : Json :=
  Json.mkObj
    [ ("callback", natJson v.callback)
    , ("currentTarget", natJson v.currentTarget.id)
    , ("eventPhase", natJson v.eventPhase) ]

def recordTypeName : RecordType → String
  | .attributes => "attributes"
  | .childList => "childList"
  | .characterData => "characterData"

def recordJson (r : MutationRecord) : Json :=
  Json.mkObj
    [ ("type", Json.str (recordTypeName r.type))
    , ("target", natJson r.target.id)
    , ("addedNodes", Json.arr (r.addedNodes.map fun n => natJson n.id).toArray)
    , ("removedNodes", Json.arr (r.removedNodes.map fun n => natJson n.id).toArray)
    , ("previousSibling", optNatJson r.previousSibling)
    , ("nextSibling", optNatJson r.nextSibling)
    , ("attributeName", optStrJson r.attributeName)
    , ("attributeNamespace", optStrJson r.attributeNamespace)
    , ("oldValue", optStrJson r.oldValue) ]

/--
戻り値の外部表現。

`kind` を添えるのは、`undefined` と `null` を返す操作を取り違えないためである
（`removeChild` が null を返したら不一致、`remove()` が undefined を返すのは正しい）。
-/
def returnValueJson : ReturnValue → Json
  | .unit => Json.mkObj [("kind", Json.str "undefined")]
  | .node n => Json.mkObj [("kind", Json.str "node"), ("node", optNatJson n)]
  | .bool b => Json.mkObj [("kind", Json.str "boolean"), ("value", Json.bool b)]
  | .records rs =>
    Json.mkObj [("kind", Json.str "records"),
                ("records", Json.arr (rs.map recordJson).toArray)]
  | .int i => Json.mkObj [("kind", Json.str "number"), ("value", Json.num (.fromInt i))]
  | .str s =>
    Json.mkObj [("kind", Json.str "string"),
                ("value", match s with | none => Json.null | some x => Json.str x)]
  | .strs l =>
    Json.mkObj [("kind", Json.str "strings"),
                ("value", Json.arr (l.map Json.str).toArray)]
  | .attr a =>
    Json.mkObj [("kind", Json.str "attr"),
                ("attr", match a with | none => Json.null | some x => natJson x.id)]
  | .nodes l =>
    Json.mkObj [("kind", Json.str "nodes"),
                ("nodes", Json.arr (l.map (fun n => natJson n.id)).toArray)]

/--
`Observation` の外部表現。

`result` は `ok` / `exception` として並べる。
JSON は `Observation` の serialize であり、
比較の意味は「同じ `Observation` に落ちること」である。
-/
def observationFields (o : Observation) : List (String × Json) :=
  let resultFields : List (String × Json) :=
    match o.result with
    | .ok => [("ok", Json.bool true)]
    | .failed e => [("ok", Json.bool false), ("exception", Json.str e.name)]
  -- 失敗した操作に戻り値は無いので、その step では field ごと出さない。
  let returnedFields : List (String × Json) :=
    match o.result with
    | .ok => [("returned", returnValueJson o.returned)]
    | .failed _ => []
  resultFields ++ returnedFields ++
    [ ("nodes", Json.arr (o.nodes.map observedNodeJson).toArray)
    , ("ranges", Json.arr (o.ranges.map rangeJson).toArray)
    , ("iterators", Json.arr (o.iterators.map iteratorJson).toArray)
    , ("walkers", Json.arr (o.walkers.map walkerJson).toArray)
    , ("observers", Json.arr
        (o.records.map fun rs => Json.arr (rs.map recordJson).toArray).toArray)
    , ("invocations", Json.arr (o.invocations.map invocationJson).toArray)
    , ("detachedAttrs", Json.arr (o.detachedAttrs.map attrJson).toArray)
    , ("delivered", Json.arr (o.delivered.map fun p =>
        Json.mkObj [("observer", natJson p.1),
                    ("records", Json.arr (p.2.map recordJson).toArray)]).toArray) ]

def observationJson (o : Observation) : Json :=
  Json.mkObj (observationFields o)

/-- 初期状態の観測。まだ操作していないので `ok` / `exception` は出さない。 -/
def stateJson (s : DOMState) : Json :=
  Json.mkObj ((observationFields (observe s .ok)).filter fun p =>
    p.1 ≠ "ok" && p.1 ≠ "returned")

def stepJson : StepResult → Json
  | .ok s delivered returned invoked =>
    observationJson (observe s .ok delivered returned invoked)
  | .failed before e => observationJson (observe before (.failed e))

end Dom.Exec
