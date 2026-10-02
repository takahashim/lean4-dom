import Dom.Attribute.Algorithms
import Dom.Query.Lookup
import Dom.Selector.Api

/-!
# reflect・`DOMTokenList`・`HTMLCollection.namedItem`

attribute を **namespace が null で、その local name を持つもの**として読み書きする API。

| 仕様 | 定義 |
| --- | --- |
| DOM §4.9 `Element.id` / `className` / `slot`、HTML の `title` / `lang` / `accessKey` / `inert` / `autofocus`（reflect） | `reflectSpec`, `getReflectedProp`, `setReflectedProp`, `setReflectedBool` |
| HTML §3.2.6.8 `dataset`（`DOMStringMap`） | `datasetPairs`, `datasetGet`, `datasetSet`, `datasetDelete`, `datasetKeys` |
| DOM §7.1 `DOMTokenList`（`Element.classList`） | `classListAdd` ほか |
| DOM §4.2.10.1 `HTMLCollection.namedItem(key)`（`ParentNode.children`） | `childrenNamedItem` |

reflect の getter は "get an attribute value"（namespace は null）、setter は
"set an attribute value"（namespace も prefix も null）である。qualified name で引く
`getAttribute` / `setAttribute` とは違い、`setAttributeNS("urn:x", "id", …)` で置いた
attribute は見ない・書かない（`Dom/Properties/NullNamespace.lean`）。

`DOMTokenList` の token set は、associated attribute の値を ordered set parser で読んだもの
（"attribute change steps" が保つもの）である。model は attribute の値から毎回読み直す。
-/

namespace Dom

/-- 受け手が Element であること（WebIDL）。 -/
def requireElementData (t : Tree) (element : NodeId) : Except DOMException NodeData :=
  match t.get? element with
  | none => .error .notFoundError
  | some d => if d.kind != .element then .error .typeError else .ok d

/--
DOMString の reflect の getter。"get an attribute value"（namespace は null）。
受け手の interface は見ない（`getReflectedProp` が見る）。`Dom/Properties/NullNamespace.lean` の
frame 定理はこの形で述べ、`getReflectedProp` の DOMString の枝はこれと同じ値を返す。
-/
def getReflected (t : Tree) (element : NodeId) (localName : String) :
    Except DOMException String :=
  (requireElementData t element).map fun d => getAttributeValue d none localName

/-! ## HTML の reflect（string と boolean） -/

/-- Infra の SVG namespace。 -/
def svgNamespace : String := "http://www.w3.org/2000/svg"

/-- reflect の種類。DOMString か boolean か。 -/
inductive ReflectKind where
  | string
  | boolean
deriving DecidableEq, Repr

/-- IDL attribute を持つ interface。 -/
inductive ReflectIface where
  /-- `Element`（どの namespace の element も持つ）。 -/
  | element
  /-- `HTMLElement`（HTML namespace の element）。 -/
  | html
  /-- `HTMLOrSVGElement` mixin（HTML namespace と SVG namespace の element）。 -/
  | htmlOrSvg
deriving DecidableEq, Repr

/-- reflect する IDL attribute の一つ。 -/
structure ReflectSpec where
  attr : String
  kind : ReflectKind
  iface : ReflectIface
deriving DecidableEq, Repr

/--
model が持つ reflect の表。値の解釈（enumerated・URL・数値）を伴わないものだけを置く。

* DOM §4.9：`id` / `className` / `slot`
* HTML §3.2.6：`title` / `lang` / `accessKey`（DOMString）、`inert`（boolean）
* HTML §6.6.3 / §3.2.3：`autofocus`（boolean、`HTMLOrSVGElement`）
-/
def reflectSpec : String → Option ReflectSpec
  | "id" => some ⟨"id", .string, .element⟩
  | "className" => some ⟨"class", .string, .element⟩
  | "slot" => some ⟨"slot", .string, .element⟩
  | "title" => some ⟨"title", .string, .html⟩
  | "lang" => some ⟨"lang", .string, .html⟩
  | "accessKey" => some ⟨"accesskey", .string, .html⟩
  | "inert" => some ⟨"inert", .boolean, .html⟩
  | "autofocus" => some ⟨"autofocus", .boolean, .htmlOrSvg⟩
  | _ => none

/-- element がその interface を持つか。 -/
def ReflectIface.applies (d : NodeData) : ReflectIface → Bool
  | .element => true
  | .html => d.namespace == some htmlNamespace
  | .htmlOrSvg => d.namespace == some htmlNamespace || d.namespace == some svgNamespace

/-- 受け手が Element で、その IDL attribute を持つこと。持たなければ WebIDL の TypeError とする。 -/
def requireReflectTarget (t : Tree) (element : NodeId) (r : ReflectSpec) :
    Except DOMException NodeData := do
  let d ← requireElementData t element
  if r.iface.applies d then return d else throw .typeError

/--
reflect の getter。DOMString は "get an attribute value"、boolean は
"get an attribute by namespace and local name" が null でないこと（どちらも namespace は null）。
-/
def getReflectedProp (t : Tree) (element : NodeId) (r : ReflectSpec) :
    Except DOMException (String ⊕ Bool) :=
  (requireReflectTarget t element r).map fun d =>
    match r.kind with
    | .string => .inl (getAttributeValue d none r.attr)
    | .boolean => .inr (getAttributeByKey d none r.attr).isSome

/-- DOMString の reflect の setter。"set an attribute value"（namespace も prefix も null）。 -/
def setReflectedProp (s : DOMState) (element : NodeId) (r : ReflectSpec) (value : String) :
    Except DOMException DOMState := do
  let _ ← requireReflectTarget s.tree element r
  setAttributeValue s element r.attr value

/--
boolean の reflect の setter。true なら空文字列で "set an attribute value"、false なら
"remove an attribute by namespace and local name"（namespace は null）。
-/
def setReflectedBool (s : DOMState) (element : NodeId) (r : ReflectSpec) (b : Bool) :
    Except DOMException DOMState := do
  let _ ← requireReflectTarget s.tree element r
  if b then setAttributeValue s element r.attr "" else removeAttributeNS s element none r.attr

/-! ## `dataset`（HTML §3.2.6.8 `DOMStringMap`） -/

def isAsciiUpperAlpha (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isAsciiLowerAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- "get the name-value pairs" step 3。`-` の後の ASCII lower alpha を大文字にして `-` を落とす。 -/
def datasetCamel : List Char → List Char
  | '-' :: tl@(c :: rest) =>
    if isAsciiLowerAlpha c then c.toUpper :: datasetCamel rest else '-' :: datasetCamel tl
  | c :: rest => c :: datasetCamel rest
  | [] => []

/--
"get the name-value pairs"。

**namespace を見ない。** 本文は「名前（qualified name）が `data-` で始まり、残りに ASCII upper alpha
を含まない content attribute」と言うので、prefix の無い namespace 付きの `data-x` も入る。
prefix 付きのもの（`p:data-x`）は名前が `data-` で始まらないので入らない。
-/
def datasetPairs (d : NodeData) : List (String × String) :=
  d.attributes.filterMap fun a =>
    let qn := a.qualifiedName.toList
    if qn.take 5 == "data-".toList && !(qn.drop 5).any isAsciiUpperAlpha then
      some (String.ofList (datasetCamel (qn.drop 5)), a.value)
    else none

/-- 名前付き property の値（最初に当たる組）。 -/
def datasetGet (t : Tree) (element : NodeId) (name : String) : Except DOMException (Option String) :=
  (requireReflectTarget t element ⟨"", .string, .htmlOrSvg⟩).map fun d =>
    ((datasetPairs d).find? (·.1 == name)).map (·.2)

/-- supported property names。重複は一つにする（WebIDL の property 名は集合である）。 -/
def datasetKeys (t : Tree) (element : NodeId) : Except DOMException (List String) :=
  (requireReflectTarget t element ⟨"", .string, .htmlOrSvg⟩).map fun d =>
    ((datasetPairs d).map (·.1)).eraseDups

/-- 名前の変換（setter step 2-3 と deleter step 1-2）。ASCII upper alpha の前に `-` を入れて小文字にする。 -/
def datasetAttrName (name : String) : String :=
  "data-" ++ String.ofList (name.toList.flatMap fun c =>
    if isAsciiUpperAlpha c then ['-', c.toLower] else [c])

/-- `-` の後に ASCII lower alpha が来るか（setter step 1）。 -/
def hasDashLower : List Char → Bool
  | '-' :: tl@(c :: _) => isAsciiLowerAlpha c || hasDashLower tl
  | _ :: rest => hasDashLower rest
  | [] => false

/-- named property の setter。最後は "set an attribute value"（namespace も prefix も null）。 -/
def datasetSet (s : DOMState) (element : NodeId) (name value : String) :
    Except DOMException DOMState := do
  let _ ← requireReflectTarget s.tree element ⟨"", .string, .htmlOrSvg⟩
  -- step 1
  if hasDashLower name.toList then throw .syntaxError
  -- step 2-3
  let qn := datasetAttrName name
  -- step 4
  if !isValidAttributeLocalName qn then throw .invalidCharacterError
  -- step 5
  setAttributeValue s element qn value

/--
named property の deleter。**"remove an attribute by name"**（qualified name で引く）なので、
prefix の無い namespace 付きの `data-x` が先にあればそちらを消す。
-/
def datasetDelete (s : DOMState) (element : NodeId) (name : String) :
    Except DOMException DOMState := do
  let d ← requireReflectTarget s.tree element ⟨"", .string, .htmlOrSvg⟩
  -- WebIDL は supported property name にだけ deleter を呼ぶ。それ以外の `delete` は何もしない。
  if !(datasetPairs d).any (·.1 == name) then return s
  removeAttribute s element (datasetAttrName name)

/-! ## `DOMTokenList`（associated attribute は `class`） -/

/-- token set。associated attribute の値を ordered set parser で読んだもの。 -/
def classTokenSet (d : NodeData) : List String :=
  orderedSetParse (getAttributeValue d none "class")

/-- `add` / `remove` / `toggle` の token の検査（DOM §7.1 の各 method の step 1）。 -/
def validateToken (token : String) : Option DOMException :=
  if token.isEmpty then some .syntaxError
  else if token.toList.any isAsciiWhitespace then some .invalidCharacterError
  else none

/-- 先頭から検査して、最初の失敗を返す。 -/
def validateTokens : List String → Option DOMException
  | [] => none
  | t :: ts => (validateToken t).orElse fun _ => validateTokens ts

/--
DOM §7.1 の "update steps"。

1. associated attribute が無く token set が空なら何もしない。
2. そうでなければ、ordered set serializer の結果で "set an attribute value" する。
-/
def tokenListUpdate (s : DOMState) (element : NodeId) (d : NodeData) (set : List String) :
    Except DOMException DOMState :=
  if (getAttributeByKey d none "class").isNone && set.isEmpty then .ok s
  else setAttributeValue s element "class" (" ".intercalate set)

/-- ordered set への append（既にあれば何もしない）。 -/
def orderedSetAppend (set : List String) (token : String) : List String :=
  if set.contains token then set else set ++ [token]

/--
Infra の ordered set の "replace"。`item` か `replacement` の最初の出現を `replacement` にし、
それ以外の出現を取り除く。
-/
def orderedSetReplace (item replacement : String) : List String → List String
  | [] => []
  | x :: xs =>
    if x == item || x == replacement then
      replacement :: xs.filter fun y => y != item && y != replacement
    else x :: orderedSetReplace item replacement xs

/-- DOM §7.1 `add(tokens...)`。 -/
def classListAdd (s : DOMState) (element : NodeId) (tokens : List String) :
    Except DOMException DOMState := do
  let d ← requireElementData s.tree element
  -- step 1
  if let some e := validateTokens tokens then throw e
  -- step 2-3
  tokenListUpdate s element d (tokens.foldl orderedSetAppend (classTokenSet d))

/-- DOM §7.1 `remove(tokens...)`。 -/
def classListRemove (s : DOMState) (element : NodeId) (tokens : List String) :
    Except DOMException DOMState := do
  let d ← requireElementData s.tree element
  if let some e := validateTokens tokens then throw e
  tokenListUpdate s element d ((classTokenSet d).filter fun x => !tokens.contains x)

/-- DOM §7.1 `toggle(token, force)`。返り値の `Bool` は token が結果として含まれるか。 -/
def classListToggle (s : DOMState) (element : NodeId) (token : String) (force : Option Bool) :
    Except DOMException (DOMState × Bool) := do
  let d ← requireElementData s.tree element
  -- step 1
  if let some e := validateToken token then throw e
  let set := classTokenSet d
  -- step 2
  if set.contains token then
    if force == some true then return (s, true)
    else return (← tokenListUpdate s element d (set.filter (· != token)), false)
  -- step 3
  else if force != some false then
    return (← tokenListUpdate s element d (set ++ [token]), true)
  -- step 4
  else return (s, false)

/-- DOM §7.1 `replace(token, newToken)`。返り値の `Bool` は置き換えたか。 -/
def classListReplace (s : DOMState) (element : NodeId) (token newToken : String) :
    Except DOMException (DOMState × Bool) := do
  let d ← requireElementData s.tree element
  -- step 1-2。空文字列の検査を両方済ませてから空白の検査をする。
  if token.isEmpty || newToken.isEmpty then throw .syntaxError
  if token.toList.any isAsciiWhitespace || newToken.toList.any isAsciiWhitespace then
    throw .invalidCharacterError
  let set := classTokenSet d
  -- step 3
  if !set.contains token then return (s, false)
  -- step 4-6
  return (← tokenListUpdate s element d (orderedSetReplace token newToken set), true)

/-- DOM §7.1 `contains(token)`。token の検査はしない。 -/
def classListContains (t : Tree) (element : NodeId) (token : String) : Except DOMException Bool :=
  (requireElementData t element).map fun d => (classTokenSet d).contains token

/-! ## `HTMLCollection.namedItem(key)` -/

/--
DOM §4.2.10.1 `namedItem(key)` を `ParentNode.children` に対して呼んだもの。
受け手の検査は `querySelector` と同じ `requireParentNode`（`Dom/Selector/Api.lean`）。

1. key が空文字列なら null。
2. collection のうち、ID が key か、HTML namespace にあって `name` attribute
   （namespace は null）の値が key である最初の element。
-/
def childrenNamedItem (t : Tree) (node : NodeId) (key : String) :
    Except DOMException (Option NodeId) :=
  (requireParentNode t node).map fun _ =>
    if key.isEmpty then none
    else (elementChildrenOf t node).find? fun e =>
      elementIdOf t e == some key ||
        match t.get? e with
        | none => false
        | some d => d.namespace == some htmlNamespace && plainAttr d "name" == some key

end Dom
