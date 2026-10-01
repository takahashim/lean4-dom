import Dom.Basic.Utf16

/-!
# Node の識別子と node data

DOM Standard §4.4 Interface `Node` に対応する状態のうち、
本 model が扱う部分だけを抜き出す。

node は Ruby / JavaScript の object reference ではなく、安定した識別子 `NodeId` で扱う。
これにより tree の状態は `NodeId` から `NodeData` への finite map として表現できる。
-/

namespace Dom

/-- Node の識別子。model の内部でのみ意味を持ち、仕様上の概念には対応しない。 -/
structure NodeId where
  id : Nat
deriving DecidableEq, Hashable, Inhabited

/-- oracle の出力を読みやすくするため、`NodeId` は識別子の数値だけを表示する。 -/
instance : Repr NodeId := ⟨fun n _ => repr n.id⟩

instance : ToString NodeId := ⟨fun n => toString n.id⟩

/--
DOM Standard §4.4 の node type に対応する。

仕様の `nodeType` は数値定数だが、model では分岐を網羅的に書けるよう inductive とする。
`attribute` は本 model の対象外である（`memo.md` の範囲に従い node tree のみを扱う）。
-/
inductive NodeKind where
  | document
  | documentType
  | documentFragment
  | element
  | text
  | cdataSection
  | processingInstruction
  | comment
deriving DecidableEq, Repr, Inhabited

namespace NodeKind

/-- DOM Standard §4.10 `CharacterData` を継承する node か。 -/
def isCharacterData : NodeKind → Bool
  | .text | .cdataSection | .processingInstruction | .comment => true
  | _ => false

/--
DOM Standard §4.2.3 pre-insertion validity で「element または CharacterData」として
扱われる種別か。`Document` の子に許されない種別の判定に使う。
-/
def isElementOrCharacterData (k : NodeKind) : Bool :=
  k == .element || k.isCharacterData

/--
仕様の `Text` を継承する種別か。

`CDATASection` の IDL は `interface CDATASection : Text` なので、
CDATASection node は Text node でもある。
「Document の子に Text は置けない」という制約はこちらで判定する。
-/
def isText : NodeKind → Bool
  | .text | .cdataSection => true
  | _ => false

/--
DOM Standard §4.4 の `nodeType` の数値。

`NodeFilter` の `whatToShow` はこの値から 1 を引いた bit を見る。
attribute (2) と、歴史的な entity reference (5) / entity (6) / notation (12) は
`NodeKind` に無いので現れない。
-/
def nodeType : NodeKind → Nat
  | .element => 1
  | .text => 3
  | .cdataSection => 4
  | .processingInstruction => 7
  | .comment => 8
  | .document => 9
  | .documentType => 10
  | .documentFragment => 11

/--
children を持てる種別か。

DOM Standard §4.2.3 "ensure pre-insertion validity" step 1 が parent に許す
Document / DocumentFragment / Element の三つである。
それ以外は仕様上 leaf であり、children は常に空でなければならない。
-/
def canHaveChildren : NodeKind → Bool
  | .document | .documentFragment | .element => true
  | _ => false

end NodeKind

/--
Attr の識別子。`NodeId` とは別の空間である。

仕様の `Attr` は `Node` だが、本 model の node tree は element や text だけを載せる
（`NodeKind` に attribute が無い）。attribute は element の状態として持ったまま、
**同一性だけ**を id で表す。`getAttributeNode` が同じ attribute に同じものを返すこと、
`setAttributeNode` が copy を作らないことが、これで観測できるようになる。
-/
structure AttrId where
  id : Nat
deriving DecidableEq, Hashable, Inhabited

/-- oracle の出力を読みやすくするため、`AttrId` は識別子の数値だけを表示する。 -/
instance : Repr AttrId := ⟨fun n _ => repr n.id⟩

instance : ToString AttrId := ⟨fun n => toString n.id⟩

/--
DOM Standard §4.9 の attribute。

attribute は仕様上 node（`Attr`）だが、本 model では element の状態として持つ。
node tree に入らない（parent を持てず tree order にも現れない）ので、
`NodeId` を振っても `Tree` の不変条件に絡まないためである。
同一性だけは `AttrId` で表す。

* `id` — 同一性。仕様の `Attr` node にあたる。
* `namespace?` — 仕様の namespace。null は `none`。
* `prefix?` — 仕様の namespace prefix。qualified name の計算にだけ使う。
* `localName` — 仕様の local name。mutation record の `attributeName` はこれである。
* `value` — 仕様の value。
* `ownerDocument` — 仕様の node document（`Attr` も node なので持つ）。"create an attribute" は
  受け手の document、"append an attribute" と "replace an attribute" は element の node document、
  adopt は element の attribute ごとと、`Attr` を直に渡されたときに書き換える。
  element に付いている間も element の node document と一致するとは限らない
  （`adoptNode(attr)` は element から外さずに node document だけを変える）。
-/
structure Attr where
  id : AttrId
  «namespace» : Option String := none
  «prefix» : Option String := none
  localName : String
  value : String := ""
  ownerDocument : NodeId
deriving DecidableEq, Repr, Inhabited

namespace Attr

/-- DOM Standard §1.4 の qualified name。prefix があれば `prefix:localName`。 -/
def qualifiedName (a : Attr) : String :=
  match a.prefix with
  | none => a.localName
  | some p => p ++ ":" ++ a.localName

/-- 仕様が attribute を同定する鍵、すなわち namespace と local name の組。 -/
def key (a : Attr) : Option String × String := (a.namespace, a.localName)

/--
同一性を落とした attribute。

clone は attribute を写すが、copy の `Attr` は原本とは別のものである（仕様の
"clone a single node" step 2.1 が attribute ごとに clone を作る）。
「id と node document 以外は同じ」を言うのにこれを使う（import した copy は node document も違う）。
-/
def anon (a : Attr) : Attr := { a with id := ⟨0⟩, ownerDocument := ⟨0⟩ }

@[simp] theorem anon_key (a : Attr) : a.anon.key = a.key := rfl

/-- node document だけを付け替えた attribute。adopt が element の attribute ごとに行う。 -/
def withOwnerDocument (a : Attr) (doc : NodeId) : Attr := { a with ownerDocument := doc }

/-- node document を落とした attribute。木の surgery が保つのはこの部分である。 -/
def dropDoc (a : Attr) : Attr := a.withOwnerDocument ⟨0⟩

@[simp] theorem withOwnerDocument_id (a : Attr) (doc : NodeId) : (a.withOwnerDocument doc).id = a.id := rfl
@[simp] theorem withOwnerDocument_key (a : Attr) (doc : NodeId) : (a.withOwnerDocument doc).key = a.key := rfl
@[simp] theorem withOwnerDocument_localName (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).localName = a.localName := rfl
@[simp] theorem withOwnerDocument_namespace (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).namespace = a.namespace := rfl
@[simp] theorem withOwnerDocument_prefix (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).prefix = a.prefix := rfl
@[simp] theorem withOwnerDocument_value (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).value = a.value := rfl
@[simp] theorem withOwnerDocument_ownerDocument (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).ownerDocument = doc := rfl
@[simp] theorem withOwnerDocument_anon (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).anon = a.anon := rfl
@[simp] theorem withOwnerDocument_dropDoc (a : Attr) (doc : NodeId) :
    (a.withOwnerDocument doc).dropDoc = a.dropDoc := rfl
@[simp] theorem dropDoc_key (a : Attr) : a.dropDoc.key = a.key := rfl
@[simp] theorem dropDoc_id (a : Attr) : a.dropDoc.id = a.id := rfl
@[simp] theorem dropDoc_value (a : Attr) : a.dropDoc.value = a.value := rfl
@[simp] theorem dropDoc_localName (a : Attr) : a.dropDoc.localName = a.localName := rfl
@[simp] theorem dropDoc_namespace (a : Attr) : a.dropDoc.namespace = a.namespace := rfl
@[simp] theorem dropDoc_prefix (a : Attr) : a.dropDoc.prefix = a.prefix := rfl
@[simp] theorem dropDoc_anon (a : Attr) : a.dropDoc.anon = a.anon := rfl

end Attr

/--
DOM §4.5 の document の mode。HTML parser が doctype から決め、それ以外の document は
no-quirks で生まれる。一度決まれば doctype を変えても変わらない。clone は元の mode を写す。
-/
inductive DocumentMode where
  | noQuirks
  | quirks
  | limitedQuirks
deriving DecidableEq, Repr, Inhabited

/--
一つの node が持つ状態。

* `kind` — 仕様の node type。Phase 1 と 2 では参照しないが、Phase 3 の
  pre-insertion validity が kind による分岐で占められるため最初から持たせる（PLAN §3.1）。
* `parent` — 仕様の parent。`Option` なので parent の一意性は構造上保証される。
* `children` — 仕様の children。順序に意味があるので `List` で持つ。
* `ownerDocument` — 仕様の node document。Phase 3 の adopt で必要になる。
* `data` — 仕様 §4.10 `CharacterData` の data。CharacterData 以外では空文字列とする。
* `attributes` — 仕様 §4.9 の attribute list。Element 以外では空とする。
  順序に意味がある（`getAttributeNames` と qualified name による探索が list 順）ので `List` で持つ。
* `namespace` / `prefix` / `localName` — 仕様 §4.8 Element の namespace・namespace prefix・
  local name。Element 以外では `none` / `none` / `""` とする。
* `isHTMLDocument` — 仕様 §4.5 Document の type が "html" であること。
  Document 以外では `false` とする。
  attribute 名を ASCII lowercase するかどうかがこれと element の namespace で決まる
  （"get an attribute by name" step 1、`setAttribute` step 2）。
* `mode` — 仕様 §4.5 Document の mode。Document 以外では `noQuirks` とする。
  quirks mode の document では class と id の比較が ASCII case-insensitive になる
  （HTML §"Case-sensitivity of selectors"、DOM "list of elements with class names"）。
-/
structure NodeData where
  kind : NodeKind
  parent : Option NodeId := none
  children : List NodeId := []
  ownerDocument : NodeId
  data : String := ""
  attributes : List Attr := []
  «namespace» : Option String := none
  «prefix» : Option String := none
  localName : String := ""
  isHTMLDocument : Bool := false
  mode : DocumentMode := .noQuirks
deriving DecidableEq, Repr, Inhabited

namespace NodeData

/--
木の surgery が触らない部分。

`detach` / `insertAt` / `setOwnerDocument` / `withData` はどれも
parent・children・node document（element の attribute の node document を含む）・data しか
変えないので、それを落とした残りは保たれる。
`ShapePreserving`（`Dom/Properties/Algorithms.lean`）がこの保存を表す。

落とす側を並べてあるので、`NodeData` に field が増えても自動的に保存の対象に入る。
-/
def shape (d : NodeData) : NodeData :=
  { d with parent := none, children := [], ownerDocument := ⟨0⟩, data := "",
           attributes := d.attributes.map Attr.dropDoc }

@[simp] theorem shape_kind (d : NodeData) : d.shape.kind = d.kind := rfl

@[simp] theorem shape_attributes (d : NodeData) :
    d.shape.attributes = d.attributes.map Attr.dropDoc := rfl

/--
DOM §4.5 adopt step 3 が一つの node に行うこと。node document を `doc` にし、
element なら attribute list の各 attribute の node document も `doc` にする。
-/
def withOwnerDocument (d : NodeData) (doc : NodeId) : NodeData :=
  { d with ownerDocument := doc, attributes := d.attributes.map (·.withOwnerDocument doc) }

@[simp] theorem withOwnerDocument_ownerDocument (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).ownerDocument = doc := rfl
@[simp] theorem withOwnerDocument_kind (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).kind = d.kind := rfl
@[simp] theorem withOwnerDocument_parent (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).parent = d.parent := rfl
@[simp] theorem withOwnerDocument_children (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).children = d.children := rfl
@[simp] theorem withOwnerDocument_data (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).data = d.data := rfl
@[simp] theorem withOwnerDocument_attributes (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).attributes = d.attributes.map (·.withOwnerDocument doc) := rfl
@[simp] theorem withOwnerDocument_namespace (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).namespace = d.namespace := rfl
@[simp] theorem withOwnerDocument_prefix (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).prefix = d.prefix := rfl
@[simp] theorem withOwnerDocument_localName (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).localName = d.localName := rfl
@[simp] theorem withOwnerDocument_isHTMLDocument (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).isHTMLDocument = d.isHTMLDocument := rfl
@[simp] theorem withOwnerDocument_mode (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).mode = d.mode := rfl
@[simp] theorem withOwnerDocument_shape (d : NodeData) (doc : NodeId) :
    (d.withOwnerDocument doc).shape = d.shape := by
  simp [shape, withOwnerDocument, List.map_map, Function.comp_def]

/-- `shape` から attribute の同一性も落としたもの。clone の「同じ形」はこれで見る。 -/
def shapeAnon (d : NodeData) : NodeData :=
  { d.shape with attributes := d.shape.attributes.map Attr.anon }

@[simp] theorem shapeAnon_kind (d : NodeData) : d.shapeAnon.kind = d.kind := rfl

/-- `shape` が等しければ `shapeAnon` も等しい。`shapeAnon` は `shape` だけで決まる。 -/
theorem shapeAnon_congr {d e : NodeData} (h : d.shape = e.shape) : d.shapeAnon = e.shapeAnon := by
  unfold shapeAnon
  rw [h]

/--
DOM Standard §1.4 の qualified name。prefix があれば `prefix:localName`。

Element の `tagName` はこれを、HTML namespace の element が HTML document にあるときは
ASCII uppercase したものである。
-/
def qualifiedName (d : NodeData) : String :=
  match d.prefix with
  | none => d.localName
  | some p => p ++ ":" ++ d.localName

/--
DOM Standard §4.4 の node length。

CharacterData なら data の長さ、DocumentType なら 0、それ以外は children の個数。
Phase 5 の boundary point validity で使うが、定義は node data だけで決まるためここに置く。

data の長さは仕様どおり **UTF-16 の code unit 数** である（`Dom.Utf16.length`）。
-/
def length (d : NodeData) : Nat :=
  if d.kind.isCharacterData then Dom.Utf16.length d.data
  else if d.kind == .documentType then 0
  else d.children.length

end NodeData

end Dom
