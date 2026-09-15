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

仕様の node document は持たない。model の attribute は node tree に入らないので、
その node document は観測できない。
-/
structure Attr where
  id : AttrId
  «namespace» : Option String := none
  «prefix» : Option String := none
  localName : String
  value : String := ""
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
「id 以外は同じ」を言うのにこれを使う。
-/
def anon (a : Attr) : Attr := { a with id := ⟨0⟩ }

@[simp] theorem anon_key (a : Attr) : a.anon.key = a.key := rfl

end Attr

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
deriving DecidableEq, Repr, Inhabited

namespace NodeData

/--
木の surgery が触らない部分。

`detach` / `insertAt` / `setOwnerDocument` / `withData` はどれも
parent・children・node document・data しか変えないので、それを落とした残りは保たれる。
`ShapePreserving`（`Dom/Properties/Algorithms.lean`）がこの保存を表す。

落とす側を並べてあるので、`NodeData` に field が増えても自動的に保存の対象に入る。
-/
def shape (d : NodeData) : NodeData :=
  { d with parent := none, children := [], ownerDocument := ⟨0⟩, data := "" }

@[simp] theorem shape_kind (d : NodeData) : d.shape.kind = d.kind := rfl

@[simp] theorem shape_attributes (d : NodeData) : d.shape.attributes = d.attributes := rfl

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
