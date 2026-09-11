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
一つの node が持つ状態。

* `kind` — 仕様の node type。Phase 1 と 2 では参照しないが、Phase 3 の
  pre-insertion validity が kind による分岐で占められるため最初から持たせる（PLAN §3.1）。
* `parent` — 仕様の parent。`Option` なので parent の一意性は構造上保証される。
* `children` — 仕様の children。順序に意味があるので `List` で持つ。
* `ownerDocument` — 仕様の node document。Phase 3 の adopt で必要になる。
* `data` — 仕様 §4.10 `CharacterData` の data。CharacterData 以外では空文字列とする。
-/
structure NodeData where
  kind : NodeKind
  parent : Option NodeId := none
  children : List NodeId := []
  ownerDocument : NodeId
  data : String := ""
deriving DecidableEq, Repr, Inhabited

namespace NodeData

/--
DOM Standard §4.4 の node length。

CharacterData なら data の長さ、DocumentType なら 0、それ以外は children の個数。
Phase 5 の boundary point validity で使うが、定義は node data だけで決まるためここに置く。
-/
def length (d : NodeData) : Nat :=
  if d.kind.isCharacterData then d.data.length
  else if d.kind == .documentType then 0
  else d.children.length

end NodeData

end Dom
