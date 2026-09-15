import Dom.Mutation.Create
import Dom.Mutation.Algorithms

/-!
# node を複製する（§4.4 `cloneNode`）

`Dom/Mutation/Create.lean` が「node を一つ作る」だったのに対し、ここは
「既にある node と同じ形の node を作る」である。

**identity と structural equivalence の違い**がここで形になる。copy は
原本と同じ kind・data・attribute・名前を持つが、`NodeId` は別である。
「同じ形である」は `Dom/Properties/Clone.lean` の `CloneOf` が述べ、
「別のものである」は copy が `freshId` であることから出る。

## 仕様の手順をそのまま呼ぶ

"clone a node" の step 4 は「parent が null でなければ copy を parent に
**append** する」で、step 5 の children の clone はそのあとである。
だから model も自前で木を触らず、§4.2.3 の `append` を呼ぶ。
妥当性の保存も live range の調整も mutation record も、
そちらで既に証明したものがそのまま効く。

step 5 が children に渡す `document` は **copy ではなく引数の document のまま**である。
Document を clone したときに children の copy の node document が copy になるのは、
`append` の中の adopt が付け替えるからである。ここでもその経路をそのまま使う。

`cloneSingle`（"clone a single node"）だけは copy 自身の node document を決める。
Document の copy は自分自身を node document とするので、そこは `cloneDocumentOf` が見る。

fuel が尽きた場合は `outsideModel` を返す。`cloneNode` は `Tree.size + 1` を渡す。
children と兄弟のどちらにも同じ fuel を渡すので、必要な fuel は clone する node の数を
超えず、木の node 数で足りる。

shadow root（step 6）と custom element（"clone a single node" の step 2.1-2.3）は
model の対象外である。
-/

namespace Dom

/-- copy の node data。parent・children・node document 以外はそのまま写す。 -/
def cloneData (d : NodeData) (doc : NodeId) : NodeData :=
  { d with parent := none, children := [], ownerDocument := doc }

@[simp] theorem cloneData_shape (d : NodeData) (doc : NodeId) :
    (cloneData d doc).shape = d.shape := rfl

@[simp] theorem cloneData_data (d : NodeData) (doc : NodeId) :
    (cloneData d doc).data = d.data := rfl

@[simp] theorem cloneData_kind (d : NodeData) (doc : NodeId) :
    (cloneData d doc).kind = d.kind := rfl

@[simp] theorem cloneData_attributes (d : NodeData) (doc : NodeId) :
    (cloneData d doc).attributes = d.attributes := rfl

@[simp] theorem cloneData_children (d : NodeData) (doc : NodeId) :
    (cloneData d doc).children = [] := rfl

@[simp] theorem cloneData_parent (d : NodeData) (doc : NodeId) :
    (cloneData d doc).parent = none := rfl

@[simp] theorem cloneData_ownerDocument (d : NodeData) (doc : NodeId) :
    (cloneData d doc).ownerDocument = doc := rfl

/--
copy の node document。

Document の copy は自分自身を node document とする。それ以外の copy は
引数の document に属する。
-/
def cloneDocumentOf (d : NodeData) (doc copy : NodeId) : NodeId :=
  if d.kind == .document then copy else doc

/-- §4.4 "clone a single node"。children も parent も持たない copy を一つ作る。 -/
def cloneSingle (s : DOMState) (d : NodeData) (doc : NodeId) : NodeId × DOMState :=
  withFresh s (cloneData d (cloneDocumentOf d doc (freshId s.tree)))

/-- "clone a node" の step 4。parent が null でなければ copy をそこに append する。 -/
def cloneAppend (s : DOMState) (copy : NodeId) (parent : Option NodeId) :
    Except DOMException DOMState :=
  match parent with
  | none => .ok s
  | some p => append s copy p

/--
"clone a node" を node の列に対して順に行う。

`cloneNode` は `[n]` と parent = null で呼ぶ。step 5 の再帰は
その node の children と parent = copy で呼ぶ。
-/
def cloneMany : Nat → DOMState → List NodeId → NodeId → Option NodeId →
    Except DOMException (List NodeId × DOMState)
  | _, s, [], _, _ => .ok ([], s)
  | 0, _, _ :: _, _, _ => .error .outsideModel
  | fuel + 1, s, n :: rest, doc, parent =>
    match s.tree.get? n with
    | none => .error .notFoundError
    | some d =>
      -- step 2
      let (copy, s₁) := cloneSingle s d doc
      -- step 4
      match cloneAppend s₁ copy parent with
      | .error e => .error e
      | .ok s₂ =>
        -- step 5
        match cloneMany fuel s₂ d.children doc (some copy) with
        | .error e => .error e
        | .ok (_, s₃) =>
          match cloneMany fuel s₃ rest doc parent with
          | .error e => .error e
          | .ok (siblings, s₄) => .ok (copy :: siblings, s₄)

/--
§4.4 "clone a node" を、document を指定して parent = null で呼ぶ形。

`cloneNode` は node 自身の node document を、`importNode` は受け手の document を渡す。
parent が null なので、返る copy は detach されている。
-/
def cloneNodeIn (s : DOMState) (n : NodeId) (doc : NodeId) (subtree : Bool) :
    Except DOMException (NodeId × DOMState) :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d =>
    if subtree then
      match cloneMany (s.tree.size + 1) s [n] doc none with
      | .error e => .error e
      | .ok (c :: _, s') => .ok (c, s')
      -- 空の列は返らない。
      | .ok ([], _) => .error .outsideModel
    else .ok (cloneSingle s d doc)

/--
DOM Standard §4.4 `cloneNode(deep)`。

"clone a node" を this、document = this の node document、subtree = deep、
parent = null で呼ぶ。
-/
def cloneNode (s : DOMState) (n : NodeId) (deep : Bool) :
    Except DOMException (NodeId × DOMState) :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d => cloneNodeIn s n d.ownerDocument deep

theorem cloneNode_eq {s : DOMState} {n : NodeId} {d : NodeData} {deep : Bool}
    (hd : s.tree.get? n = some d) :
    cloneNode s n deep = cloneNodeIn s n d.ownerDocument deep := by
  unfold cloneNode
  rw [hd]

end Dom
