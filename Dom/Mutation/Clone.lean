import Dom.Mutation.Create

/-!
# node を複製する（§4.4 `cloneNode`）

`Dom/Mutation/Create.lean` が「node を一つ作る」だったのに対し、ここは
「既にある node と同じ形の node を作る」である。

**identity と structural equivalence の違い**がここで形になる。copy は
原本と同じ kind・data・attribute・名前を持つが、`NodeId` は別である。
「同じ形である」は `Dom/Properties/Clone.lean` の `CloneOf` が述べ、
「別のものである」は copy の id が木にある id より大きいことから出る。

## 仕様との対応

仕様の "clone a node" は copy を作ってから、parent があれば copy をそこに append し、
deep なら children を順に clone してその copy に append する。

model は **children の copy が揃ってから copy を木に入れる**。つまり copy は
最初から完成した形で店に並び、一度入れた node を後から書き換えることが無い。
こうするのは証明のためで、「新しく足すだけ」という frame がそのまま使えるからである。
観測できる違いは無い。作っている最中の copy はどこからも参照されていない
（live range も `NodeIterator` も registered observer も原本の側を指す）ので、
途中経過を読む手段が無い。

そのため、新しい id は `freshId`（木から導く）ではなく **引数の counter** から取る。
まだ木に入っていない copy の id も使用済みとして数える必要があるからである。
`cloneNode` は `(freshId s.tree).id` を最初の値として渡すので、
取れる id はどれも木にある id より大きい。

fuel が尽きた場合は `none` を返す。`cloneNode` は `Tree.size + 1` を渡す。
children と兄弟のどちらにも同じ fuel を渡すので、必要な fuel は
clone する node の数を超えず、木の node 数で足りる。
-/

namespace Dom

/-- copy の node data。parent・children・node document 以外はそのまま写す。 -/
def cloneData (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : NodeData :=
  { d with parent := parent, children := children, ownerDocument := doc }

@[simp] theorem cloneData_shape (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : (cloneData d doc parent children).shape = d.shape := rfl

@[simp] theorem cloneData_data (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : (cloneData d doc parent children).data = d.data := rfl

@[simp] theorem cloneData_children (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : (cloneData d doc parent children).children = children := rfl

@[simp] theorem cloneData_parent (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : (cloneData d doc parent children).parent = parent := rfl

@[simp] theorem cloneData_ownerDocument (d : NodeData) (doc : NodeId) (parent : Option NodeId)
    (children : List NodeId) : (cloneData d doc parent children).ownerDocument = doc := rfl

/--
copy の node document。

仕様の step 3.1 では、Document を clone した copy の node document は copy 自身であり、
その subtree の copy もそちらに属する。それ以外の node の copy は引数の document に属する。
-/
def cloneDocumentOf (d : NodeData) (doc copy : NodeId) : NodeId :=
  if d.kind == .document then copy else doc

/--
§4.4 "clone a single node"。children を持たない copy を一つ作る。

shadow root は model の対象外なので step 1 は無い。custom element も同様である。
`cloneNode(false)` はこれだけを行う。
-/
def cloneSingle (s : DOMState) (d : NodeData) (doc : NodeId) (parent : Option NodeId) :
    NodeId × DOMState :=
  withFresh s (cloneData d (cloneDocumentOf d doc (freshId s.tree)) parent [])

/--
node の列を順に clone し、`parent` の children になる id の列を返す。

`next` はまだ使っていない id の最小値である。返り値の二つめは、
この呼び出しが使い終えた後の値である。
-/
def cloneMany : Nat → DOMState → Nat → List NodeId → NodeId → Option NodeId →
    Option (List NodeId × Nat × DOMState)
  | _, s, next, [], _, _ => some ([], next, s)
  | 0, _, _, _ :: _, _, _ => none
  | fuel + 1, s, next, n :: rest, doc, parent =>
    match s.tree.get? n with
    | none => none
    | some d =>
      let copy : NodeId := ⟨next⟩
      let doc' := cloneDocumentOf d doc copy
      -- step 3。children を tree order で clone する。copy の id は既に取ってある。
      match cloneMany fuel s (next + 1) d.children doc' (some copy) with
      | none => none
      | some (kids, next₁, s₂) =>
        -- children が揃ったので copy を木に入れる。
        let s₃ := s₂.withTree (s₂.tree.insertNode copy (cloneData d doc' parent kids))
        match cloneMany fuel s₃ next₁ rest doc parent with
        | none => none
        | some (siblings, next₂, s₄) => some (copy :: siblings, next₂, s₄)

/--
DOM Standard §4.4 `cloneNode(deep)`。

返る copy は detach されている。仕様が copy を parent に append するのは
"clone a node" を再帰で呼ぶときだけで、`cloneNode` の入口では parent は null である。
-/
def cloneNode (s : DOMState) (n : NodeId) (deep : Bool) :
    Except DOMException (NodeId × DOMState) :=
  match s.tree.get? n with
  | none => .error .notFoundError
  | some d =>
    if deep then
      match cloneMany (s.tree.size + 1) s (freshId s.tree).id [n] d.ownerDocument none with
      | some (c :: _, _, s') => .ok (c, s')
      -- fuel は足りているので、ここには来ない。
      | _ => .error .outsideModel
    else .ok (cloneSingle s d d.ownerDocument none)

end Dom
