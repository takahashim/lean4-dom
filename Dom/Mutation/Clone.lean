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

/--
copy の node data。parent・children・node document 以外はそのまま写す。

**attribute には新しい id を振る。** 仕様の "clone a single node" step 2.1 は
attribute ごとに clone を作るので、copy の `Attr` は原本とは別のものである。
`base` から list 順に振る。呼び出し側は `maxAttrId + 1` を渡す。
-/
def cloneData (d : NodeData) (doc : NodeId) (base : Nat) : NodeData :=
  { d with parent := none, children := [], ownerDocument := doc,
           attributes := d.attributes.zipIdx.map fun (a, i) => { a with id := ⟨base + i⟩ } }

@[simp] theorem cloneData_data (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).data = d.data := rfl

@[simp] theorem cloneData_kind (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).kind = d.kind := rfl

@[simp] theorem cloneData_children (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).children = [] := rfl

@[simp] theorem cloneData_parent (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).parent = none := rfl

@[simp] theorem cloneData_ownerDocument (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).ownerDocument = doc := rfl

@[simp] theorem cloneData_attributes (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).attributes =
      d.attributes.zipIdx.map (fun p => { p.1 with id := ⟨base + p.2⟩ }) := rfl

/-- id を落とせば attribute list は写したままである。 -/
@[simp] theorem cloneData_anonAttributes (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).attributes.map Attr.anon = d.attributes.map Attr.anon := by
  simp only [cloneData_attributes, List.map_map]
  have : d.attributes.zipIdx.map (fun p => (Attr.anon { p.1 with id := ⟨base + p.2⟩ })) =
      d.attributes.zipIdx.map (fun p => Attr.anon p.1) := by
    refine List.map_congr_left fun p _ => rfl
  rw [Function.comp_def, this]
  rw [show (fun p : Attr × Nat => Attr.anon p.1) = Attr.anon ∘ Prod.fst from rfl,
    ← List.map_map, List.zipIdx_map_fst]

@[simp] theorem cloneData_attributes_length (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).attributes.length = d.attributes.length := by
  simp [cloneData]

@[simp] theorem cloneData_attributes_keys (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).attributes.map Attr.key = d.attributes.map Attr.key := by
  have h : ∀ l : List Attr, l.map Attr.key = (l.map Attr.anon).map Attr.key := by
    intro l; rw [List.map_map]; rfl
  rw [h, cloneData_anonAttributes, ← h]

/-- copy の attribute は、id を除けば原本のどれかと同じである。 -/
theorem cloneData_mem_anon {d : NodeData} {doc : NodeId} {base : Nat} {a : Attr}
    (h : a ∈ (cloneData d doc base).attributes) : ∃ b ∈ d.attributes, b.anon = a.anon := by
  have hm : a.anon ∈ d.attributes.map Attr.anon := by
    rw [← cloneData_anonAttributes d doc base]
    exact List.mem_map_of_mem h
  obtain ⟨b, hb, hba⟩ := List.mem_map.mp hm
  exact ⟨b, hb, hba⟩

/-- **copy は id 以外は原本と同じ形である。** -/
@[simp] theorem cloneData_shapeAnon (d : NodeData) (doc : NodeId) (base : Nat) :
    (cloneData d doc base).shapeAnon = d.shapeAnon := by
  unfold NodeData.shapeAnon
  simp only [NodeData.shape_attributes, cloneData_anonAttributes]
  rfl

/--
copy の node document。

Document の copy は自分自身を node document とする。それ以外の copy は
引数の document に属する。
-/
def cloneDocumentOf (d : NodeData) (doc copy : NodeId) : NodeId :=
  if d.kind == .document then copy else doc

/-- §4.4 "clone a single node"。children も parent も持たない copy を一つ作る。 -/
def cloneSingle (s : DOMState) (d : NodeData) (doc : NodeId) : NodeId × DOMState :=
  withFresh s (cloneData d (cloneDocumentOf d doc (freshId s.tree)) (maxAttrId s.tree + 1))

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
