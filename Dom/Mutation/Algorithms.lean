import Dom.Mutation.Detach
import Dom.Mutation.Insert
import Dom.Mutation.Adopt
import Dom.Range.Adjust

/-!
# WHATWG の mutation algorithm

DOM Standard §4.2.3（mutation algorithms）と §4.5（adopt）を、
Phase 2 の primitive（`detach`, `insertAt`, `setOwnerDocument`）の上に組み立てる。

参照した仕様の版は `docs/spec-version.md` のとおり。
各定義の doc comment に仕様の step 番号を残す。

状態は木だけでなく live object も含む `DOMState` である（PLAN §8.1）。
Phase 2 の primitive（`detach`, `insertAt`, `setOwnerDocument`）は木だけを変えるので
`Tree` の上に残し、ここでは `DOMState` に持ち上げて使う。

live object の調整は `liveRangePreRemove` / `liveRangeInsertAdjust`（`Dom/Range/Adjust.lean`）と
`iteratorPreRemove`（Phase 6 で中身を入れる）で行う。
hook の位置は仕様の step 順序に合わせてある（PLAN §6.1）。

本 model は Shadow DOM を扱わないので、仕様の
「host-including inclusive ancestor」は `InclusiveAncestor`、
「shadow-including root」は `root`、
「shadow-including inclusive descendant」は `InclusiveDescendant` に読み替える。
また、他の仕様のための拡張点である insertion steps / removing steps / moving steps、
custom element reaction、slot assignment、MutationObserver の record は扱わない。
-/

namespace Dom

open Dom.ListUtil

/-! ## live object の調整 hook -/

/--
DOM Standard §4.2.3 remove step 4 / move step 11（NodeIterator pre-remove steps）。
Phase 6 で中身を入れる。
-/
def iteratorPreRemove (s : DOMState) (_node : NodeId) : DOMState := s

@[simp] theorem iteratorPreRemove_tree (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).tree = s.tree := rfl

@[simp] theorem iteratorPreRemove_ranges (s : DOMState) (n : NodeId) :
    (iteratorPreRemove s n).ranges = s.ranges := rfl

/-! ## 木の走査に使う補助定義 -/

/-- `n` の次の兄弟。 -/
def nextSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match splitAt? (childrenOf t p) n with
    | none => none
    | some (_, after) => after.head?

/-- `n` の前の兄弟。 -/
def previousSibling (t : Tree) (n : NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match splitAt? (childrenOf t p) n with
    | none => none
    | some (before, _) => before.getLast?

/-- `nodes` に含まれない、`n` の最初の preceding sibling（DOM Standard §4.2.9）。 -/
def viablePreviousSibling (t : Tree) (n : NodeId) (nodes : List NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match splitAt? (childrenOf t p) n with
    | none => none
    | some (before, _) => before.reverse.find? fun x => !nodes.contains x

/-- `nodes` に含まれない、`n` の最初の following sibling（DOM Standard §4.2.9）。 -/
def viableNextSibling (t : Tree) (n : NodeId) (nodes : List NodeId) : Option NodeId :=
  match parentOf t n with
  | none => none
  | some p =>
    match splitAt? (childrenOf t p) n with
    | none => none
    | some (_, after) => after.find? fun x => !nodes.contains x

/-- `p` の children のうち element であるもの。 -/
def elementChildren (t : Tree) (p : NodeId) : List NodeId :=
  (childrenOf t p).filter fun c => kindOf t c == some .element

/-- `p` の children のうち doctype であるもの。 -/
def doctypeChildren (t : Tree) (p : NodeId) : List NodeId :=
  (childrenOf t p).filter fun c => kindOf t c == some .documentType

/-- `p` の children のうち Text であるもの。 -/
def textChildren (t : Tree) (p : NodeId) : List NodeId :=
  (childrenOf t p).filter fun c => kindOf t c == some .text

/--
`c` より後ろに doctype があるか。

仕様の「a doctype is following child」は tree order での following だが、
doctype の parent になれるのは Document だけなので、
well-formed な木では「`c` より後ろの兄弟に doctype がある」と同値である。
-/
def doctypeFollows (t : Tree) (parent c : NodeId) : Bool :=
  match splitAt? (childrenOf t parent) c with
  | none => false
  | some (_, after) => after.any fun x => kindOf t x == some .documentType

/--
`c` より前に element があるか。

仕様の「an element is preceding child」も tree order での preceding だが、
`c` より前の兄弟の部分木に element があればその兄弟自身が element なので、
「`c` より前の兄弟に element がある」と同値である。
-/
def elementPrecedes (t : Tree) (parent c : NodeId) : Bool :=
  match splitAt? (childrenOf t parent) c with
  | none => false
  | some (before, _) => before.any fun x => kindOf t x == some .element

/--
DOM Standard §4.2.3 ensure pre-insert validity step 3 / move step 3。
`child` が指定されていれば、その parent が `parent` であること。
-/
def childHasParent (t : Tree) (child : Option NodeId) (parent : NodeId) : Bool :=
  match child with
  | none => true
  | some c => parentOf t c = some parent

/-! ## remove -/

/--
remove と move が共有する部分。
仕様の remove step 3,4,7 と move step 10,11,14 に対応する。
-/
def detachWithLiveAdjust (s : DOMState) (node : NodeId) : Except DOMException DOMState :=
  (iteratorPreRemove (liveRangePreRemove s node) node).mapTree fun t => detach t node

/--
DOM Standard §4.2.3 "remove"。

step 1-2 は parent が非 null であることの assert なので、model では
parent が無ければ `notFoundError` を返す。
step 15 の removing steps は他仕様のための拡張点なので扱わない。
-/
def remove (s : DOMState) (node : NodeId) : Except DOMException DOMState :=
  match parentOf s.tree node with
  | none => .error .notFoundError
  | some _ => detachWithLiveAdjust s node

/-- node の列を順に remove する。DOM Standard §4.2.3 insert step 4 などで使う。 -/
def removeEach : DOMState → List NodeId → Except DOMException DOMState
  | s, [] => .ok s
  | s, n :: ns =>
    match remove s n with
    | .error e => .error e
    | .ok s' => removeEach s' ns

/-! ## adopt -/

/--
DOM Standard §4.5 "adopt"。

step 2 の removal は素の detach ではなく完全な `remove` を呼ぶ。
`memo.md` が指摘する「explicit remove は adjustment を通るが
move 中の implicit removal は通らない」という不一致は、この構造で防がれる（PLAN §6.1）。
-/
def adopt (s : DOMState) (node doc : NodeId) : Except DOMException DOMState :=
  -- step 1
  match ownerDocumentOf s.tree node with
  | none => .error .notFoundError
  | some oldDocument =>
    -- step 2
    match (match parentOf s.tree node with
           | none => (.ok s : Except DOMException DOMState)
           | some _ => remove s node) with
    | .error e => .error e
    | .ok s₁ =>
      -- step 3
      if doc = oldDocument then .ok s₁
      else .ok (s₁.withTree (setOwnerDocument s₁.tree node doc))

/-! ## ensure pre-insert validity -/

/--
DOM Standard §4.2.3 ensure pre-insert validity step 9.1。
node が element、または element の子を持つ DocumentFragment のときの検査。
-/
def checkElementInsertion (t : Tree) (parent : NodeId) (child : Option NodeId)
    (childrenToExclude : List NodeId) : Except DOMException Unit :=
  if (elementChildren t parent).any (fun c => !childrenToExclude.contains c) then
    .error .hierarchyRequestError
  else
    match child with
    | none => .ok ()
    | some c =>
      if doctypeFollows t parent c then .error .hierarchyRequestError
      else if kindOf t c == some .documentType && !childrenToExclude.contains c then
        .error .hierarchyRequestError
      else .ok ()

/-- DOM Standard §4.2.3 ensure pre-insert validity step 11。node が doctype のときの検査。 -/
def checkDoctypeInsertion (t : Tree) (parent : NodeId) (child : Option NodeId)
    (childrenToExclude : List NodeId) : Except DOMException Unit :=
  if (doctypeChildren t parent).any (fun c => !childrenToExclude.contains c) then
    .error .hierarchyRequestError
  else
    match child with
    | some c => if elementPrecedes t parent c then .error .hierarchyRequestError else .ok ()
    | none =>
      if (elementChildren t parent).any (fun c => !childrenToExclude.contains c) then
        .error .hierarchyRequestError
      else .ok ()

/--
DOM Standard §4.2.3 "ensure pre-insert validity"。

現行の仕様は `childrenToExclude` を取る形になっている。
`pre-insert` は « » を、`replace` は « child » を渡す。
木だけを見る検査なので `Tree` の上に置く。
-/
def ensurePreInsertionValidity (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (childrenToExclude : List NodeId) : Except DOMException Unit :=
  match t.get? parent with
  | none => .error .notFoundError
  | some pd =>
    match t.get? node with
    | none => .error .notFoundError
    | some nd =>
      -- step 1
      if !(pd.kind == .document || pd.kind == .documentFragment || pd.kind == .element) then
        .error .hierarchyRequestError
      -- step 2
      else if isInclusiveAncestorOf t node parent then
        .error .hierarchyRequestError
      -- step 3
      else if !childHasParent t child parent then
        .error .notFoundError
      -- step 4
      else if !(nd.kind == .documentFragment || nd.kind == .documentType ||
                nd.kind == .element || nd.kind.isCharacterData) then
        .error .hierarchyRequestError
      -- step 5
      else if pd.kind ≠ .document then
        if nd.kind == .documentType then .error .hierarchyRequestError else .ok ()
      -- step 6
      else if nd.kind == .text then .error .hierarchyRequestError
      -- step 7
      else if nd.kind.isCharacterData then .ok ()
      -- step 8
      else if nd.kind == .documentFragment then
        if 1 < (elementChildren t node).length || !(textChildren t node).isEmpty then
          .error .hierarchyRequestError
        else if (elementChildren t node).isEmpty then .ok ()
        else checkElementInsertion t parent child childrenToExclude
      -- step 9
      else if nd.kind == .element then
        checkElementInsertion t parent child childrenToExclude
      -- step 10-11（node は doctype）
      else checkDoctypeInsertion t parent child childrenToExclude

/-! ## insert -/

/-- DOM Standard §4.2.3 insert step 7。各 node を adopt してから parent に入れる。 -/
def insertEach : DOMState → NodeId → Option NodeId → NodeId → List NodeId →
    Except DOMException DOMState
  | s, _, _, _, [] => .ok s
  | s, parent, child, doc, n :: ns =>
    match adopt s n doc with
    | .error e => .error e
    | .ok s₁ =>
      match s₁.mapTree fun t => insertAt t parent n child with
      | .error e => .error e
      | .ok s₂ => insertEach s₂ parent child doc ns

/-- DOM Standard §4.2.3 insert step 7。parent の node document を取り出して各 node を入れる。 -/
def insertEachAt (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (nodes : List NodeId) : Except DOMException DOMState :=
  match s.tree.get? parent with
  | none => .error .notFoundError
  | some pd => insertEach s parent child pd.ownerDocument nodes

/-- DOM Standard §4.2.3 insert step 5 と 7。 -/
def insertNodesAt (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (nodes : List NodeId) : Except DOMException DOMState :=
  insertEachAt (liveRangeInsertAdjust s parent child nodes.length) parent child nodes

/--
DOM Standard §4.2.3 "insert"。

DocumentFragment を渡すと、その children を展開して順に挿入する。
-/
def insert (s : DOMState) (node parent : NodeId) (child : Option NodeId) :
    Except DOMException DOMState :=
  match s.tree.get? node with
  | none => .error .notFoundError
  | some nd =>
    if nd.kind == .documentFragment then
      -- step 1：nodes は fragment の children
      if nd.children.isEmpty then .ok s  -- step 2-3
      else
        -- step 4：fragment の children を先に外す
        match removeEach s nd.children with
        | .error e => .error e
        | .ok s₁ => insertNodesAt s₁ parent child nd.children
    else
      -- step 1-3：nodes は « node » なので空にならない
      insertNodesAt s parent child [node]

/-! ## pre-insert / append / pre-remove / replace / replace all -/

/-- DOM Standard §4.2.3 "pre-insert"。 -/
def preInsert (s : DOMState) (node parent : NodeId) (child : Option NodeId) :
    Except DOMException DOMState :=
  -- step 1
  match ensurePreInsertionValidity s.tree node parent child [] with
  | .error e => .error e
  | .ok () =>
    -- step 2-3
    let referenceChild := if child = some node then nextSibling s.tree node else child
    -- step 4
    insert s node parent referenceChild

/-- DOM Standard §4.2.3 "append"。 -/
def append (s : DOMState) (node parent : NodeId) : Except DOMException DOMState :=
  preInsert s node parent none

/-- DOM Standard §4.2.3 "pre-remove"。 -/
def preRemove (s : DOMState) (child parent : NodeId) : Except DOMException DOMState :=
  -- step 1
  if parentOf s.tree child ≠ some parent then .error .notFoundError
  -- step 2
  else remove s child

/-- DOM Standard §4.2.3 "replace"。 -/
def replace (s : DOMState) (child node parent : NodeId) : Except DOMException DOMState :=
  -- step 1
  match ensurePreInsertionValidity s.tree node parent (some child) [child] with
  | .error e => .error e
  | .ok () =>
    -- step 2-3
    let referenceChild₀ := nextSibling s.tree child
    let referenceChild := if referenceChild₀ = some node then nextSibling s.tree node
                          else referenceChild₀
    match s.tree.get? parent with
    | none => .error .notFoundError
    | some pd =>
      -- step 6
      match adopt s node pd.ownerDocument with
      | .error e => .error e
      | .ok s₁ =>
        -- step 7
        match (match parentOf s₁.tree child with
               | none => (.ok s₁ : Except DOMException DOMState)
               | some _ => remove s₁ child) with
        | .error e => .error e
        | .ok s₂ =>
          -- step 9
          insert s₂ node parent referenceChild

/--
DOM Standard §4.2.3 "replace all"。

仕様どおり、この algorithm 自身は node tree の制約を検査しない。
-/
def replaceAll (s : DOMState) (node : Option NodeId) (parent : NodeId) :
    Except DOMException DOMState :=
  -- step 1, 4
  match removeEach s (childrenOf s.tree parent) with
  | .error e => .error e
  | .ok s₁ =>
    -- step 5
    match node with
    | none => .ok s₁
    | some n => insert s₁ n parent none

/-! ## move -/

/--
DOM Standard §4.2.3 "move"（2025 年に追加された algorithm）。

remove と insert の合成と違う点は次の三つである。

* removing steps と insertion steps を走らせない（本 model はどちらも扱わない）。
* node document を付け替えない（step 1 が同じ root であることを要求するため）。
* validity の検査が `ensure pre-insert validity` ではなく step 1-6 の独自のものである。

live range と NodeIterator の pre-remove steps（step 10-11）と
挿入側の offset 調整（step 16）は走らせる。
したがって木・Range・NodeIterator に射影した結果は remove と insert の合成と一致する。
これを `move_eq_remove_insertAt` で示す。
-/
def moveValidity (t : Tree) (node newParent : NodeId) (child : Option NodeId) :
    Except DOMException Unit :=
  match t.get? newParent with
  | none => .error .notFoundError
  | some pd =>
    match t.get? node with
    | none => .error .notFoundError
    | some nd =>
      -- step 1
      if root t newParent ≠ root t node then .error .hierarchyRequestError
      -- step 2
      else if isInclusiveAncestorOf t node newParent then .error .hierarchyRequestError
      -- step 3
      else if !childHasParent t child newParent then .error .notFoundError
      -- step 4
      else if !(nd.kind == .element || nd.kind.isCharacterData) then
        .error .hierarchyRequestError
      -- step 5
      else if nd.kind == .text && pd.kind == .document then .error .hierarchyRequestError
      -- step 6
      else if pd.kind == .document && nd.kind == .element &&
          (!(elementChildren t newParent).isEmpty ||
            (match child with
             | none => false
             | some c => kindOf t c == some .documentType || doctypeFollows t newParent c)) then
        .error .hierarchyRequestError
      else .ok ()

/-- DOM Standard §4.2.3 "move" の step 1-6（validity）と step 7-18（本体）。 -/
def move (s : DOMState) (node newParent : NodeId) (child : Option NodeId) :
    Except DOMException DOMState :=
  match moveValidity s.tree node newParent child with
  | .error e => .error e
  | .ok () =>
    -- step 7-9（oldParent が非 null であることの assert。step 1-2 から従う）
    match parentOf s.tree node with
    | none => .error .hierarchyRequestError
    | some _ =>
      -- step 10-11, 14
      match detachWithLiveAdjust s node with
      | .error e => .error e
      | .ok s₁ =>
        -- step 16-18
        (liveRangeInsertAdjust s₁ newParent child 1).mapTree fun t =>
          insertAt t newParent node child

end Dom
