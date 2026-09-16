import Dom.Mutation.Detach
import Dom.Mutation.Insert
import Dom.Mutation.Adopt
import Dom.Range.Adjust
import Dom.Traversal.NodeIterator
import Dom.Observer.Record

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
`iteratorPreRemove`（`Dom/Traversal/NodeIterator.lean`）で行う。
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

/-! ## 木の走査に使う補助定義 -/

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

/--
`p` の children のうち Text であるもの。

`CDATASection` は仕様上 `Text` の subclass なのでここに含める。
-/
def textChildren (t : Tree) (p : NodeId) : List NodeId :=
  (childrenOf t p).filter fun c =>
    match kindOf t c with
    | some k => k.isText
    | none => false

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
def remove (s : DOMState) (node : NodeId) (suppressObservers : Bool := false) :
    Except DOMException DOMState :=
  match parentOf s.tree node with
  | none => .error .notFoundError
  | some parent =>
    -- step 12-13。木を変える前の兄弟を控える。
    let oldPreviousSibling := previousSibling s.tree node
    let oldNextSibling := nextSibling s.tree node
    match detachWithLiveAdjust s node with
    | .error e => .error e
    | .ok s₁ =>
      -- step 20。外す部分木の中の変更も subtree observer が配送まで見続けられるようにする。
      -- `parent` の ancestor は node を外しても変わらないので、
      -- 仕様どおり step 14 の後で数えてよい。
      let s₂ := addTransientObservers s₁ node parent
      -- step 21
      if suppressObservers then .ok s₂
      else .ok (queueTreeMutationRecord s₂ parent [] [node] oldPreviousSibling oldNextSibling)

/-- node の列を順に remove する。DOM Standard §4.2.3 insert step 4 などで使う。 -/
def removeEach (s : DOMState) (ns : List NodeId) (suppressObservers : Bool := false) :
    Except DOMException DOMState :=
  match ns with
  | [] => .ok s
  | n :: rest =>
    match remove s n suppressObservers with
    | .error e => .error e
    | .ok s' => removeEach s' rest suppressObservers

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
      else if nd.kind.isText then .error .hierarchyRequestError
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

/-- DOM Standard §4.2.3 insert step 5-9。 -/
def insertNodesAt (s : DOMState) (parent : NodeId) (child : Option NodeId)
    (nodes : List NodeId) (suppressObservers : Bool := false) :
    Except DOMException DOMState :=
  -- step 6。木を変える前に決める。
  let prev := match child with
    | some c => previousSibling s.tree c
    | none => (childrenOf s.tree parent).getLast?
  -- step 5, 7
  match insertEachAt (liveRangeInsertAdjust s parent child nodes.length) parent child nodes with
  | .error e => .error e
  | .ok s' =>
    -- step 9
    if suppressObservers then .ok s'
    else .ok (queueTreeMutationRecord s' parent nodes [] prev child)

/--
DOM Standard §4.2.3 "insert"。

DocumentFragment を渡すと、その children を展開して順に挿入する。
-/
def insert (s : DOMState) (node parent : NodeId) (child : Option NodeId)
    (suppressObservers : Bool := false) : Except DOMException DOMState :=
  match s.tree.get? node with
  | none => .error .notFoundError
  | some nd =>
    if nd.kind == .documentFragment then
      -- step 1：nodes は fragment の children
      if nd.children.isEmpty then .ok s  -- step 2-3
      else
        -- step 4：fragment の children を先に外す
        match removeEach s nd.children true with
        | .error e => .error e
        | .ok s₁ =>
          -- step 4.2。suppressObservers に関わらず fragment に record を積む。
          insertNodesAt (queueTreeMutationRecord s₁ node [] nd.children none none)
            parent child nd.children suppressObservers
    else
      -- step 1-3：nodes は « node » なので空にならない
      insertNodesAt s parent child [node] suppressObservers

/--
`insert` が成功したときに通った枝を、本体を開かずに取り出す。

DOM Standard §4.2.3 の step 1-4 にあたる三つの場合しかない。`insert` を使う証明は
この補題だけを見ればよく、本体の分岐の書き方には依存しない。
-/
theorem insert_cases {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} (h : insert s node parent child b = .ok s') :
    ∃ nd, s.tree.get? node = some nd ∧
      ((nd.kind = NodeKind.documentFragment ∧ nd.children = [] ∧ s' = s)
        ∨ (nd.kind = NodeKind.documentFragment ∧ nd.children ≠ [] ∧
            ∃ s₁, removeEach s nd.children true = .ok s₁ ∧
              insertNodesAt (queueTreeMutationRecord s₁ node [] nd.children none none)
                parent child nd.children b = .ok s')
        ∨ (nd.kind ≠ NodeKind.documentFragment ∧
            insertNodesAt s parent child [node] b = .ok s')) := by
  unfold insert at h
  split at h
  · simp at h
  · next nd hnd =>
    refine ⟨nd, hnd, ?_⟩
    split at h
    · next hkind =>
      have hk : nd.kind = NodeKind.documentFragment := by simpa using hkind
      split at h
      · next hempty =>
        exact Or.inl ⟨hk, by simpa using hempty, (Except.ok.inj h).symm⟩
      · next hempty =>
        split at h
        · simp at h
        · next s₁ hre =>
          exact Or.inr (Or.inl ⟨hk, by simpa using hempty, s₁, hre, h⟩)
    · next hkind =>
      exact Or.inr (Or.inr ⟨by simpa using hkind, h⟩)

/--
fragment でない node の `insert` は step 1-3 と step 5-9 だけ、つまり
`insertNodesAt` そのものである。`insert` の結果を作る側の証明はこれを使う。
-/
theorem insert_of_not_fragment {s : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} {nd : NodeData} (hnd : s.tree.get? node = some nd)
    (hk : nd.kind ≠ NodeKind.documentFragment) :
    insert s node parent child b = insertNodesAt s parent child [node] b := by
  unfold insert
  rw [hnd]
  simp only [beq_iff_eq, hk, if_false]

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

/--
DOM Standard §4.2.3 "replace" step 2-3 の reference child。

`child` の次の兄弟。ただしそれが `node` 自身なら、さらにその次を取る。
-/
def replaceReferenceChild (t : Tree) (child node : NodeId) : Option NodeId :=
  if nextSibling t child = some node then nextSibling t node else nextSibling t child

/--
DOM Standard §4.2.3 "replace" step 8 の nodes。

fragment なら children、そうでなければ « node »。
-/
def replaceNodes (t : Tree) (node : NodeId) : List NodeId :=
  match t.get? node with
  | some nd => if nd.kind == .documentFragment then nd.children else [node]
  | none => [node]

/-- DOM Standard §4.2.3 "replace"。 -/
def replace (s : DOMState) (child node parent : NodeId) : Except DOMException DOMState :=
  -- step 1
  match ensurePreInsertionValidity s.tree node parent (some child) [child] with
  | .error e => .error e
  | .ok () =>
    match s.tree.get? parent with
    | none => .error .notFoundError
    | some pd =>
      -- step 6
      match adopt s node pd.ownerDocument with
      | .error e => .error e
      | .ok s₁ =>
        -- step 7。removedNodes は child が実際に外れたときだけ « child »。
        match (match parentOf s₁.tree child with
               | none => (.ok s₁ : Except DOMException DOMState)
               | some _ => remove s₁ child true) with
        | .error e => .error e
        | .ok s₂ =>
          -- step 9。record は step 10 でまとめて積むので、ここでは抑制する。
          match insert s₂ node parent (replaceReferenceChild s.tree child node) true with
          | .error e => .error e
          | .ok s₃ =>
            -- step 10。previousSibling と nodes は木を変える前の値。
            .ok (queueTreeMutationRecord s₃ parent (replaceNodes s.tree node)
              (if (parentOf s₁.tree child).isSome then [child] else [])
              (previousSibling s.tree child) (replaceReferenceChild s.tree child node))

/--
`replace` が成功したときに通った経路を、本体を開かずに取り出す。

DOM Standard §4.2.3 の step 1 / 6 / 7 / 9 / 10 にあたる。step 7 だけが
「`child` に parent があるか」で二つに分かれる。
-/
theorem replace_cases {s s' : DOMState} {child node parent : NodeId}
    (h : replace s child node parent = .ok s') :
    ∃ pd s₁ s₂ s₃,
      ensurePreInsertionValidity s.tree node parent (some child) [child] = .ok () ∧
      s.tree.get? parent = some pd ∧
      adopt s node pd.ownerDocument = .ok s₁ ∧
      ((parentOf s₁.tree child = none ∧ s₂ = s₁) ∨
        ((∃ q, parentOf s₁.tree child = some q) ∧ remove s₁ child true = .ok s₂)) ∧
      insert s₂ node parent (replaceReferenceChild s.tree child node) true = .ok s₃ ∧
      s' = queueTreeMutationRecord s₃ parent (replaceNodes s.tree node)
        (if (parentOf s₁.tree child).isSome then [child] else [])
        (previousSibling s.tree child) (replaceReferenceChild s.tree child node) := by
  unfold replace at h
  split at h
  · simp at h
  · next hv =>
    split at h
    · simp at h
    · next pd hpd =>
      split at h
      · simp at h
      · next s₁ ha =>
        split at h
        · simp at h
        · next s₂ hrm =>
          split at h
          · simp at h
          · next s₃ hi =>
            refine ⟨pd, s₁, s₂, s₃, ?_, hpd, ha, ?_, hi, (Except.ok.inj h).symm⟩
            · cases hx : ensurePreInsertionValidity s.tree node parent (some child) [child] with
              | error e => rw [hx] at hv; exact absurd hv (by simp)
              | ok u => cases u; rfl
            · revert hrm
              cases hp : parentOf s₁.tree child with
              | none => intro hrm; exact Or.inl ⟨rfl, (Except.ok.inj hrm).symm⟩
              | some q => intro hrm; exact Or.inr ⟨⟨q, rfl⟩, hrm⟩

/-- `replaceReferenceChild` の値。 -/
theorem replaceReferenceChild_eq (t : Tree) (child node : NodeId) :
    replaceReferenceChild t child node =
      if nextSibling t child = some node then nextSibling t node else nextSibling t child := rfl

/-- `replaceNodes` の値。 -/
theorem replaceNodes_eq {t : Tree} {node : NodeId} {nd : NodeData} (hnd : t.get? node = some nd) :
    replaceNodes t node =
      if nd.kind == NodeKind.documentFragment then nd.children else [node] := by
  unfold replaceNodes
  rw [hnd]

/-- step 1 で落ちたら `replace` はその例外をそのまま返す。 -/
theorem replace_of_validity_error {s : DOMState} {child node parent : NodeId}
    {e : DOMException}
    (hv : ensurePreInsertionValidity s.tree node parent (some child) [child] = .error e) :
    replace s child node parent = .error e := by
  unfold replace
  rw [hv]

/--
DOM Standard §4.2.3 "replace all"。

仕様どおり、この algorithm 自身は node tree の制約を検査しない。
-/
def replaceAll (s : DOMState) (node : Option NodeId) (parent : NodeId) :
    Except DOMException DOMState :=
  -- step 1-3
  let removedNodes := childrenOf s.tree parent
  let addedNodes := match node with
    | none => []
    | some n =>
      match s.tree.get? n with
      | some nd => if nd.kind == .documentFragment then nd.children else [n]
      | none => [n]
  -- step 4
  match removeEach s removedNodes true with
  | .error e => .error e
  | .ok s₁ =>
    -- step 5
    match (match node with
           | none => (.ok s₁ : Except DOMException DOMState)
           | some n => insert s₁ n parent none true) with
    | .error e => .error e
    | .ok s₂ =>
      -- step 6-7
      .ok (queueTreeMutationRecord s₂ parent addedNodes removedNodes none none)

/-! ## move -/

/--
DOM Standard §4.2.3 "move" step 6 の後半。

「`child` が doctype である」か「`child` より後ろに doctype がある」か。
`child` が null ならどちらも成り立たない。
-/
def doctypeAtOrAfter (t : Tree) (parent : NodeId) (child : Option NodeId) : Bool :=
  match child with
  | none => false
  | some c => kindOf t c == some .documentType || doctypeFollows t parent c

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
      -- step 5。`CDATASection` は仕様上 `Text` の subclass なので `isText` で判定する。
      else if nd.kind.isText && pd.kind == .document then .error .hierarchyRequestError
      -- step 6
      else if pd.kind == .document && nd.kind == .element &&
          (!(elementChildren t newParent).isEmpty ||
            doctypeAtOrAfter t newParent child) then
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
      -- step 12-13
      let oldPreviousSibling := previousSibling s.tree node
      let oldNextSibling := nextSibling s.tree node
      let oldParent := parentOf s.tree node
      -- step 10-11, 14
      match detachWithLiveAdjust s node with
      | .error e => .error e
      | .ok s₁ =>
        -- step 17。挿入前の兄弟。
        let newPreviousSibling := match child with
          | some c => previousSibling s₁.tree c
          | none => (childrenOf s₁.tree newParent).getLast?
        -- step 16-18
        match (liveRangeInsertAdjust s₁ newParent child 1).mapTree fun t =>
          insertAt t newParent node child with
        | .error e => .error e
        | .ok s₂ =>
          -- step 23-24。旧 parent に removal、新 parent に addition の二つ。
          let s₃ := match oldParent with
            | none => s₂
            | some p => queueTreeMutationRecord s₂ p [] [node] oldPreviousSibling oldNextSibling
          .ok (queueTreeMutationRecord s₃ newParent [node] [] newPreviousSibling child)

end Dom
