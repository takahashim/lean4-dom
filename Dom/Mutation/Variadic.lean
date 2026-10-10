import Dom.Mutation.Api
import Dom.Mutation.Create

/-!
# 可変長の `(Node or DOMString)` 引数を取る method

DOM Standard §4.2.6 `ParentNode` の `prepend()`・`append()`・`replaceChildren()` と、
§4.2.8 `ChildNode` の `before()`・`after()`・`replaceWith()`。

どれも引数を "convert nodes into a node"（§4.2.6）で一つの node にまとめる。

1. 文字列を、それを data に持つ新しい Text node に置き換える。
2. 一つしか無ければ、それを返す。
3. 新しい DocumentFragment を作り、4. 各 node を append し、5. それを返す。

## 失敗したときの状態

step 4 の append は、node が doctype や Document なら `HierarchyRequestError` で止まる。
本文はそこで例外を投げ、それまでに fragment へ移した node はそのまま残る。method の後半の
pre-insert が失敗した場合も、変換で fragment へ移した node は残る。
これらの method は、失敗しても状態を変えうる。そこで失敗にもその時点の状態を持たせる
（`Except (DOMException × DOMState) DOMState`）。

## 参照されなくなった node

変換が作った DocumentFragment は、挿入の後で空になり、どこからも参照されない。
失敗したときに fragment へ入らなかった Text node も同じである。JavaScript からは観測できないので、
model の状態からも消す（`discard`）。消すのは、parent も children も持たず、live range・
iterator・walker・listener・registered observer・record のどれからも指されていないときだけである。
失敗した変換が残す「文字列の Text node だけが入った fragment」は、部分木ごと消す（`discardFragment`）。
-/

namespace Dom

/-- `(Node or DOMString)` の一つ。 -/
inductive NodeOrString where
  | node (n : NodeId)
  | string (data : String)
deriving DecidableEq, Repr, Inhabited

/-- 引数のうち node であるもの。viable sibling の判定（「nodes に無い」）に使う。 -/
def nodesOf (items : List NodeOrString) : List NodeId :=
  items.filterMap fun | .node n => some n | .string _ => none

/-! ## 参照されなくなった node を消す -/

/-- 木から node を消す。 -/
def Tree.eraseNode (t : Tree) (n : NodeId) : Tree := ⟨t.nodes.erase n⟩

/-- record が node を指すか。 -/
def MutationRecord.mentions (r : MutationRecord) (n : NodeId) : Bool :=
  r.target == n || r.addedNodes.contains n || r.removedNodes.contains n ||
    r.previousSibling == some n || r.nextSibling == some n

/--
**node を指すものが状態のどこにも無いか。**

parent・children・attribute を持たず、Document でなく（Document でなければ誰の node document でもない）、
live range・iterator・walker・listener・registered observer・observer の node list と record の
どれからも指されていない。
-/
def unreferenced (s : DOMState) (n : NodeId) : Bool :=
  match s.tree.get? n with
  | none => false
  | some d =>
    d.parent.isNone && d.children.isEmpty && d.attributes.isEmpty && d.kind != .document &&
    s.ranges.all (fun r => r.start.node != n && r.«end».node != n) &&
    s.iterators.all (fun it => it.root != n && it.reference != n) &&
    s.walkers.all (fun w => w.root != n && w.current != n) &&
    s.listeners.all (fun l => l.target != n) &&
    s.registrations.all (fun r => r.node != n && r.source != some n) &&
    s.observers.all (fun o => !o.nodeList.contains n && o.records.all (fun r => !r.mentions n))

/-- 参照されなくなった node を状態から消す。参照が残っていれば何もしない。 -/
def discard (s : DOMState) (n : NodeId) : DOMState :=
  if unreferenced s n then { s with tree := s.tree.eraseNode n } else s

/-- 作った node を順に、参照されなくなっていれば消す。 -/
def discardAll (s : DOMState) (ns : List NodeId) : DOMState := ns.foldl discard s

/--
**node を、木の親子のほかに指すものが無いか。** attribute を持たず、Document でなく、live range・iterator・
walker・listener・registered observer・observer の node list と record のどれからも指されていない。
-/
def notPointedTo (s : DOMState) (n : NodeId) : Bool :=
  match s.tree.get? n with
  | none => false
  | some d =>
    d.attributes.isEmpty && d.kind != .document &&
    s.ranges.all (fun r => r.start.node != n && r.«end».node != n) &&
    s.iterators.all (fun it => it.root != n && it.reference != n) &&
    s.walkers.all (fun w => w.root != n && w.current != n) &&
    s.listeners.all (fun l => l.target != n) &&
    s.registrations.all (fun r => r.node != n && r.source != some n) &&
    s.observers.all (fun o => !o.nodeList.contains n && o.records.all (fun r => !r.mentions n))

/--
**変換が作った fragment を、部分木ごと消せるか。** parent が無く、子はどれも変換が作った node で子を持たず、
fragment も子も木の親子のほかに指されていない。変換が失敗すると、文字列から作った Text node だけが入った
fragment が残ることがある。Text node と fragment は互いを parent と child として指すので、`unreferenced` は
どちらにも成り立たないが、部分木の外からは辿れず、JavaScript から観測できない。
-/
def fragmentDiscardable (s : DOMState) (frag : NodeId) (created : List NodeId) : Bool :=
  match s.tree.get? frag with
  | none => false
  | some fd =>
    fd.kind == .documentFragment && fd.parent.isNone && notPointedTo s frag &&
    fd.children.all fun c =>
      created.contains c && notPointedTo s c && (childrenOf s.tree c).isEmpty

/--
**変換が作った fragment を部分木ごと消す。** 消せるときは、子を suppress observers flag 付きの "remove" で
fragment から外し（record は積まず、指すものが無いので live object も動かない）、子と fragment を `discard` で
一つずつ消す。消せなければ何もしない（観測できる状態を変えない）。
-/
def discardFragment (s : DOMState) (frag : NodeId) (created : List NodeId) : DOMState :=
  if fragmentDiscardable s frag created then
    let kids := childrenOf s.tree frag
    match removeEach s kids true with
    | .ok s' => discardAll s' (kids ++ [frag])
    | .error _ => s
  else s

/--
**変換が作った node のうち、観測できなくなったものを消す。** 一つずつ `discard` で消してから、作った列の
最後が fragment なら、部分木ごと消せるかを見る。
-/
def discardConverted (s : DOMState) (created : List NodeId) : DOMState :=
  let s' := discardAll s created
  match created.getLast? with
  | some f => discardFragment s' f created
  | none => s'

/-! ## convert nodes into a node -/

/--
step 1。文字列を、左から順に新しい Text node にする。

返り値は（文字列を Text node に置き換えた列、作った Text node の列、状態）。
-/
def textsFor (s : DOMState) (doc : NodeId) :
    List NodeOrString → List NodeId × List NodeId × DOMState
  | [] => ([], [], s)
  | .node n :: rest =>
    let (ns, cs, s') := textsFor s doc rest
    (n :: ns, cs, s')
  | .string d :: rest =>
    let (t, s₁) := withFresh s { kind := .text, ownerDocument := doc, data := d }
    let (ns, cs, s') := textsFor s₁ doc rest
    (t :: ns, t :: cs, s')

/-- step 4。各 node を fragment に append する。失敗したらその時点の状態を返す。 -/
def appendAll (s : DOMState) (frag : NodeId) :
    List NodeId → Except (DOMException × DOMState) DOMState
  | [] => .ok s
  | n :: rest =>
    match append s n frag with
    | .error e => .error (e, s)
    | .ok s' => appendAll s' frag rest

/--
**DOM Standard §4.2.6 "convert nodes into a node"。**

返り値は（node、作った node の列、状態）。作った node の列は、method の終わりに参照されなく
なったものを消すのに使う。失敗したときは、作った node のうち参照されなくなったものを消した状態を返す。
-/
def convertNodesIntoNode (s : DOMState) (items : List NodeOrString) (doc : NodeId) :
    Except (DOMException × DOMState) (NodeId × List NodeId × DOMState) :=
  -- step 1
  let (ns, created, s₁) := textsFor s doc items
  match ns with
  -- step 2
  | [n] => .ok (n, created, s₁)
  | _ =>
    -- step 3
    let (frag, s₂) := withFresh s₁ { kind := .documentFragment, ownerDocument := doc }
    -- step 4
    match appendAll s₂ frag ns with
    | .error (e, s₃) => .error (e, discardConverted s₃ (created ++ [frag]))
    -- step 5
    | .ok s₃ => .ok (frag, created ++ [frag], s₃)

/-- 失敗に状態を付ける。 -/
def withState {α : Type} (s : DOMState) (r : Except DOMException α) :
    Except (DOMException × DOMState) α :=
  match r with
  | .error e => .error (e, s)
  | .ok a => .ok a

/--
変換の後の手順を走らせ、成否どちらでも、変換が作って参照されなくなった node を消す。
-/
def afterConvert (created : List NodeId) (s₁ : DOMState)
    (k : DOMState → Except DOMException DOMState) : Except (DOMException × DOMState) DOMState :=
  match k s₁ with
  | .error e => .error (e, discardConverted s₁ created)
  | .ok s₂ => .ok (discardConverted s₂ created)

/-- 失敗の状態を落とす。algorithm の層（`Except DOMException`）へ渡すときに使う。 -/
def dropState (r : Except (DOMException × DOMState) DOMState) : Except DOMException DOMState :=
  match r with
  | .error (e, _) => .error e
  | .ok s => .ok s

theorem dropState_ok {r : Except (DOMException × DOMState) DOMState} {s : DOMState}
    (h : dropState r = .ok s) : r = .ok s := by
  unfold dropState at h
  split at h
  · cases h
  · cases h; rfl

/-- 失敗したときの状態。成功なら `s` を返す。 -/
def failureState (s : DOMState) (r : Except (DOMException × DOMState) DOMState) : DOMState :=
  match r with
  | .error (_, s') => s'
  | .ok _ => s

/-- `this` の node document。 -/
def nodeDocumentOf (s : DOMState) (this : NodeId) : NodeId :=
  (ownerDocumentOf s.tree this).getD this

/-! ## `ParentNode` -/

/-- **DOM Standard §4.2.6 `ParentNode.prepend(nodes)`。** -/
def prependNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  -- model の都合。this が木に無ければ node document が決まらない。
  if (s.tree.get? this).isNone then .error (.notFoundError, s) else
  match convertNodesIntoNode s items (nodeDocumentOf s this) with
  | .error p => .error p
  | .ok (node, created, s₁) =>
    -- step 2。first child は変換の後の木で決まる。
    afterConvert created s₁ fun s₁ => preInsert s₁ node this (childrenOf s₁.tree this).head?

/-- **DOM Standard §4.2.6 `ParentNode.append(nodes)`。** -/
def appendNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  -- model の都合。this が木に無ければ node document が決まらない。
  if (s.tree.get? this).isNone then .error (.notFoundError, s) else
  match convertNodesIntoNode s items (nodeDocumentOf s this) with
  | .error p => .error p
  | .ok (node, created, s₁) => afterConvert created s₁ fun s₁ => append s₁ node this

/-- **DOM Standard §4.2.6 `ParentNode.replaceChildren(nodes)`。** -/
def replaceChildrenNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  -- model の都合。this が木に無ければ node document が決まらない。
  if (s.tree.get? this).isNone then .error (.notFoundError, s) else
  match convertNodesIntoNode s items (nodeDocumentOf s this) with
  | .error p => .error p
  | .ok (node, created, s₁) =>
    -- step 2-3
    afterConvert created s₁ fun s₁ => replaceChildren s₁ this (some node)

/-! ## `ChildNode` -/

/-- **DOM Standard §4.2.8 `ChildNode.before(nodes)`。** -/
def beforeNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  -- step 1-2
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    -- step 3。変換の前の木で決める。
    let viable := viablePreviousSibling s.tree this (nodesOf items)
    -- step 4
    match convertNodesIntoNode s items (nodeDocumentOf s this) with
    | .error p => .error p
    | .ok (node, created, s₁) =>
      afterConvert created s₁ fun s₁ =>
        -- step 5。変換の後の木で決める。
        let ref := match viable with
          | none => (childrenOf s₁.tree parent).head?
          | some v => nextSibling s₁.tree v
        -- step 6
        preInsert s₁ node parent ref

/-- **DOM Standard §4.2.8 `ChildNode.after(nodes)`。** -/
def afterNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    let viable := viableNextSibling s.tree this (nodesOf items)
    match convertNodesIntoNode s items (nodeDocumentOf s this) with
    | .error p => .error p
    | .ok (node, created, s₁) => afterConvert created s₁ fun s₁ => preInsert s₁ node parent viable

/-- **DOM Standard §4.2.8 `ChildNode.replaceWith(nodes)`。** -/
def replaceWithNodes (s : DOMState) (this : NodeId) (items : List NodeOrString) :
    Except (DOMException × DOMState) DOMState :=
  match parentOf s.tree this with
  | none => .ok s
  | some parent =>
    let viable := viableNextSibling s.tree this (nodesOf items)
    match convertNodesIntoNode s items (nodeDocumentOf s this) with
    | .error p => .error p
    | .ok (node, created, s₁) =>
      afterConvert created s₁ fun s₁ =>
        -- step 5。変換で this が fragment に移っていれば、parent はもう this の parent ではない。
        if parentOf s₁.tree this = some parent then replace s₁ this node parent
        -- step 6
        else preInsert s₁ node parent viable

end Dom
