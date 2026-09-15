import Dom.Mutation.Clone

/-!
# 別の document から node を持ってくる（§4.5）

`importNode` と `adoptNode`。どちらも「別の document にある node をこの document で
使えるようにする」ものだが、**identity の扱いが正反対**である。

* `importNode` は **copy を作る**。返るのは新しい `NodeId` で、原本は動かない。
* `adoptNode` は **node そのものを移す**。返るのは渡した `NodeId` のままで、
  元の親からは外れる。

どちらも受け手が Document でなければ `TypeError` を返す。仕様では `Document` の
method なので受け手は必ず Document だが、model は id を受け取るので、
WebIDL の受け手検査に当たるものをここで行う
（`docs/threats-to-validity.md` の「WebIDL の TypeError」を参照）。

shadow root は model の対象外なので、それを弾く step は無い。
-/

namespace Dom

/--
DOM Standard §4.5 `importNode(node, options)`。

`options` が boolean のときの形だけを扱う。`subtree` はその値である。
custom element registry を指定する dictionary の形は model の対象外である。

step 1 で Document を弾いてから、"clone a node" を document = this、parent = null で呼ぶ。
-/
def importNode (s : DOMState) (doc : NodeId) (n : NodeId) (subtree : Bool) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match s.tree.get? n with
    | none => .error .notFoundError
    | some d =>
      -- step 1
      if d.kind == .document then .error .notSupportedError
      else cloneNodeIn s n doc subtree

/--
DOM Standard §4.5 `adoptNode(node)`。

step 1 で Document を弾いてから §4.5 の "adopt" を呼び、渡された node を返す。
-/
def adoptNode (s : DOMState) (doc : NodeId) (n : NodeId) :
    Except DOMException (NodeId × DOMState) :=
  match requireDocument s.tree doc with
  | .error e => .error e
  | .ok _ =>
    match s.tree.get? n with
    | none => .error .notFoundError
    | some d =>
      -- step 1
      if d.kind == .document then .error .notSupportedError
      else
        -- step 3
        match adopt s n doc with
        | .error e => .error e
        | .ok s' => .ok (n, s')

end Dom
