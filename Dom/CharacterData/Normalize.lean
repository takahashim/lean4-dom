import Dom.Mutation.Algorithms
import Dom.CharacterData.ReplaceData

/-!
# `Node.normalize()`

DOM Standard §4.4。`this` の descendant exclusive Text node を走査し、
長さ 0 のものを外し、隣り合うものを先頭のものへ畳む。

## 仕様の読みと engine の実装が違うところ

仕様を字義どおり読むと、step 3-4 は run 全体の data を**一度に**連結して
"replace data" を一回だけ呼ぶので、characterData の record は run ごとに一つになる。
実際の engine（Blink・WebCore・Gecko）は兄弟ごとに畳み、
四つの Text node の run に対して characterData / childList / characterData / childList …
と record を積む。WPT が固定しているのは childList の側だけである
（Dommy の issue #24 に三つの engine で確かめた記録がある）。

本 model は **engine 側の読み（兄弟ごと）** を採る。木と live range の最終状態は
どちらの読みでも同じで、違うのは record の並びだけである。
関係意味論（`Dom/Spec/Normalize.lean`）も同じ読みで書く。

## 空の兄弟

data が空の兄弟は、畳んでも data が変わらないので characterData record を積まない
（engine も step 4 を飛ばす）。boundary point の引き渡しは行う。
-/

namespace Dom

/-- exclusive Text node か。CDATASection は Text を継承するが exclusive ではない。 -/
def isExclusiveText (t : Tree) (n : NodeId) : Bool :=
  match t.get? n with
  | some d => d.kind == .text
  | none => false

/--
DOM Standard §4.4 normalize step 6.1-6.4。

畳まれて消える兄弟 `sib` が持っていた boundary point を survivor へ渡す。
`len` は survivor の（この兄弟を畳む直前の）長さで、そこが継ぎ目になる。
`idx` は parent の children の中での `sib` の位置である。

remove より**前**に呼ぶ。後にすると live range の pre-remove steps が
boundary point を parent 側へ移してしまう。
-/
def normalizeMergeBP (survivor sib parent : NodeId) (idx len : Nat) (bp : BoundaryPoint) :
    BoundaryPoint :=
  if bp.node = sib then { node := survivor, offset := bp.offset + len }
  else if bp.node = parent ∧ bp.offset = idx then { node := survivor, offset := len }
  else bp

/-- `normalizeMergeBP` を range の両端に当てる。 -/
def normalizeMergeRange (survivor sib parent : NodeId) (idx len : Nat) (r : RangeState) :
    RangeState :=
  { start := normalizeMergeBP survivor sib parent idx len r.start
    «end» := normalizeMergeBP survivor sib parent idx len r.«end» }

/--
兄弟を一つ畳む。data を足し、boundary point を渡し、兄弟を外す。

`sib` が survivor の次の兄弟であることは呼び出し側が確かめる。
どちらも exclusive Text で、別の node であることはここで確かめる
（呼び出し側の候補列はそう絞ってあるが、長さの計算がその kind に依るので算法の側にも置く）。
-/
def normalizeMergeOne (s : DOMState) (survivor sib : NodeId) : Except DOMException DOMState :=
  match s.tree.get? survivor, s.tree.get? sib, parentOf s.tree sib, index s.tree sib with
  | some dsurv, some dsib, some parent, some idx =>
    if survivor == sib || dsurv.kind != NodeKind.text || dsib.kind != NodeKind.text then
      .error .invalidNodeTypeError
    else
    let len := dsurv.length
    -- step 3-4。空の兄弟には data の step が無い（record も積まない）。
    match (if dsib.data.isEmpty then Except.ok s else replaceData s survivor len 0 dsib.data) with
    | .error e => .error e
    | .ok s₁ =>
      -- step 6.1-6.4
      let s₂ := { s₁ with
                    ranges := s₁.ranges.map (normalizeMergeRange survivor sib parent idx len) }
      -- step 7
      remove s₂ sib
  | _, _, _, _ => .error .notFoundError

/--
§4.4 の「contiguous exclusive Text nodes」のうち、`n` より後ろのもの。

`n` の次の兄弟から、exclusive Text が続くかぎり tree order で並べる。
normalize は descendant を tree order で処理し、run の先頭が後ろを全部畳むので、
処理する時点で `n` の前に exclusive Text の兄弟は残っていない。
-/
def followingTexts (t : Tree) (n : NodeId) : List NodeId :=
  match parentOf t n with
  | none => []
  | some p =>
    match ListUtil.splitAt? (childrenOf t p) n with
    | none => []
    | some (_, after) => after.takeWhile (isExclusiveText t)

/--
survivor に続く exclusive Text の兄弟 `sibs` を、tree order で一つずつ畳む（step 3-7）。

兄弟ごとに data を足し、boundary point を渡し、外す（engine の読み）。
-/
def normalizeRun (s : DOMState) (survivor : NodeId) :
    List NodeId → Except DOMException DOMState
  | [] => .ok s
  | sib :: rest =>
    match normalizeMergeOne s survivor sib with
    | .error e => .error e
    | .ok s' => normalizeRun s' survivor rest

/--
候補列（`this` の descendant exclusive Text node を tree order で並べたもの）を順に処理する。

先の run で畳まれて `this` の descendant でなくなったものは飛ばす。
残るものは、長さ 0 なら外し（step 2）、そうでなければ run の先頭として畳む。
-/
def normalizeList (s : DOMState) (this : NodeId) : List NodeId → Except DOMException DOMState
  | [] => .ok s
  | n :: rest =>
    if isAncestorOf s.tree this n then
      match s.tree.get? n with
      | none => normalizeList s this rest
      | some d =>
        if d.length = 0 then
          match remove s n with
          | .error e => .error e
          | .ok s' => normalizeList s' this rest
        else
          match normalizeRun s n (followingTexts s.tree n) with
          | .error e => .error e
          | .ok s' => normalizeList s' this rest
    else normalizeList s this rest

/--
DOM Standard §4.4 `Node.normalize()`。

対象は `node` の **descendant**（自身は含まない）exclusive Text node である。
Text node に対して呼んでも何も起きない。
-/
def normalize (s : DOMState) (node : NodeId) : Except DOMException DOMState :=
  match s.tree.get? node with
  | none => .error .notFoundError
  | some _ => normalizeList s node (((preorder s.tree node).drop 1).filter (isExclusiveText s.tree))

end Dom
