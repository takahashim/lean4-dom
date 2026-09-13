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
どちらの読みでも同じで、違うのは record の並びだけである
（`normalizeBatch` と `normalize_batch_agrees` にその比較を置く）。

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
survivor に続く exclusive Text の run を畳む。

`cands` は tree order で並べた候補の残りで、返り値の第二成分は畳んだ個数である。
Text node は子を持たないので、survivor の次の兄弟が exclusive Text なら
それは候補列の次の要素にほかならない。
-/
def normalizeRun (s : DOMState) (survivor : NodeId) :
    List NodeId → Except DOMException (DOMState × Nat)
  | [] => .ok (s, 0)
  | sib :: rest =>
    if nextSibling s.tree survivor = some sib then
      match normalizeMergeOne s survivor sib with
      | .error e => .error e
      | .ok s' =>
        match normalizeRun s' survivor rest with
        | .error e => .error e
        | .ok (s'', k) => .ok (s'', k + 1)
    else .ok (s, 0)

/--
候補列を順に処理する。

長さ 0 のものは外し（step 2）、それ以外は run の先頭として畳む。
先の run で畳まれて木から外れたものは飛ばす。
-/
def normalizeList (s : DOMState) : List NodeId → Except DOMException DOMState
  | [] => .ok s
  | n :: rest =>
    match s.tree.get? n, parentOf s.tree n with
    | some d, some _ =>
      if d.length = 0 then
        match remove s n with
        | .error e => .error e
        | .ok s' => normalizeList s' rest
      else
        match normalizeRun s n rest with
        | .error e => .error e
        | .ok (s', k) => normalizeList s' (rest.drop k)
    | _, _ => normalizeList s rest
termination_by l => l.length
decreasing_by
  · simp_wf
  · simp_wf
    exact Nat.lt_succ_of_le (by simp)
  · simp_wf

/--
DOM Standard §4.4 `Node.normalize()`。

対象は `node` の **descendant**（自身は含まない）exclusive Text node である。
Text node に対して呼んでも何も起きない。
-/
def normalize (s : DOMState) (node : NodeId) : Except DOMException DOMState :=
  match s.tree.get? node with
  | none => .error .notFoundError
  | some _ => normalizeList s (((preorder s.tree node).drop 1).filter (isExclusiveText s.tree))

end Dom
