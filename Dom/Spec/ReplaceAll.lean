import Dom.Spec.Insert

/-!
# `replace all` の関係意味論（§4.2.3）

`replace` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは `Dom/Spec/ReplaceAllSound.lean` で証明する。

step 4 で `RemoveEachSpec` を、step 5 で `InsertSpec` を composition する。
replace all は validity を自分では検査しない（呼び出し側の `replaceChildren` が step 2 で、
`textContent` などの setter はそもそも validity の要らない node で呼ぶ）。

## removedNodes と addedNodes は木を変える前に決まる

step 1-3 は step 4 の removal より前にある。record に載るのはその値である。
-/

namespace Dom.Spec

open Dom

/-- 仕様の step 2-3：addedNodes。`node` が null なら空、そうでなければ step 5 で入る node 列。 -/
def AddedNodes (t : Tree) (node : Option NodeId) (added : List NodeId) : Prop :=
  (node = none ∧ added = []) ∨ (∃ n, node = some n ∧ NodesToInsert t n added)

/-- 仕様の step 5：`node` が null でなければ、parent の末尾に observer を抑えて insert する。 -/
def ReplaceAllInserted (s : DOMState) (node : Option NodeId) (parent : NodeId)
    (s' : DOMState) : Prop :=
  (node = none ∧ s' = s) ∨ (∃ n, node = some n ∧ InsertSpec s n parent none true s')

/--
**`replace all` の関係意味論。**

`ReplaceAllSpec s node parent s'` は「状態 `s` で `parent` の children を全部 `node` に
置き換えると `s'` になる」と読む。

step 6-7 の record は、addedNodes と removedNodes のどちらかが空でないときだけ積まれる。
step 4 と step 5 は suppress observers を立てて呼ぶので、そちらは record を積まない。
-/
def ReplaceAllSpec (s : DOMState) (node : Option NodeId) (parent : NodeId)
    (s' : DOMState) : Prop :=
  ∃ (removed added : List NodeId) (s₁ s₂ : DOMState),
    -- step 1
    removed = childrenOf s.tree parent ∧
    -- step 2-3
    AddedNodes s.tree node added ∧
    -- step 4
    RemoveEachSpec s removed true s₁ ∧
    -- step 5
    ReplaceAllInserted s₁ node parent s₂ ∧
    -- step 6-7
    ((added = [] ∧ removed = [] ∧ s' = s₂) ∨
      ((added ≠ [] ∨ removed ≠ []) ∧
        TreeRecordQueued s₂ s' parent added removed none none false ∧ ObserverOnly s₂ s'))

end Dom.Spec
