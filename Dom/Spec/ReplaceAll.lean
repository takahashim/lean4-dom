import Dom.Spec.Insert

/-!
# `replace all` の関係意味論（§4.2.3）

`replace` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは `Dom/Spec/ReplaceAllSound.lean` で証明する。

step 5 で `RemoveEachSpec` を、step 6 で `InsertSpec` を composition する。
replace all は validity を自分では検査しない（呼び出し側の `replaceChildren` が step 2 で、
`textContent` などの setter はそもそも validity の要らない node で呼ぶ）。

## removedNodes と addedNodes は木を変える前に決まる

step 1-4 は step 5 の removal より前にある。record に載るのはその値である。
-/

namespace Dom.Spec

open Dom

/-- 仕様の step 2-4：addedNodes。`node` が null なら空、そうでなければ step 6 で入る node 列。 -/
def AddedNodes (t : Tree) (node : Option NodeId) (added : List NodeId) : Prop :=
  (node = none ∧ added = []) ∨ (∃ n, node = some n ∧ NodesToInsert t n added)

/-- 仕様の step 6：`node` が null でなければ、parent の末尾に observer を抑えて insert する。 -/
def ReplaceAllInserted (s : DOMState) (node : Option NodeId) (parent : NodeId)
    (s' : DOMState) : Prop :=
  (node = none ∧ s' = s) ∨ (∃ n, node = some n ∧ InsertSpec s n parent none true s')

/--
**`replace all` の関係意味論。**

`ReplaceAllSpec s node parent s'` は「状態 `s` で `parent` の children を全部 `node` に
置き換えると `s'` になる」と読む。

step 7 の record は、addedNodes と removedNodes のどちらかが空でないときだけ積まれる。
step 5 と step 6 は suppress observers を立てて呼ぶので、そちらは record を積まない。
-/
def ReplaceAllSpec (s : DOMState) (node : Option NodeId) (parent : NodeId)
    (s' : DOMState) : Prop :=
  ∃ (removed added : List NodeId) (s₁ s₂ : DOMState),
    -- step 1
    removed = childrenOf s.tree parent ∧
    -- step 2-4
    AddedNodes s.tree node added ∧
    -- step 5
    RemoveEachSpec s removed true s₁ ∧
    -- step 6
    ReplaceAllInserted s₁ node parent s₂ ∧
    -- step 7
    ((added = [] ∧ removed = [] ∧ s' = s₂) ∨
      ((added ≠ [] ∨ removed ≠ []) ∧
        TreeRecordQueued s₂ s' parent added removed none none false ∧ ObserverOnly s₂ s'))

end Dom.Spec
