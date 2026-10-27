import Dom.Spec.Insert

/-!
# `move` の関係意味論（§4.2.4）

`remove` / `insert` と違って、`move` はそれらを呼ばない。
仕様が「pre-remove steps を走らせて木から外し、offset を調整して入れる」と
段を並べて書いているので、関係もその段をそのまま並べる。

`remove` との差は、**record を最後に二つまとめて積む**（旧 parent に removal、新 parent に addition）
ことである。木から外す段（`Detached`）と transient registered observer を足す段（`TransientAdded`）は
`remove` と同じ関係を使う。

step 1-6（`moveValidity`）は別の algorithm なので、ここには含めない。
`InsertSpec` が pre-insert を含まないのと同じ扱いである。
-/

namespace Dom.Spec

open Dom

/-! ## 全体 -/

/--
**`move` の関係意味論。**

`MoveSpec s node newParent child s'` は
「状態 `s` で `node` を `newParent` の `child` の直前へ動かすと `s'` になる」と読む。
step 1-6 の validity を通った後の話である。

record に載る旧 parent 側の兄弟は **木を変える前**の値、
新 parent 側の兄弟は **外した後・入れる前**の値である（step 11-12 と step 19）。
-/
def MoveSpec (s : DOMState) (node newParent : NodeId) (child : Option NodeId)
    (s' : DOMState) : Prop :=
  ∃ (oldParent : NodeId) (index idx : Nat) (newPrev : Option NodeId) (s₁ sₜ sa s₂ s₃ : DOMState),
    -- step 7-8。oldParent が非 null であることの assert。
    parentOf s.tree node = some oldParent ∧
    index = ((Dom.index s.tree node).getD 0) ∧
    -- step 9-10, 13
    Detached s s₁ node oldParent index ∧
    -- step 17
    TransientAdded s₁ sₜ node oldParent ∧
    -- step 19
    PreviousSiblingOf sₜ.tree newParent child newPrev ∧
    -- step 18
    ChildIndex sₜ.tree child idx ∧
    RangeInsertAdjusted sₜ sa newParent child idx 1 ∧
    -- step 20-21
    TreeInserted sa.tree s₂.tree newParent node child ∧
    LiveObjectsUnchangedExceptTree sa s₂ ∧
    -- step 26。旧 parent に removal。
    TreeRecordQueued s₂ s₃ oldParent [] [node]
      (previousSibling s.tree node) (nextSibling s.tree node) false ∧
    ObserverOnly s₂ s₃ ∧
    -- step 27。新 parent に addition。
    TreeRecordQueued s₃ s' newParent [node] [] newPrev child false ∧
    ObserverOnly s₃ s'

end Dom.Spec
