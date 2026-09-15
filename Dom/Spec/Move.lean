import Dom.Spec.Insert

/-!
# `move` の関係意味論（§4.2.4）

`remove` / `insert` と違って、`move` はそれらを呼ばない。
仕様が「pre-remove steps を走らせて木から外し、offset を調整して入れる」と
段を並べて書いているので、関係もその段をそのまま並べる。

`remove` との差は二つある。

* **transient registered observer を足さない**（`remove` の step 20 は `move` に無い）
* **record は最後に二つまとめて積む**（旧 parent に removal、新 parent に addition）

step 1-6（`moveValidity`）は別の algorithm なので、ここには含めない。
`InsertSpec` が pre-insert を含まないのと同じ扱いである。
-/

namespace Dom.Spec

open Dom

/-! ## step 10-11, 14：木から外す -/

/--
仕様の step 10-11 と 14。

`remove` の step 3-4, 7 と同じ三つ（live range / NodeIterator / 木）だが、
observer の側は何も動かない。
-/
def MoveDetached (s s' : DOMState) (node parent : NodeId) (index : Nat) : Prop :=
  RangeAdjusted s s' node parent index ∧
  IteratorAdjusted s s' node ∧
  TreeRemoved s.tree s'.tree node parent ∧
  ObserversUntouched s s'

/-! ## 全体 -/

/--
**`move` の関係意味論。**

`MoveSpec s node newParent child s'` は
「状態 `s` で `node` を `newParent` の `child` の直前へ動かすと `s'` になる」と読む。
step 1-6 の validity を通った後の話である。

record に載る旧 parent 側の兄弟は **木を変える前**の値、
新 parent 側の兄弟は **外した後・入れる前**の値である（step 12-13 と step 17）。
-/
def MoveSpec (s : DOMState) (node newParent : NodeId) (child : Option NodeId)
    (s' : DOMState) : Prop :=
  ∃ (oldParent : NodeId) (index idx : Nat) (newPrev : Option NodeId) (s₁ sa s₂ s₃ : DOMState),
    -- step 7-9。oldParent が非 null であることの assert。
    parentOf s.tree node = some oldParent ∧
    index = ((Dom.index s.tree node).getD 0) ∧
    -- step 10-11, 14
    MoveDetached s s₁ node oldParent index ∧
    -- step 17
    PreviousSiblingOf s₁.tree newParent child newPrev ∧
    -- step 16
    ChildIndex s₁.tree child idx ∧
    RangeInsertAdjusted s₁ sa newParent child idx 1 ∧
    -- step 18
    TreeInserted sa.tree s₂.tree newParent node child ∧
    LiveObjectsUnchangedExceptTree sa s₂ ∧
    -- step 23。旧 parent に removal。
    TreeRecordQueued s₂ s₃ oldParent [] [node]
      (previousSibling s.tree node) (nextSibling s.tree node) false ∧
    ObserverOnly s₂ s₃ ∧
    -- step 24。新 parent に addition。
    TreeRecordQueued s₃ s' newParent [node] [] newPrev child false ∧
    ObserverOnly s₃ s'

end Dom.Spec
