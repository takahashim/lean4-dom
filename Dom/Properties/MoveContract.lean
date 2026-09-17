import Dom.Properties.ReplaceContract

/-!
# 契約：`moveBefore` の成功条件

`move` が落ちうるのは三箇所である。

* step 1-6 の `moveValidity`
* step 10-11, 14 の `detach`
* step 16-18 の `insertAt`

`detach` は step 7-9 の assert（`moveValidity_parentOf_isSome`）から落ちない。
`insertAt` の四つの前提は `moveValidity` が与える——ただし
**reference child が `node` 自身でない**ことだけは別に要る。

仕様の `move` algorithm 自身にその除外は無い
（`dom.bs` の "To move a node ... before null or a node child"）。
除外は `moveBefore()` の method steps の側にある。

    1. Let referenceChild be child.
    2. If referenceChild is node, then set referenceChild to node's next sibling.
    3. Move node into this before referenceChild.

`pre-insert` の step 2-3 と同じ形である。したがって `move` を直接呼ぶときだけ
`child ≠ some node` が要り、`moveBefore` の側では要らない。

`child` が `node` のまま `move` に入ったときの**仕様の**振る舞いは定まっている。
step 14 で `node` を外すと `node` は parent を失うので preceding sibling が 0 個、
§1.4 の定義により index は 0 になり、step 18 は「先頭に入れる」になる。

**model はそこで `notFoundError` を返す。** `insertAt` が「`child` は `parent` の子」を
primitive の前提として検査するからである（`Dom/Mutation/Insert.lean`）。
仕様はその検査を `pre-insert` の validity 側（step 3）に置いていて、
`move` の側には置いていない。したがってこれは **model 側の近似**である。

その差が観測できないことは、散文ではなく二つの検査で押さえてある。

* `moveBefore_reference_ne`（下）：`moveBefore` が `move` に渡す reference child は
  `node` 自身にならない。
* `ruby test/callsites.rb`：`move` を呼ぶ実行定義は `moveBefore` だけである。

二つ合わせて「`move` の `child = node` の枝に届く経路は無い」になる。
どちらかが破れたら差が観測できるようになるので、そのとき検査が落ちる。
-/

namespace Dom

/--
**`moveBefore` が `move` に渡す reference child は `node` 自身にならない。**

step 1-2 が `child = node` を `node` の次の兄弟に取り替え、children に重複が無いので
その結果が `node` になることも無い（`nextSibling_ne_self`）。

`ruby test/callsites.rb`（`move` を呼ぶ実行定義は `moveBefore` だけ）と合わせて、
`move` の `child = node` の枝に届く経路が無いことの根拠になる。
-/
theorem moveBefore_reference_ne {t : Tree} (hwf : WellFormed t) (node : NodeId)
    (child : Option NodeId) :
    (if child = some node then nextSibling t node else child) ≠ some node := by
  by_cases hq : child = some node
  · rw [if_pos hq]; exact nextSibling_ne_self hwf node
  · rw [if_neg hq]; exact hq

/--
**`moveBefore` は、`node` 自身でない reference child で `move` を呼ぶ。**

委譲そのものを定理にしてある。定義を読んで確かめるのではなく、
`moveBefore` が `move` へ渡す値がどういうものかを型で押さえるためである。
-/
theorem moveBefore_eq_move {s : DOMState} (hwf : WellFormed s.tree) {parent node : NodeId}
    {child : Option NodeId} {pd : NodeData} (hpd : s.tree.get? parent = some pd)
    (hk : pd.kind.canHaveChildren = true) :
    ∃ ref, ref ≠ some node ∧ moveBefore s parent node child = move s node parent ref := by
  refine ⟨if child = some node then nextSibling s.tree node else child,
    moveBefore_reference_ne hwf node child, ?_⟩
  unfold moveBefore
  simp only [hpd]
  rw [if_neg (by simp [hk])]

/--
**`move` は validity を通り、reference child が `node` 自身でなければ必ず成功する。**
-/
theorem move_isOk_of_validity {s : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hwf : WellFormed s.tree)
    (hv : moveValidity s.tree node newParent child = .ok ())
    (hcn : child ≠ some node) :
    ∃ s', move s node newParent child = .ok s' := by
  obtain ⟨nd, pd, hnd, hpd, -, -, -, -⟩ := moveValidity_ok hv
  obtain ⟨hanc, hch⟩ := moveValidity_ok_child hv
  have hnotanc : ¬ InclusiveAncestor s.tree node newParent := by
    intro hq
    rw [(isInclusiveAncestorOf_iff hwf node newParent).mpr hq] at hanc
    exact Bool.noConfusion hanc
  -- step 7-9：node は parent を持つ（step 1-2 から従う）
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (moveValidity_parentOf_isSome hwf hv)
  obtain ⟨nd', hnd', hnp'⟩ := parentOf_eq_some hp
  obtain ⟨ppd, hppd⟩ : ∃ ppd, s.tree.get? p = some ppd := exists_data_of_parentOf hwf hp
  have hdet : detach s.tree node = .ok (detachFrom s.tree node p nd' ppd) := by
    simp [detach, hnd', hnp', hppd]
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : DOMState, s₁ =
      (iteratorPreRemove (liveRangePreRemove s node) node).withTree
        (detachFrom s.tree node p nd' ppd) := ⟨_, rfl⟩
  have hdw : detachWithLiveAdjust s node = .ok s₁ := by
    rw [hs₁]; exact detachWithLiveAdjust_of_detach hdet
  have htree₁ : s₁.tree = detachFrom s.tree node p nd' ppd := by
    rw [hs₁, DOMState.withTree_tree]
  have hd₁ : detach s.tree node = .ok s₁.tree := by rw [htree₁]; exact hdet
  have hwf₁ : WellFormed s₁.tree := detach_preserves_wellformed hwf hd₁
  have hsp₁ : ShapePreserving s.tree s₁.tree := shapePreserving_detach hd₁
  -- step 16-18：`insertAt` の四つの前提
  obtain ⟨pd₁, hpd₁⟩ := exists_get?_of_kindPreserving hsp₁ hpd
  obtain ⟨nd₁, hnd₁⟩ := exists_get?_of_kindPreserving hsp₁ hnd
  have hnp₁ : nd₁.parent = none := by
    have hq := detach_parentOf hd₁
    rw [parentOf_of_get? hnd₁] at hq
    exact hq
  have hanc₁ : isInclusiveAncestorOf s₁.tree node newParent = false := by
    cases hb : isInclusiveAncestorOf s₁.tree node newParent with
    | false => rfl
    | true =>
      exfalso
      refine hnotanc ?_
      rcases (isInclusiveAncestorOf_iff hwf₁ node newParent).mp hb with he | hx
      · exact Or.inl he
      · exact Or.inr (ancestor_of_detach hd₁ hx)
  have hchild₁ : ∀ c, child = some c → c ∈ pd₁.children := by
    intro c hc
    have hcp : parentOf s.tree c = some newParent := by
      rw [hc] at hch
      exact childHasParent_some_iff.mp hch
    have hcn' : c ≠ node := fun he => hcn (by rw [hc, he])
    rw [← childrenOf_eq hpd₁]
    refine mem_childrenOf_of_parentOf hwf₁ ?_
    rw [parentOf_detach hd₁, if_neg hcn']
    exact hcp
  have hins := insertAt_eq_ok hpd₁ hnd₁ hnp₁ hanc₁ hchild₁
  unfold move
  simp only [hv, hp, hdw]
  rw [show (liveRangeInsertAdjust s₁ newParent child 1).mapTree
      (fun t => insertAt t newParent node child) =
      .ok ((liveRangeInsertAdjust s₁ newParent child 1).withTree
        (insertAtIn s₁.tree newParent node child pd₁ nd₁)) from by
    show (match insertAt (liveRangeInsertAdjust s₁ newParent child 1).tree newParent node child with
      | Except.error e => Except.error e
      | Except.ok t => Except.ok (_root_.Dom.DOMState.withTree _ t)) = _
    rw [liveRangeInsertAdjust_tree, hins]]
  exact ⟨_, rfl⟩

/--
**`moveBefore` が成功するのは、receiver が `ParentNode` で validity を通るときちょうどである。**

step 1-2 が reference child を `node` の次の兄弟に取り替えるので、
`move` に `child = node` が渡ることは無い（`nextSibling_ne_self`）。
-/
theorem moveBefore_succeeds_iff {s : DOMState} (hwf : WellFormed s.tree)
    {parent node : NodeId} {child : Option NodeId} {pd : NodeData}
    (hpd : s.tree.get? parent = some pd) (hk : pd.kind.canHaveChildren = true) :
    (∃ s', moveBefore s parent node child = .ok s') ↔
      moveValidity s.tree node parent
        (if child = some node then nextSibling s.tree node else child) = .ok () := by
  have href := moveBefore_reference_ne hwf node child
  unfold moveBefore
  simp only [hpd, hk, Bool.not_eq_true']
  rw [if_neg (by simp [hk])]
  constructor
  · rintro ⟨s', h⟩
    exact move_moveValidity h
  · intro hv
    exact move_isOk_of_validity hwf hv href

end Dom
