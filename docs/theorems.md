# 主定理の一覧

`notes/research-foundation-roadmap.md` §16。

木・Range・NodeIterator・CharacterData に分散した結果を、
状態遷移系全体に関する少数の定理として並べる。
依存する axiom は `Audit.lean` が CI で検査している。
許容しているのは `propext` / `Classical.choice` / `Quot.sound` の三つだけで、
`sorryAx` は無い。

## 1. 妥当な状態は決定可能である

| 定理 | module |
| --- | --- |
| `Dom.checkAdmissibleDOMState_iff` | `Dom/Validity/State.lean` |

```lean
theorem checkAdmissibleDOMState_iff (s : DOMState) :
    checkAdmissibleDOMState s = true ↔ AdmissibleDOMState s
```

`AdmissibleDOMState` は七つの成分（構造・node document・Document の children・
Range の端点・NodeIterator・observer registration・attribute list）の連言である。
boolean の checker と `Prop` が一致するので、
evaluator は実行時に同じ条件を検査できる。

## 2. すべての操作が admissibility を保つ

| 定理 | module |
| --- | --- |
| `Dom.Exec.admissible_applyOperation` | `Dom/Exec/Invariant.lean` |

```lean
theorem admissible_applyOperation {s s' : DOMState} {op : Operation}
    (h : AdmissibleDOMState s) (hop : applyOperation s op = .ok s') : AdmissibleDOMState s'
```

`Operation` は harness が扱う全 public API と NodeIterator の走査である。
個別の操作は `Dom/Validity/Admissible.lean` にある。

| 操作 | 定理 |
| --- | --- |
| `appendChild` | `Dom.admissible_appendChild` |
| `insertBefore` | `Dom.admissible_insertBefore` |
| `replaceChild` | `Dom.admissible_replaceChild` |
| `removeChild` | `Dom.admissible_removeChild` |
| `replaceChildren` | `Dom.admissible_replaceChildren` |
| `before` / `after` / `replaceWith` / `remove` | `Dom.admissible_before` ほか |
| `moveBefore` | `Dom.admissible_moveBefore` |
| `appendData` / `insertData` / `deleteData` / `setData` | `Dom.admissible_appendData` ほか |
| `normalize` | `Dom.admissible_normalize` |
| `Range.setStart` / `setEnd` / `setStartBefore` ほか / `collapse` / `selectNode` / `selectNodeContents` | `Dom.admissible_rangeSetStart` ほか |
| `Range.deleteContents` / `insertNode` | `Dom.admissible_rangeDeleteContents`, `Dom.admissible_rangeInsertNode` |
| `TreeWalker` の走査七つ | `Dom.admissible_walkerStep` |
| 値を返すだけの十二（`compareDocumentPosition` ほか） | `Dom.Exec.admissible_requireNodes` |
| `addEventListener` / `removeEventListener` / `dispatchEvent` | `Dom.admissible_addEventListener` ほか |
| `MutationObserver.observe` / `disconnect` / `takeRecords` | `Dom.admissible_observe` ほか |
| notify mutation observers | `Dom.admissible_notifyMutationObservers` |
| `setAttribute` / `setAttributeNS` / `removeAttribute` / `removeAttributeNS` / `toggleAttribute` | `Dom.admissible_setAttribute` ほか |

§4.2.3 の algorithm 側は `Dom.admissible_remove` / `_insert` / `_replace` /
`_replaceAll` / `_move` / `_replaceData`。

## 3. 有限の操作列が admissibility を保つ

| 定理 | module |
| --- | --- |
| `Dom.Exec.run_preserves_admissibility` | `Dom/Exec/Invariant.lean` |

```lean
theorem run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
```

## 4. 到達可能な状態は妥当である

| 定理 | module |
| --- | --- |
| `Dom.Exec.reachable_admissible` | `Dom/Exec/Invariant.lean` |

```lean
theorem reachable_admissible {initial : DOMState → Prop}
    (hinit : ∀ s, initial s → AdmissibleDOMState s) {s : DOMState}
    (hr : ReachableFrom initial s) : AdmissibleDOMState s
```

`AdmissibleDOMState` は局所不変条件の閉包、`ReachableFrom` は構成可能性であり、
別の概念として分けてある。

## 5. `remove` は live object を保つ

| 定理 | module |
| --- | --- |
| `Dom.remove_preserves_live_objects` | `Dom/Validity/Admissible.lean` |

```lean
theorem remove_preserves_live_objects {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : AdmissibleDOMState s) (hr : remove s n b = .ok s') :
    RangeEndpointsValid s' ∧ IteratorsValid s'
```

## 6. `insert` は Range の端点を木の中に保つ

| 定理 | module |
| --- | --- |
| `Dom.insert_preserves_endpoints` | `Dom/Properties/Range.lean` |

DocumentFragment を展開する場合も含む。
**順序（start ≤ end）は保たない。**それが 9 の結果である。

## 7. `move` は remove と insertAt の合成に一致する

| 定理 | module |
| --- | --- |
| `Dom.move_matches_remove_insert_observation` | `Dom/Validity/Admissible.lean` |

```lean
theorem move_matches_remove_insert_observation {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hm : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      insertAt s₁.tree newParent node child = .ok s'.tree ∧
      s'.ranges = (liveRangeInsertAdjust s₁ newParent child 1).ranges ∧
      s'.iterators = s₁.iterators
```

`move` は node document を付け替えないので、`insert`（adopt を含む）ではなく
primitive の `insertAt` との一致になる。

## 8. `replace data` は live object を保つ

| 定理 | module |
| --- | --- |
| `Dom.replaceData_preserves_live_object_validity` | `Dom/Validity/Admissible.lean` |

## 9. `insert` は Range の順序を保たない（negative result）

| 定理 | module |
| --- | --- |
| `Dom.exists_insert_breaking_boundaryLE` | `Dom/Properties/Counterexample.lean` |
| `Dom.boundaryLE_not_preserved_by_insert` | 同上 |

```lean
theorem exists_insert_breaking_boundaryLE :
    ∃ (s s' : DOMState) (parent node child : NodeId) (r r' : RangeState),
      AdmissibleDOMState s ∧ s.ranges = [r] ∧
      BoundaryLE s.tree r.start r.«end» ∧
      insertBefore s parent node (some child) = .ok s' ∧
      AdmissibleDOMState s' ∧ s'.ranges = [r'] ∧
      ValidBoundaryPoint s'.tree r'.start ∧ ValidBoundaryPoint s'.tree r'.«end» ∧
      ¬ BoundaryLE s'.tree r'.start r'.«end»
```

反例の状態は具体的に構成してあり、証明は `decide` だけを使う。
`native_decide` は使っていないので kernel で検査される。
同じ例の JSON 版が `test/scenarios/range-order-broken-by-insert.json` である。

## 10. `TreeWalker` は走査で木から出ない（ただし remove には追随しない）

| 定理 | module |
| --- | --- |
| `Dom.walkersValid_walkerStep` | `Dom/Properties/Walker.lean` |

```lean
theorem walkersValid_walkerStep {s s' : DOMState} {i : Nat} {m : WalkerMethod}
    {r : Option NodeId} (hwf : WellFormed s.tree) (h : WalkersValid s)
    (hs : walkerStep s i m = .ok (r, s')) : WalkersValid s'
```

`WalkersValid` は「root と current が木にある」である。
`NodeIterator` の `ValidIterator` のように
**「current は root の inclusive descendant」までは要求しない**。
§6.2 には "removing steps" が無いので remove がその関係を壊すからで、
それは仕様どおりの挙動である（`test/scenarios/walker-not-adjusted-by-remove.json`）。
そのため `walkers` は `AdmissibleDOMState` の成分ではない
（`Dom/Validity/Walkers.lean` にその理由を書いてある）。

## 11. `compareDocumentPosition` は実装依存の枝でも一貫している

| 定理 | module |
| --- | --- |
| `Dom.compareDocumentPosition_disconnected_consistent` | `Dom/Query/NodeQuery.lean` |

```lean
theorem compareDocumentPosition_disconnected_consistent {t : Tree} {a b : NodeId}
    (hne : a ≠ b) (hr : root t a ≠ root t b) :
    (compareDocumentPosition t a b = 37 ∧ compareDocumentPosition t b a = 35) ∨
    (compareDocumentPosition t a b = 35 ∧ compareDocumentPosition t b a = 37)
```

仕様 §4.4 step 6 は、同じ木にない二つの node について
PRECEDING と FOLLOWING のどちらを返すかを実装に任せたうえで、
**一貫していること**を求めている。model は node id の順で決めるので、
逆から呼べば逆の答えになる。37 は `DISCONNECTED+IMPLEMENTATION_SPECIFIC+FOLLOWING`、
35 は `+PRECEDING` である。

## 12. event の配送は listener list しか変えない

| 定理 | module |
| --- | --- |
| `Dom.listenersOnly_dispatchEvent` | `Dom/Validity/Events.lean` |
| `Dom.admissible_dispatchEvent` | 同上 |

```lean
theorem listenersOnly_dispatchEvent {s s' : DOMState} {target : NodeId} {ty : String}
    {b c r : Bool} {log : List Invocation}
    (hd : dispatchEvent s target ty b c = .ok (s', r, log)) : ListenersOnly s s'
```

`ListenersOnly s s'` は `{ s with listeners := s'.listeners } = s'`、
つまり「listener list 以外は同じ」である。配送は木も range も iterator も触らないので、
admissibility の保存はここから出る。listener の callback は model の外だが、
scenario が宣言した副作用（`ListenerAction`）は listener list しか変えないので、
この定理はその範囲での主張である。

## 13. 実行関数は関係意味論を満たす（`remove`）

| 定理 | module |
| --- | --- |
| `Dom.Spec.remove_sound` | `Dom/Spec/RemoveSound.lean` |
| `Dom.Spec.adopt_sound` | `Dom/Spec/AdoptSound.lean` |
| `Dom.Spec.insert_sound` | `Dom/Spec/InsertSound.lean` |
| `Dom.Spec.replaceData_sound` | `Dom/Spec/ReplaceDataSound.lean` |

```lean
theorem remove_sound {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : remove s n b = .ok s') : RemoveSpec s n b s'
```

`RemoveSpec`（`Dom/Spec/Remove.lean`）は仕様本文から独立に書き写した関係で、
実行側の algorithm を一つも呼ばない。仕様の副作用ごとに六つの component に分かれる。

| component | 仕様の step | soundness |
| --- | --- | --- |
| `RemovePre` | 1-2 | `remove_ok` |
| `RangeAdjusted` | 3 | `Dom.Spec.remove_sound_range` |
| `IteratorAdjusted` | 4 | `Dom.Spec.remove_sound_iterator` |
| `TreeRemoved` | 7 | `Dom.Spec.remove_sound_tree` |
| `TransientAdded` | 20 | `Dom.Spec.remove_sound_transient` |
| `RecordQueued` | 21 | `Dom.Spec.remove_sound_record` |

`adopt`（§4.5）と `insert`（§4.2.3）も同じ形で入れた。`insert` は step 4 で `remove` を、
step 7.1 で `adopt` を呼ぶので、関係もそれぞれ `RemoveSpec` / `AdoptSpec` を composition する
（仕様本文がそう書いているとおりの構成であり、実行関数の再利用ではない）。

`remove` の逆向きのうち **一意性** は示してある。

| 定理 | module |
| --- | --- |
| `Dom.Spec.removeSpec_deterministic` | `Dom/Spec/RemoveDeterministic.lean` |

```lean
theorem removeSpec_deterministic {s s₁ s₂ : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h₁ : RemoveSpec s n b s₁) (h₂ : RemoveSpec s n b s₂) :
    (∀ m, s₁.tree.get? m = s₂.tree.get? m) ∧ s₁.ranges = s₂.ranges ∧ ...
```

木の表現そのものは決まらない（store が association list なので、同じ `get?` を持つ表現が
複数ある）。決まるのは **観測**である。registered observer list は順序を決めていないので
所属の一致になる。soundness と合わせると「`remove` の結果は、関係が許す唯一の観測である」
と言える。completeness（関係を満たす状態が必ず作れること）はまだ無い。

### 観測が等しい状態どうしの congruence

`insert` のように関係を繋いだものの一意性には、上の形では足りない。
途中の状態は観測としてしか一致しないので、
「入力の観測が等しければ出力の観測も等しい」が要る。

| 定理 | module |
| --- | --- |
| `Dom.Spec.ObsEq` | `Dom/Spec/ObsEq.lean` |
| `Dom.Spec.removeSpec_congr` | `Dom/Spec/RemoveCongr.lean` |
| `Dom.Spec.adoptSpec_congr` | `Dom/Spec/AdoptCongr.lean` |
| `Dom.Spec.insertSpec_congr` | `Dom/Spec/InsertCongr.lean` |
| `Dom.Spec.insertSpec_deterministic` | `Dom/Spec/InsertCongr.lean` |

```lean
theorem insertSpec_deterministic {s o₁ o₂ : DOMState} {suppress : Bool}
    (hwf : WellFormed s.tree)
    (hacyc : ∀ ns, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : InsertSpec s node parent child suppress o₁)
    (h₂ : InsertSpec s node parent child suppress o₂) : ObsEq o₁ o₂
```

`hacyc`（入れる node が `parent` の inclusive ancestor でない）は §4.2.1 の
pre-insertion validity が保証するもので、`insert` 本体は前提として受け取る。
これが無いと木が循環し、`TreeInserted` の結果が well-formed でなくなる。

## 14. oracle は自分の invariant を破らない

| 定理 | module |
| --- | --- |
| `Dom.Exec.runOperations_no_violation` | `Dom/Exec/Invariant.lean` |

```lean
theorem runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

evaluator は各 step の後で `AdmissibleDOMState` の七成分を実行時に検査する。
admissible な初期状態から始めれば、この検査は決して発火しない。
`invariantViolation` が出たら harness 側の誤りである。

## 15. `cloneNode` は妥当な木の上では失敗しない

| 定理 | module |
| --- | --- |
| `Dom.cloneNode_isOk` / `Dom.cloneNodeIn_isOk` / `Dom.importNode_isOk` | `Dom/Properties/CloneOk.lean` |

```lean
theorem cloneNode_isOk {s : DOMState} {n : NodeId} {deep : Bool} {d : NodeData}
    (hv : AdmissibleDOMState s) (hd : s.tree.get? n = some d) :
    ∃ c s', cloneNode s n deep = .ok (c, s')
```

model の `cloneNode` は §4.2.3 の `append` を呼ぶので、原理的には pre-insert validity の
検査に落ちて `HierarchyRequestError` を返しうる。落ちうる場所は三つ（fuel の枯渇、
pre-insert validity、`append` の中の `adopt` と `insertAt`）で、妥当な木ではどれも起きない。

要は `AppendableInto` の `docKinds` である。**append 先に既に入れた children の kind 列と、
これから入れる残りの kind 列を繋いだもの**が Document の制約を満たす、という形にしてある。
一つ append すると前半が一つ伸びて後半が一つ縮むだけなので繋いだ列は変わらず、
条件が自分で自分を保つ。最初にそれが成り立つのは、繋いだ列が原本の children の
kind 列そのものだからである。

## 16. selector の API が満たすこと

| 定理 | module |
| --- | --- |
| `Dom.querySelector_eq_head` ほか | `Dom/Selector/Spec.lean` |

```lean
theorem querySelector_eq_head (t : Tree) (selectors : String) (node : NodeId) :
    querySelector t selectors node = (querySelectorAll t selectors node).map List.head?

theorem matchTree_sublist (t : Tree) (sel : SelectorList) (node : NodeId) :
    (matchTree t sel node).Sublist (preorder t node)

theorem mem_matchTree_iff (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) (sel : SelectorList) (e : NodeId) :
    e ∈ matchTree t sel node ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        matchSelList { tree := t, scope := some node } sel e = true
```

`querySelectorAll()` の結果は候補列（`preorder`）の部分列なので **tree order に並ぶ**。
`preorder_nodup` と合わせて **重複が無い**（`matchTree_nodup`）。
入るのはちょうど「scoping root の descendant である element で selector に当たるもの」である。

`closest()` については、返るのが inclusive ancestor である element で selector に当たること
（`closest_spec`）、**それより近いものは当たらないこと**（`closest_first`）、
当たるものが無いときだけ null を返すこと（`closest_eq_none_iff`）を示してある。

## 17. scoping root が見えるのは `:scope` からだけ

| 定理 | module |
| --- | --- |
| `Dom.scope_irrelevant` / `Dom.mem_matchTree_iff_matches` | `Dom/Selector/Spec.lean` |

```lean
theorem matchSelList_scope_irrelevant {t : Tree} {s₁ s₂ a : Option NodeId}
    {l : List Complex} {n : NodeId} (hf : scopeFreeL l = true) :
    matchSelList ⟨t, s₁, a⟩ l n = matchSelList ⟨t, s₂, a⟩ l n
```

`matchSimple` が `ctx.scope` を読むのは `Simple.scope` の枝だけなので、
そこを塞げば scoping root は観測できない。

これが要るのは `matches()` と `querySelectorAll()` を繋ぐためである。前者の scoping root は
element 自身、後者は受け手なので、`:scope` を含む selector では両者が食い違う。
含まなければ一致する（`mem_matchTree_iff_matches`）。

照合は四つの相互再帰なので functional induction が作れない
（`:nth-child(... of S)` の `filter` に再帰呼び出しが入るため）。代わりに
selector の大きさについての強い帰納法で、四つの命題を同時に示している。

## 契約

例外の検査順序と成功条件は `Dom/Properties/Contract.lean` にある。
`docs/traceability.md` の表に algorithm ごとの現状を並べてある。

| 定理 | 内容 |
| --- | --- |
| `Dom.remove_succeeds_iff` | `remove` が成功する必要十分条件 |
| `Dom.remove_error_iff` | `remove` が失敗する必要十分条件 |
| `Dom.replace_cycle_precedes_notFound` | cycle は reference child の検査より先に返る |
| `Dom.ensurePreInsertionValidity_step1` 〜 `_step3` | pre-insert 検査の step 1-3 の優先順位 |
| `Dom.moveValidity_step1` 〜 `_step4` | move 検査の step 1-4 の優先順位 |

## axiom 依存

`Audit.lean` を CI で elaborate する。

```sh
lake env lean Audit.lean
```

許容外の axiom（`sorryAx` を含む）に依存する定理があると失敗する。
