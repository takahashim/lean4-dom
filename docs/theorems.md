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

`AdmissibleDOMState` は六つの成分（構造・node document・Document の children・
Range の端点・NodeIterator・observer registration）の連言である。
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

## 10. oracle は自分の invariant を破らない

| 定理 | module |
| --- | --- |
| `Dom.Exec.runOperations_no_violation` | `Dom/Exec/Invariant.lean` |

```lean
theorem runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

evaluator は各 step の後で `AdmissibleDOMState` の六成分を実行時に検査する。
admissible な初期状態から始めれば、この検査は決して発火しない。
`invariantViolation` が出たら harness 側の誤りである。

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
