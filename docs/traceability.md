# 仕様トレーサビリティ

`notes/research-foundation-roadmap.md` §10。

WHATWG DOM Standard の algorithm と、Lean の実行関数・契約・固定 scenario・
Dommy 側の WPT 由来 test を結ぶ対応表である。

参照する仕様は `docs/spec-version.md` に固定した commit
`a2331a45360129e8645ef7e0a04740241b6e3726`（2026-08-25）である。
step 番号だけに頼ると仕様改訂でずれるので、各行に短い step 要約も置く。

## 読み方

| 列 | 内容 |
| --- | --- |
| Evaluator | `Dom/Mutation/` などの実行関数 |
| Contracts | preservation / success / exception / effect / frame の定理名 |
| Scenario | `test/scenarios/` の固定 scenario |
| WPT | Dommy 側の WPT 由来 test（`gems/dommy/test/wpt/`） |
| Status | 済 / 部分 / 未 |

**spec relation の列は置いていない。** 本 model は関係意味論と実行関数を分けておらず、
実行関数 `Except DOMException DOMState` そのものを意味論としている。
妥当性は述語（`AdmissibleDOMState` など）として別に持つ。
roadmap §5 が求める「任意の declarative layer」はまだ無い。

## §4.2.3 node tree の mutation

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| ensure pre-insert validity | 1 parent の kind / 2 cycle / 3 child の parent / 4 node の kind / 5 非 Document / 6 Text / 7 CharacterData / 8 fragment / 9 element / 10-11 doctype | `ensurePreInsertionValidity` | exception 順序 `ensurePreInsertionValidity_step1`〜`_step3`、事実の抽出 `_parentCanHaveChildren` `_nodeNotDocument` `_doctypeParentIsDocument` `_childParent` `_documentFacts` | `childnode-after-bypasses-validity`, `childnode-before-leaks-backend-error`, `replacechildren-bypasses-validity`, `replacewith-bypasses-validity` | `test_wpt_child_node_pre_insertion_validity.rb` | 済 |
| pre-insert | 1 validity / 2-3 reference child のずらし / 4 insert | `preInsert` | preservation `admissible_preInsert`、委譲 `insertBefore_refines_preInsert`、reference child `ensurePreInsertionValidity_shift` | 同上 | `test_wpt_node_mutation.rb` | 済 |
| insert | 1-3 nodes と count / 4 fragment の children を外す / 5 live range の offset 調整 / 6 previousSibling / 7 adopt して入れる / 9 record | `insert`, `insertNodesAt`, `insertEachAt`, `insertEach` | preservation `admissible_insert`、effect `insert_parentOf` `insert_children_split` `insert_preserves_endpoints`、frame `insertAt_frame`、negative `exists_insert_breaking_boundaryLE` | `basic-insert-remove`, `range-adjust-order-on-before`, `range-order-broken-by-insert` | `test_wpt_live_range_insert_order.rb`, `test_wpt_mutation_record_insertion_point.rb` | 済（success は未） |
| append | 1 pre-insert(child=null) | `append` | 委譲 `append_refines_preInsert`、preservation `admissible_append` | `basic-insert-remove` | `test_wpt_node_mutation.rb` | 済 |
| remove | 1-2 parent の assert / 3 live range の pre-remove / 4 NodeIterator の pre-remove / 14 children から外す / 20 transient observer / 21 record | `remove`, `detachWithLiveAdjust`, `detach` | preservation `admissible_remove`、success `remove_succeeds_iff`、exception `remove_error_iff`、effect `remove_parentOf` `remove_not_mem_childrenOf` `remove_ranges` `remove_iterators`、frame `detach_frame` | `basic-insert-remove`, `iterator-adjust-on-remove`, `iterator-adjust-pointer-before` | `test_wpt_mutation_primitives.rb`, `test_wpt_transient_registered_observer.rb` | 済 |
| pre-remove | 1 parent の一致 / 2 remove | `preRemove` | exception `preRemove_error_notFound`、委譲 `removeChild_refines_preRemove` | `basic-insert-remove` | `test_wpt_node_methods_on_every_node.rb` | 済 |
| replace | 1 validity(child を除外) / 2-3 reference child / 4 previousSibling / 6 adopt / 7 child を外す / 9 insert / 10 record | `replace` | preservation `admissible_replace`、exception `replace_cycle_precedes_notFound`、effect `replace_reference_head` | `replacewith-bypasses-validity` | `test_wpt_mutation_record_insertion_point.rb` | 済（success は未） |
| replace all | 1-3 removedNodes と addedNodes / 4 children を全部外す / 5 insert / 7 record | `replaceAll` | preservation `admissible_replaceAll`、effect `removeEach_childrenOf_nil` | `replacechildren-bypasses-validity` | `test_wpt_node_mutation.rb` | 済 |
| move | 1 同じ root / 2 cycle / 3 reference child / 4 node の kind / 5 Text と Document / 6 Document の element と doctype / 10-11 pre-remove / 14 外す / 16 offset 調整 / 18 入れる / 23-24 record | `move`, `moveValidity`, `moveBefore` | preservation `admissible_move` `admissible_moveBefore`、exception 順序 `moveValidity_step1`〜`_step4`、effect `move_eq_remove_insertAt` `move_parentOf` `move_childrenOf` `move_ranges` `move_iterators` | `range-adjust-order-on-move` | `test_wpt_move_before.rb` | 済（success は未） |

## §4.10 CharacterData

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| replace data | 1-2 IndexSizeError / 3 count の切り詰め / 4 record / 5-7 data の差し替え / 8-11 live range の調整 | `replaceData` と `appendData` / `insertData` / `deleteData` / `setData` | preservation `admissible_replaceData` ほか四つ、effect `replaceData_ok` | `characterdata-index-size-and-clamp`, `characterdata-replace-data-ranges` | `test_wpt_character_data.rb` | 済（success と exception は未） |

## §5.5 live Range / §6.1 NodeIterator

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| live range pre-remove steps | 1-4 | `liveRangePreRemove` | `remove_preserves_endpoints`, `valid_liveRangePreRemoveBP`, `boundaryLE_detach` | `iterator-adjust-on-remove` | `test_wpt_range_mutations.rb` | 済 |
| live range の insert 側調整 | insert step 5 | `liveRangeInsertAdjust` | `rangeValidUpTo_liveRangeInsertAdjust` | `range-adjust-order-on-before`, `range-order-broken-by-insert` | `test_wpt_live_range_insert_order.rb` | 済 |
| NodeIterator pre-remove steps | 1-5 | `iteratorPreRemove`, `iteratorPreRemoveOne` | `remove_preserves_iterators_valid`, `remove_iterators_leave_subtree`, `adjustNodePointer_spec` | `iterator-adjust-on-remove`, `iterator-adjust-pointer-before` | `test_wpt_node_edges.rb` | 済 |
| nextNode / previousNode | §6.1 | `nextNode`, `previousNode` | `validIterator_nextNode`, `validIterator_previousNode` | `iterator-adjust-pointer-before` | `test_wpt_node_edges.rb` | 済 |

## §4.3 MutationObserver

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| queue a mutation record | 1-2 inclusive ancestor を辿って observer を集める / 3-6 record を積む | `queueMutationRecord`, `interestedObservers` | preservation `preservesRegs_*` | `observer-uninterested-registration-does-not-shadow` | `test_wpt_mutation_record_details.rb`, `test_wpt_mutation_observer_order.rb` | 済（attribute を除く） |
| queue a tree mutation record | 1 assert / 2 queue | `queueTreeMutationRecord` | 同上 | 同上 | `test_wpt_mutation_record_insertion_point.rb` | 済 |
| transient registered observer | remove step 20 | `addTransientObservers` | `preservesRegs_remove` | `observer-transient-follows-existing-registration` | `test_wpt_transient_registered_observer.rb` | 済 |
| queue a mutation observer microtask | 1-3 | `queueMutationObserverMicrotask`, `addPendingObserver` | preservation `admissible_*`（配送は木を触らない） | `observer-delivery` | `test_wpt_mutation_observer_order.rb` | 済 |
| notify mutation observers | 1-5 | `notifyMutationObservers`, `notifyEach`, `notifyOne`, `removeTransients` | `admissible_notifyMutationObservers`, `notifyMutationObservers_tree/_ranges/_iterators` | 同上 | 同上 | 済 |
| `observe(target, options)` | 1-8（step 3 / 6 の TypeError を含む） | `MutationObserver.observe` | `admissible_observe`, `observe_tree/_ranges/_iterators` | `observer-uninterested-registration-does-not-shadow` | 同上 | 済（attribute を除く） |
| `disconnect()` | 1-2 | `MutationObserver.disconnect` | `admissible_disconnect`, `disconnect_tree/_ranges/_iterators` | （生成 scenario の `disconnect`） | 同上 | 済 |
| `takeRecords()` | 1-3 | `MutationObserver.takeRecords` | `admissible_takeRecords`, `takeRecords_tree/_ranges/_iterators` | （生成 scenario の `takeRecords`） | 同上 | 済 |

## normative branch の網羅（roadmap §11.3）

scenario の **件数** ではなく、対象 algorithm の各 normative branch に
固定 scenario があるかどうかを指標にする。

### ensure pre-insert validity

| step | 分岐 | 固定 scenario |
| --- | --- | --- |
| 1 | parent が Document / DocumentFragment / Element でない | `validity-step1-leaf-parent` |
| 2 | node が parent の inclusive ancestor | `childnode-before-leaks-backend-error`, `replacechildren-bypasses-validity` |
| 3 | child の parent が parent でない | `validity-step3-foreign-reference-child` |
| 4 | node の kind が四つのどれでもない | `replacewith-bypasses-validity` |
| 5 | parent が Document でなく node が doctype | `validity-step5-doctype-into-element` |
| 5 | parent が Document でなく node が doctype でない（通る） | `basic-insert-remove` |
| 6 | node が Text（parent は Document） | `childnode-after-bypasses-validity` |
| 7 | node が CharacterData（通る） | `validity-step7-comment-into-document` |
| 8 | fragment に element の子が二つ以上 | `validity-step8-fragment-two-elements` |
| 8 | fragment に Text の子がある | `validity-step8-fragment-text-child` |
| 8 | fragment に element の子が無い（通る） | `validity-step8-fragment-comments-only` |
| 8 | fragment に element の子が一つ（element の検査へ） | `validity-step8-fragment-one-element` |
| 9 | node が element（element の検査へ） | `validity-step9-first-document-element` |
| 9 | parent に除外されない element の子がある | `validity-step9-second-document-element` |
| 9 | child より後ろに doctype がある | `validity-step9-doctype-follows-child` |
| 9 | child が除外されない doctype である | `validity-step9-child-is-doctype` |
| 10-11 | parent に除外されない doctype の子がある | `validity-step11-second-doctype` |
| 10-11 | child より前に element がある | `validity-step11-element-precedes-child` |
| 10-11 | child が null で parent に element の子がある | `validity-step11-doctype-after-element` |
| 10-11 | doctype が入る（通る） | `doctype-wrapper-identity` |

### move の step 1-6

| step | 分岐 | 固定 scenario |
| --- | --- | --- |
| IDL | receiver が ParentNode でない | `move-receiver-must-be-parentnode`（差分比較の対象外） |
| 1 | root が違う | `move-step1-different-root` |
| 2 | cycle | `move-step2-cycle` |
| 3 | reference child が新しい parent の子でない | `move-step3-foreign-reference-child` |
| 4 | node が Element でも CharacterData でもない | `move-step4-doctype` |
| 5 | node が Text で新しい parent が Document | `move-step5-text-into-document` |
| 6 | Document に element を move する三条件 | `move-step6-second-document-element` |
| 7-24 | 成功して木・range・iterator が動く | `range-adjust-order-on-move` |

### live range / NodeIterator / CharacterData

| 分岐 | 固定 scenario |
| --- | --- |
| live range pre-remove steps | `iterator-adjust-on-remove` |
| live range の insert 側調整（`child` あり） | `range-adjust-order-on-before` |
| live range の insert 側調整（start ≤ end が壊れる） | `range-order-broken-by-insert` |
| NodeIterator pre-remove（pointerBefore が false） | `iterator-adjust-on-remove` |
| NodeIterator pre-remove（pointerBefore が true） | `iterator-adjust-pointer-before` |
| replace data の IndexSizeError と count の切り詰め | `characterdata-index-size-and-clamp` |
| replace data の boundary point 調整 | `characterdata-replace-data-ranges` |

**空欄の扱い。** 対象 algorithm の normative branch はすべて固定 scenario で押さえてある。
新しい分岐を model に足したら、この表に行を足してから実装する。

`comparable` が false の scenario は model 固有の近似を固定するためのもので、
差分比較の対象ではない。`_basis` にその旨を書く。

## 未対応と対象外

| 項目 | 扱い | 根拠 |
| --- | --- | --- |
| Shadow DOM（shadow-including root / slot） | 未対応 | roadmap の対象外。`move` step 1 は shadow-including root ではなく root で近似している |
| MutationObserver の callback 本体 | 対象外 | callback は model の外。`notifyMutationObservers` は「どの observer に何が配送されるか」を返すところまで |
| attribute（`attributes`, `attributeFilter`, `attributeOldValue`） | 対象外 | model に attribute が無い |
| custom element / insertion steps / removing steps | 対象外 | hook の位置だけを保っている |
| UTF-16 の code unit 境界 | 対象外 | roadmap §13.1。`data` は Lean の `String` |
| node 生成と可変長引数の変換 | 対象外 | roadmap §13.2。`convert nodes into a node` は呼び出し側で済ませた形で受け取る |
| object identity と戻り値 | 対象外 | roadmap §13.3。`Observation` に含めていない |
| NodeIterator の filter | 対象外 | roadmap §13.4 |
| WebIDL の TypeError | 一部 | `observe` の step 3 / 6 は `DOMException.typeError` で表す。`moveBefore` の receiver が ParentNode でない場合は HierarchyRequestError で代用する（`move-receiver-must-be-parentnode`） |

## 仕様改訂時の手順

1. `docs/spec-version.md` の commit から新しい commit までの `dom.bs` の差分を取る。
2. 差分に現れた algorithm 名でこの表を検索し、その行を review する。
3. step 要約が変わっていれば要約を直し、意味が変わっていれば evaluator と契約を直す。
4. 影響を受けた行の固定 scenario を再実行し、期待結果の根拠（`_note`）を更新する。
5. `docs/spec-version.md` の commit を進める。

step 番号だけを見て追従しないこと。番号は挿入・削除で簡単にずれる。
