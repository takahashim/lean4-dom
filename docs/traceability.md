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

**関係意味論（spec relation）は `remove` だけにある。** 本 model は長く
実行関数 `Except DOMException DOMState` そのものを意味論としてきた。
それだと仕様の翻訳を誤っても、その誤った関数についての定理は証明できてしまう。
そこで仕様本文から独立に書き写した関係を `Dom/Spec/` に置き、
実行関数がそれを満たすこと（soundness）を別に証明する層を作り始めた。
現状は下の表のとおり `remove` のみで、残りは実行関数が意味論のままである。

## §4.2.3 の関係意味論（`Dom/Spec/`）

| Algorithm | 関係 | soundness | completeness / determinism |
| --- | --- | --- | --- |
| remove | `Dom.Spec.RemoveSpec` | `Dom.Spec.remove_sound` | `Dom.Spec.removeSpec_deterministic`（観測の一意性） |
| insert | 未 | 未 | 未 |
| replace | 未 | 未 | 未 |
| move | 未 | 未 | 未 |
| replace data | 未 | 未 | 未 |

`RemoveSpec` は仕様の副作用ごとに六つの component に分かれていて、
soundness も component 単位で証明してある
（`RemovePre` / `RangeAdjusted` / `IteratorAdjusted` / `TreeRemoved` /
`TransientAdded` / `RecordQueued`）。
関係の側は実行側の algorithm（`liveRangePreRemove` / `detach` / `adjustNodePointer` /
`addTransientObservers` / `queueTreeMutationRecord`）を一切呼ばず、
`parentOf` / `childrenOf` / `ancestors` / `precedes` といった観測の語彙だけで書いてある。

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

## §4.4 `Node.normalize()`

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| normalize | 1 descendant exclusive Text を順に / 2 長さ 0 なら外す / 3-4 続く兄弟の data を足す / 5-6 live range の引き渡し / 7 兄弟を外す | `normalize`, `normalizeList`, `normalizeRun`, `normalizeMergeOne`, `normalizeMergeBP` | preservation `admissible_normalize`、`endpointsValid_normalizeMerge` | `normalize-merges-adjacent-text`, `normalize-record-order-per-sibling`, `normalize-empty-sibling-keeps-boundary`, `normalize-parent-boundary-moves-to-join`, `normalize-descends-into-subtree`, `normalize-moves-iterator-off-merged-text` | （Dommy に normalize の WPT 由来 test は無い） | 済（record は engine の読み） |

### normalize の分岐

| step | 分岐 | 固定 scenario |
| --- | --- | --- |
| 1 | descendant を tree order で辿る（子 element の中も） | `normalize-descends-into-subtree` |
| 2 | 長さ 0 の Text を外す | `normalize-merges-adjacent-text` |
| 3-4 | run の data を足す（兄弟ごと） | `normalize-record-order-per-sibling` |
| 3-4 | 空の兄弟は data の step を飛ばす | `normalize-empty-sibling-keeps-boundary` |
| 6.1-6.2 | 兄弟の中を指す boundary point | `normalize-merges-adjacent-text` |
| 6.3-6.4 | parent の中で兄弟の位置を指す boundary point | `normalize-parent-boundary-moves-to-join` |
| 7 | 外すので NodeIterator も動く | `normalize-moves-iterator-off-merged-text` |
| IDL | Node の method なので Text / Document でも呼べる | `normalize-on-text-is-noop`, `normalize-on-document`（Dommy 未実装なので比較は skip） |

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
| nextNode / previousNode（traverse） | traverse 1-6 | `nextNode`, `previousNode` | `validIterator_nextNode`, `validIterator_previousNode` | `iterator-adjust-pointer-before`, `iterator-whattoshow-skips` | `test_wpt_node_edges.rb` | 済（filter は null） |
| filter（`whatToShow`、filter は null） | filter 1-3 | `showsNode`, `NodeKind.nodeType` | 同上 | `iterator-whattoshow-skips` | 同上 | 済 |

## §5.5 `Range` の API（boundary point を動かす側）

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| set the start / set the end | 1 doctype / 2 offset / 3-5 反対の端の正規化 | `rangeSetStart`, `rangeSetEnd`, `setStartBP`, `setEndBP`, `rangeBoundaryError` | preservation `admissible_rangeSetStart` `admissible_rangeSetEnd` | `range-setstart-past-end-collapses`, `range-setstart-other-root-carries-range`, `range-setstart-errors` | `test_wpt_range_mutations.rb` | 済 |
| `setStartBefore` / `setStartAfter` / `setEndBefore` / `setEndAfter` | 1 parent / 2 null なら InvalidNodeTypeError / 3 set the start(end) | `rangeSetStartSibling`, `rangeSetEndSibling`, `siblingBP` | preservation `admissible_rangeSetStartSibling` ほか | `range-sibling-setters-and-collapse`, `range-boundary-needs-parent` | 同上 | 済 |
| `collapse(toStart)` | 1-2 | `rangeCollapse` | preservation `admissible_rangeCollapse` | `range-sibling-setters-and-collapse` | 同上 | 済 |
| `selectNode(node)` | 1 parent / 2 null なら InvalidNodeTypeError / 3-5 両端 | `rangeSelectNode` | preservation `admissible_rangeSelectNode` | `range-select-node-and-contents`, `range-boundary-needs-parent` | 同上 | 済 |
| `selectNodeContents(node)` | 1 doctype / 2-4 両端 | `rangeSelectNodeContents` | preservation `admissible_rangeSelectNodeContents` | 同上 | 同上 | 済 |
| `isPointInRange(node, offset)` | 1-5 | `rangeIsPointInRange` | — | `range-point-predicates` | 同上 | 済 |
| `intersectsNode(node)` | 1-6 | `rangeIntersectsNode` | — | 同上 | 同上 | 済 |
| `compareBoundaryPoints(how, source)` | 1 NotSupportedError / 2 WrongDocumentError / 3-4 位置 | `rangeCompareBoundaryPoints` | — | `range-compare-boundary-points` | 同上 | 済 |
| `comparePoint(node, offset)` | 1 WrongDocumentError / 2 doctype / 3 offset / 4-6 位置 | `rangeComparePoint` | — | 同上 | 同上 | 済 |

## §5.5 `Range` の API（木を変える側）

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `deleteContents()` | 1 collapsed / 3 同じ CharacterData / 4 nodes to remove / 5-6 新しい端点 / 7-9 削除と切り詰め / 10 両端 | `rangeDeleteContents`, `nodesToRemove`, `containedInRange`, `deleteContentsNewBP` | preservation `admissible_rangeDeleteContents`（step 10 の端点は実行時検査） | `range-delete-contents-within-text`, `-across-nodes`, `-ancestor-start`, `-collapsed-is-noop`, `range-delete-contents-partially-contained-end`, `-start` | `test_wpt_range_contents.rb` | 済 |
| `insertNode(node)` | 1 HierarchyRequestError / 4-5 referenceNode と parent / 6 pre-insert validity / 8-9 referenceNode と remove / 10-11 newOffset / 12 pre-insert / 13 collapsed なら end | `rangeInsertNode` | preservation `admissible_rangeInsertNode`, `validBoundaryPoint_of_siblingBP` | `range-insert-node-wraps-inserted`, `-fragment`, `-errors`, `-self-is-hierarchy-error`, `-moves-preceding-sibling`, `-start-text-is-self`, `-detached-text-start` | 同上 | 済（step 7 の split text は対象外） |

`extractContents` / `cloneContents` / `surroundContents` / `cloneRange` は node を生むので
roadmap §13.2 の対象外である。`insertNode` の step 7（start node が Text なら split する）も
同じ理由で対象外で、model は `__outsideModel__` を返す
（`range-insert-node-into-text-is-outside-model`）。

## §2.7 EventTarget / §2.9 event の配送

callback は model の外だが、**何をするか**は scenario が `ListenerAction` として宣言する。
そうすると「どの listener がどの順で呼ばれたか」が model で決まるので、
差分テストはその列（`invocations`）を比べる。

shadow tree が無いので retargeting も composed path も要らず、event path は
target から根までの祖先列そのものである。`Window` が無いので Document の
"get the parent" は null、activation behavior（`click` の既定動作）は HTML 側の hook なので
扱わない。`isTrusted` は常に false なので legacy な type の付け替えも起きない。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| dispatch | 1-5, 12-13, 14-18 | `dispatchEvent`, `eventPath`, `runPass` | `admissible_dispatchEvent`, `listenersOnly_dispatchEvent` | `event-dispatch-phases`, `event-dispatch-at-character-data-target` | `test_wpt_event_dispatch.rb` | 済（shadow / activation は対象外） |
| invoke | 1-9 | `invokeItem` | 同上 | `event-listener-flags` | 同上 | 済 |
| inner invoke | 1-3 | `innerInvoke`, `invokeOne` | 同上 | 同上 | 同上 | 済 |
| add an event listener / `addEventListener` | add 5 | `addListener`, `addEventListener` | `admissible_addEventListener` | `event-listener-add-and-remove` | 同上 | 済（`signal` / `passive` は対象外） |
| remove an event listener / `removeEventListener` | remove 2 | `removeListenerAt`, `removeEventListener` | `admissible_removeEventListener` | 同上 | 同上 | 済 |
| `stopPropagation` / `stopImmediatePropagation` / `preventDefault` | — | `runAction` | 同上 | `event-listener-flags` | 同上 | 済 |

## §4.4 値を返すだけの `Node` の method / §4.9 attribute の getter / §5.5 stringifier

木も live object も変えないので、差分テストでは戻り値だけを比べる。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `compareDocumentPosition(other)` | 1, 6-10 | `compareDocumentPosition` | `compareDocumentPosition_disconnected_consistent` | `node-query-position-and-containment`, `compare-document-position-disconnected-is-consistent` | `test_wpt_node_edges.rb` | 済（attribute の step 3-5 は対象外） |
| `contains(other)` / `getRootNode()` | — | `nodeContains`, `getRootNode` | — | `node-query-position-and-containment` | 同上 | 済（`composed` は対象外） |
| `equals` / `isEqualNode(other)` | equals | `nodeEquals`, `nodeOwnPropertiesEqual`, `attrEquals` | — | `node-query-is-equal-node` | 同上 | 済（DocumentType の name ほかは対象外） |
| get text content / `textContent` getter | — | `getTextContent`, `descendantTextContent` | — | `node-query-text-content` | 同上 | 済（setter は node を作るので対象外） |
| `nodeValue` getter | — | `getNodeValue` | — | 同上 | 同上 | 済 |
| substring data / `substringData(offset, count)` | 1-4 | `substringData` | — | `characterdata-substring-data`, `-index-size` | `test_wpt_character_data.rb` | 済 |
| `getAttribute` / `hasAttribute` / `getAttributeNames` | 1-2 ほか | `getAttribute`, `hasAttribute`, `getAttributeNames`, `attrNameFor` | — | `attribute-getters` | `test_wpt_attributes.rb` | 済 |
| `Range` の stringifier | 1-6 | `rangeToString` | — | `range-to-string`, `-within-one-text` | `test_wpt_range_contents.rb` | 済 |
| locate a namespace / `lookupNamespaceURI(prefix)` | Element 1-6 / Document 1-2 / lookupNamespaceURI 1-2 | `locateNamespace`, `locateNamespaceIn`, `elementChain` | — | `namespace-lookup-chain`, `namespace-lookup-edges` | `test_wpt_node_namespace.rb` | 済（Attr は対象外） |
| locate a namespace prefix / `lookupPrefix(namespace)` | 1-4 / lookupPrefix 1-2 | `lookupPrefix`, `locateNamespacePrefixIn` | — | 同上 | 同上 | 済 |
| `isDefaultNamespace(namespace)` | 1-3 | `isDefaultNamespace` | — | 同上 | 同上 | 済 |

`compareDocumentPosition` の step 6（同じ木にない）は PRECEDING と FOLLOWING の
どちらを返すかを実装に任せている。差分テストはその二 bit を落として比べる
（`test/compare.rb` の `normalize_returned`）。一貫性そのものは model 側の定理で見る。

## §6.2 TreeWalker

filter は null なので、"filter" は FILTER_ACCEPT か FILTER_SKIP しか返さない。
FILTER_REJECT が出ないぶん、仕様の pointer 走査は
「tree order（あるいはその鏡像 `mirrorPreorder`）に並べた候補列を、
先頭から accept されるまで見る」ことに等しい。model はその形で書いてある。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `nextNode()` | 3.1-3.5 | `walkerNextNode`, `walkerBase` | `exists_data_of_walkerNextNode` | `walker-basic-traversal`, `walker-not-adjusted-by-remove` | `test_wpt_tree_walker.rb` | 済（filter は null） |
| `previousNode()` | 2.1-2.5 | `walkerPreviousNode` | `exists_data_of_walkerPreviousNode` | 同上 | 同上 | 済 |
| `parentNode()` | 1-3 | `walkerParentNode`, `takeUntilIncl` | `exists_data_of_walkerParentNode` | `walker-parent-node-leaves-root` | 同上 | 済 |
| `firstChild()` / `lastChild()`（traverse children） | 1-4 | `walkerFirstChild`, `walkerLastChild`, `mirrorPreorder` | `exists_data_of_walkerFirstChild` ほか | `walker-whattoshow-skips`, `walker-last-child-mirrors-order` | 同上 | 済 |
| `nextSibling()` / `previousSibling()`（traverse siblings） | 1-3 | `walkerSibling`, `walkerSiblingSearch`, `siblingCandidates` | `exists_data_of_walkerSibling` | 同上 | 同上 | 済 |
| filter（`whatToShow`、filter は null） | filter 1-3 | `walkerAccepts`, `showsNode` | — | `walker-whattoshow-skips` | 同上 | 済 |
| walker の保存 | — | `walkerStep` | `walkersValid_walkerStep`, `admissible_walkerStep` | — | — | 済 |

`currentNode` の setter は scenario の初期状態（`walkers` の `current`）としてだけ使える。
`TreeWalker` を作る API（`createTreeWalker`）は object を生むので roadmap §13.2 の対象外で、
scenario が最初から walker を与える形にしてある。

## §4.3 MutationObserver

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| queue a mutation record | 1-2 inclusive ancestor を辿って observer を集める / 2.3 registration ごとの条件（型・scope・attributeFilter）/ 2.3.3 oldValue / 3-6 record を積む | `queueMutationRecord`, `interestedObservers`, `Registration.interestedIn` | preservation `preservesRegs_*` | `observer-uninterested-registration-does-not-shadow`, `observer-attribute-filter-does-not-shadow`, `observer-old-value-from-any-registration` | `test_wpt_mutation_record_details.rb`, `test_wpt_mutation_observer_order.rb`, `test_wpt_mutation_observer_attribute_options.rb` | 済 |
| queue a tree mutation record | 1 assert / 2 queue | `queueTreeMutationRecord` | 同上 | 同上 | `test_wpt_mutation_record_insertion_point.rb` | 済 |
| transient registered observer | remove step 20 | `addTransientObservers` | `preservesRegs_remove` | `observer-transient-follows-existing-registration` | `test_wpt_transient_registered_observer.rb` | 済 |
| queue a mutation observer microtask | 1-3 | `queueMutationObserverMicrotask`, `addPendingObserver` | preservation `admissible_*`（配送は木を触らない） | `observer-delivery` | `test_wpt_mutation_observer_order.rb` | 済 |
| notify mutation observers | 1-5 | `notifyMutationObservers`, `notifyEach`, `notifyOne`, `removeTransients` | `admissible_notifyMutationObservers`, `notifyMutationObservers_tree/_ranges/_iterators` | 同上 | 同上 | 済 |
| `observe(target, options)` | 1-8（step 1-2 の省略の解決と step 3-6 の TypeError を含む） | `MutationObserver.observe`, `MutationObserverInit.resolve`, `observeOptionsError` | `admissible_observe`, `observe_tree/_ranges/_iterators` | `observer-uninterested-registration-does-not-shadow` | 同上 | 済 |
| `disconnect()` | 1-2 | `MutationObserver.disconnect` | `admissible_disconnect`, `disconnect_tree/_ranges/_iterators` | （生成 scenario の `disconnect`） | 同上 | 済 |
| `takeRecords()` | 1-3 | `MutationObserver.takeRecords` | `admissible_takeRecords`, `takeRecords_tree/_ranges/_iterators` | （生成 scenario の `takeRecords`） | 同上 | 済 |

## §4.9 Attr / §1.3 名前の検査

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| valid namespace prefix / valid attribute local name | §1.3 | `isValidNamespacePrefix`, `isValidAttributeLocalName` | — | （生成 scenario の `setAttributeNS`） | `test_wpt_attr.rb` | 済 |
| validate and extract（"attribute"） | 1-12 | `validateAndExtractAttribute`, `validateAndExtractError` | `validateAndExtractAttribute_ok`（step 1 と step 8） | 同上 | 同上 | 済 |
| get an attribute by name | 1-2 | `getAttributeByName`, `attrNameFor` | `setAttribute_getAttribute` | `attribute-by-name-uses-qualified-name`, `attribute-name-case-follows-namespace` | `test_wpt_attribute_qualified_name.rb` | 済 |
| valid element local name | §1.3 | `isValidElementLocalName` | — | （loader が検査する） | — | 済 |
| `Element.tagName` | §4.8 | `tagName` | — | `attribute-name-case-follows-namespace` | `test_wpt_attribute_qualified_name.rb` | 済 |
| get an attribute by namespace and local name | 1-2 | `getAttributeByKey` | — | （生成 scenario の `removeAttributeNS`） | 同上 | 済 |
| handle attribute changes | 1（2-3 は hook の位置のみ） | `handleAttributeChanges` | preservation `admissible_setAttribute` ほか | `observer-attribute-filter-does-not-shadow` | `test_wpt_mutation_observer_attribute_options.rb` | 済 |
| change an attribute | 1-3 | `changeAttribute` | `attributesValid_change` | 同上 | 同上 | 済 |
| append an attribute | 1-4 | `appendAttribute` | `attributesValid_append` | 同上 | 同上 | 済 |
| remove an attribute | 1-4 | `removeAttributeFrom` | `attributesValid_erase`, `removeAttribute_erases` | `attribute-by-name-uses-qualified-name` | `test_wpt_attribute_qualified_name.rb` | 済 |
| set an attribute value | 1-3 | `setAttributeValue` | `attrOpResult_setAttributeValue` | （生成 scenario の `setAttributeNS`） | `test_wpt_attr.rb` | 済 |
| `setAttribute(qualifiedName, value)` | 1-2, 4-7（step 3 は Trusted Types なので非対象） | `setAttribute`, `attrNameFor` | `admissible_setAttribute`, `setAttribute_getAttribute` | `attribute-by-name-uses-qualified-name`, `attribute-name-case-follows-namespace` | `test_wpt_attribute_qualified_name.rb` | 済 |
| `setAttributeNS(namespace, qualifiedName, value)` | 1, 3（step 2 は Trusted Types なので非対象） | `setAttributeNS` | `admissible_setAttributeNS` | （生成 scenario） | `test_wpt_attr.rb` | 済 |
| `removeAttribute` / `removeAttributeNS` | 全 | `removeAttribute`, `removeAttributeNS` | `admissible_removeAttribute`, `admissible_removeAttributeNS` | `attribute-by-name-uses-qualified-name` | `test_wpt_attribute_qualified_name.rb` | 済 |
| `toggleAttribute(qualifiedName, force)` | 1-6 | `toggleAttribute`, `attrNameFor` | `admissible_toggleAttribute` | 同上 | 同上 | 済 |

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
| IDL | receiver が ParentNode でない（TypeError） | `move-receiver-must-be-parentnode`（差分比較の対象外） |
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
| `Attr` を node として扱う API（`setAttributeNode`、`attributes` の `NamedNodeMap`、"set an attribute" と "replace an attribute"） | 対象外 | model の attribute は element の状態で、node tree に入らない |
| ProcessingInstruction の attribute map（§4.11 の `setAttribute` ほか） | 対象外 | element の attribute list とは別の仕組みで、attribute の mutation record を積まない。Dommy も未実装なので差分テストで裏を取れない |
| custom element / insertion steps / removing steps | 対象外 | hook の位置だけを保っている |
| UTF-16 の lone surrogate | 部分モデル | roadmap §13.1。長さと offset は code unit で数える（`Dom/Basic/Utf16.lean`）。surrogate pair を割った切り出しだけは Lean の `Char` で表せないので `DOMException.outsideModel` を返し、差分テストはその step 以降を比較しない。boundary point が pair の途中を指すことは扱える |
| node 生成と可変長引数の変換 | 対象外 | roadmap §13.2。node は scenario が初期状態として与える（element の namespace と local name も含めて）。`convert nodes into a node` は呼び出し側で済ませた形で受け取る |
| method の戻り値 | 済 | `returnValueOf`（`Dom/Exec/Eval.lean`）。`Node?` / boolean / record 列を kind つきで観測する。`undefined` と `null` は区別する |
| wrapper の object identity | 対象外 | roadmap §13.3。model は node を生成しないので wrapper を作る API の同一性は観測できない。node を返す method の戻り値は `NodeId` で比べるので「返ってきたのは渡した node そのものか」は観測できる |
| `normalize()` の record の並び | engine に合わせた | 仕様を字義どおり読むと run ごとに characterData が一つだが、Blink・WebCore・Gecko は兄弟ごとに積む。WPT が固定しているのは childList の側だけである。木と live range の最終状態はどちらの読みでも同じ |
| `Attr` の identity | 対象外 | `setAttributeNode` / `NamedNodeMap` / `InUseAttributeError` が要求する。attribute は element の状態なので object にならない |
| `NodeFilter` の callback | 対象外 | roadmap §13.4。callback は model の外なので filter は常に null。`whatToShow` は純粋なので扱う |
| WebIDL の TypeError | 近似 | `observe` の step 3-6、attribute の method の receiver が Element でない場合、`moveBefore` の receiver が ParentNode でない場合（`move-receiver-must-be-parentnode`）を `DOMException.typeError` で表す。名前は一致するが実際には `DOMException` ではない |

## 仕様改訂時の手順

1. `docs/spec-version.md` の commit から新しい commit までの `dom.bs` の差分を取る。
2. 差分に現れた algorithm 名でこの表を検索し、その行を review する。
3. step 要約が変わっていれば要約を直し、意味が変わっていれば evaluator と契約を直す。
4. 影響を受けた行の固定 scenario を再実行し、期待結果の根拠（`_note`）を更新する。
5. `docs/spec-version.md` の commit を進める。

step 番号だけを見て追従しないこと。番号は挿入・削除で簡単にずれる。
