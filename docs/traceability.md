# 仕様トレーサビリティ

WHATWG DOM Standard の algorithm と、Lean の実行関数・契約・固定 scenario・
Dommy 側の WPT 由来 test を結ぶ対応表である。

参照する仕様は `docs/spec-version.md` に固定した commit
`a2331a45360129e8645ef7e0a04740241b6e3726`（2026-08-25）である。
step 番号だけに頼ると仕様改訂でずれるので、各行に短い step 要約も置く。

step 単位の対応は `Trace/Dom/` の表が持ち、CI が網羅を検査する。algorithm ごとの集計は
自動生成の `docs/spec-coverage.md` にある。この文書の step 要約と、Lean のコメントにある step 番号は
人が書いたもので、固定版より前の番号が残っていることがある（`docs/spec-version.md`）。

## 読み方

| 列 | 内容 |
| --- | --- |
| Evaluator | `Dom/Mutation/` などの実行関数 |
| Contracts | preservation / success / exception / effect / frame の定理名 |
| Scenario | `test/scenarios/` の固定 scenario |
| WPT | Dommy 側の WPT 由来 test（`gems/dommy/test/wpt/`） |
| Status | 済 / 部分 / 未 |

**関係意味論（spec relation）は §4.2.3 の中核と §4.5 / §4.10 にある。** 本 model は長く
実行関数 `Except DOMException DOMState` そのものを意味論としてきた。
それだと仕様の翻訳を誤っても、その誤った関数についての定理は証明できてしまう。
そこで仕様本文から独立に書き写した関係を `Dom/Spec/` に置き、
実行関数がそれを満たすこと（soundness）を別に証明する層を作った。
下の表に無い algorithm は、まだ実行関数が意味論のままである。

## §4.2.3 の関係意味論（`Dom/Spec/`）

| Algorithm | 関係 | soundness | 一意性 | completeness |
| --- | --- | --- | --- | --- |
| remove | `Dom.Spec.RemoveSpec` | `remove_sound` | `removeSpec_deterministic` / `removeSpec_congr` | `remove_complete` |
| adopt（§4.5） | `Dom.Spec.AdoptSpec` | `adopt_sound` | `adoptSpec_deterministic` / `adoptSpec_congr` | `adopt_complete` |
| insert | `Dom.Spec.InsertSpec` | `insert_sound` | `insertSpec_deterministic` / `insertSpec_congr` | `insert_complete` |
| replace | `Dom.Spec.ReplaceSpec` | `replace_sound` | `replaceSpec_deterministic` / `replaceSpec_congr` | `replace_complete` |
| move（§4.2.4） | `Dom.Spec.MoveSpec` | `move_sound` | `moveSpec_deterministic` / `moveSpec_congr` | `move_complete` |
| replace data（§4.10） | `Dom.Spec.ReplaceDataSpec` | `replaceData_sound` | `replaceDataSpec_deterministic` / `replaceDataSpec_congr` | `replaceData_complete` |
| normalize（§4.4） | `Dom.Spec.NormalizeSpec` | `normalize_sound` | `normalizeSpec_deterministic` / `normalizedEach_congr` | `normalize_isOk`（`this` が木にあれば成功） |
| replace all | `Dom.Spec.ReplaceAllSpec` | `replaceAll_sound` | `replaceAllSpec_deterministic` | `replaceAll_isOk`（step 5 の事実があれば成功） |
| ensure pre-insert validity | `Dom.Spec.PreInsertValidity` | `ensurePreInsertionValidity_spec`（仮定なし） | `preInsertValidity_deterministic` | `preInsertValidity_iff` |
| move の pre-move validity（§4.2.4） | `Dom.Spec.MoveValidity` | `moveValidity_spec`（仮定なし） | `moveValidity_deterministic` | `moveValidity_iff` |
| pre-insert（結果込み） | `Dom.Spec.PreInsertResult` | `preInsert_result_sound` | `preInsert_result_deterministic` | `preInsert_result_complete` |
| remove（結果込み） | `Dom.Spec.RemoveResult` | `remove_result_sound` | `remove_result_deterministic` | `remove_result_complete` |
| replace（結果込み） | `Dom.Spec.ReplaceResult` | `replace_result_sound` | `replace_result_deterministic` | `replace_result_complete` |
| moveBefore（結果込み） | `Dom.Spec.MoveResult` | `move_result_sound` | `move_result_deterministic` | `move_result_complete` |
| normalize（結果込み） | `Dom.Spec.NormalizeResult` | `normalize_result_sound` | `normalize_result_deterministic` | `normalize_result_complete` |
| Range `deleteContents()`（結果込み、§5.5） | `Dom.Spec.DeleteContentsResult` | `rangeDeleteContents_result_sound`（`RangeValid` を仮定） | `deleteContents_result_deterministic` | `rangeDeleteContents_result_complete` |
| Range `insertNode(node)`（結果込み、§5.5） | `Dom.Spec.InsertNodeResult` | `rangeInsertNode_result_sound`（`RangeValid` を仮定） | `insertNode_result_deterministic` | `rangeInsertNode_result_complete` |
| `dispatchEvent`（結果込み、§2.9） | `Dom.Spec.DispatchResult` | `dispatchEvent_result_sound` | `dispatchEvent_result_deterministic`（等号） | `dispatchEvent_result_complete`（等号） |
| `addEventListener` / `removeEventListener`（結果込み、§2.7） | `Dom.Spec.AddEventListenerResult` / `RemoveEventListenerResult` | `addEventListener_result_sound` / `removeEventListener_result_sound` | complete から | `addEventListener_result_complete` / `removeEventListener_result_complete`（等号） |
| `setAttribute` / `setAttributeNS` の step 2 以降 / `removeAttribute(NS)` / `toggleAttribute`（結果込み、§4.9） | `Dom.Spec.SetAttributeResult` ほか（`AttributeChanged`・`AttributeAppended`・`AttributeRemoved`・`AttributeRecordQueued`） | `setAttribute_result_sound` ほか（`AttributesValid` を仮定） | `setAttribute_result_deterministic` ほか | `setAttribute_result_complete` ほか |
| `setAttributeNode` / `removeAttributeNode` / `NamedNodeMap.removeNamedItem`（結果込み、§4.9） | `Dom.Spec.SetAttributeNodeResult` ほか（`AttrLocated`・`AttributeReplacedWith`・`AttributeDetached`） | `setAttributeNode_result_sound` ほか（`AttributesValid` と `AttrIdsUnique` を仮定） | `setAttributeNode_result_deterministic` ほか | `setAttributeNode_result_complete` ほか |
| replaceChildren（結果込み、§4.2.6） | `Dom.Spec.ReplaceChildrenResult` | `replaceChildren_result_sound` | `replaceChildren_result_deterministic` | `replaceChildren_result_complete` |
| before（結果込み、§4.2.9） | `Dom.Spec.BeforeResult`（`ViablePreviousSibling`） | `before_result_sound` | `before_result_deterministic` | `before_result_complete` |
| after（結果込み、§4.2.9） | `Dom.Spec.AfterResult`（`ViableNextSibling`） | `after_result_sound` | `after_result_deterministic` | `after_result_complete` |
| replaceWith（結果込み、§4.2.9） | `Dom.Spec.ReplaceWithResult` | `replaceWith_result_sound` | `replaceWith_result_deterministic` | `replaceWith_result_complete` |
| `remove()`（結果込み、§4.2.9） | `Dom.Spec.NodeRemoveResult` | `nodeRemove_result_sound` | `nodeRemove_result_deterministic` | `nodeRemove_result_complete` |
| replace data（結果込み） | `Dom.Spec.ReplaceDataResult` | `replaceData_result_sound` | `replaceData_result_deterministic` | `replaceData_result_complete` |
| appendData / setData（結果込み） | `Dom.Spec.AppendDataResult` / `SetDataResult` | `appendData_result_sound` / `setData_result_sound` | `replaceData_result_deterministic` に帰着 | `appendData_result_complete` / `setData_result_complete` |
| insertData / deleteData（結果込み） | `Dom.Spec.ReplaceDataResult`（引数を固定） | `insertData_result_sound` / `deleteData_result_sound` | 同上 | `insertData_result_complete` / `deleteData_result_complete` |

定理はすべて `Dom.Spec` 名前空間にある。「結果込み」の行は**例外まで含めた**関係で、
soundness が `= .ok s'` を仮定しない（`Dom/Spec/Result.lean`）。`replace` の
失敗側は `preInsert` と同じ `PreInsertValidity` を使い回す（`replace` の step 1 が
`ensurePreInsertionValidity` そのものであるため）。`move` は条件の語彙が違うので
使い回せず、`Dom/Spec/MoveValidity.lean` に独立な `MoveValidity` を別に置いた。
`moveBefore` は receiver 自身の失敗（木に無い・`ParentNode` でない）が二つある分、
`MoveResult` の失敗側は三枝になる。

`normalize` の関係（`Dom/Spec/Normalize.lean`）は、兄弟ごとに「data を足す・boundary point を
渡す・外す」を繰り返す engine の読みで書く（record の並びがそれで決まる）。
step 3 と step 7 の「contiguous exclusive Text nodes」は後ろ側だけを使う。
tree order で処理すると、前側は処理の時点で残っていないからである。

`ChildNode` / `ParentNode` の method と `CharacterData` の method は、仕様が
pre-insert・replace・remove・replace all・replace data への委譲として書いているので、
委譲の前の手順（parent が無ければ何もしない、viable sibling、reference child、
step 2 の validity）だけを仕様の語彙で書き、委譲先は上の関係をそのまま使う
（`Dom/Spec/ChildNode.lean`、`Dom/Spec/ReplaceAllSound.lean`、`Dom/Spec/CharacterDataResult.lean`）。
`replaceWith` の step 6（pre-insert に回る枝）は、model では step 4 の変換が木を変えないので通らない。

Range の `deleteContents()` と `insertNode()` は、`this` が live range として妥当（start と end が
同じ木にあり、start が end の前か等しい）であることを仮定する。admissible な状態は
range の両端が木にあることしか保証しないので、仮定として受け取る。
`insertNode` の step 7（Text の split）は model の対象外で、関係は step 6 の validity を通れば
`outsideModel` を返すとする。ここでの「Text」は CDATASection を含む。

**一意性は観測の上で述べる。** 木の store は association list なので、
同じ `get?` を持つ表現が複数ある。そこで結論は `Dom.Spec.ObsEq`
（木は `get?`、registered observer は所属、observer は record queue）の一致である。

`insert` のように関係を繋いだものの一意性には、`_deterministic` だけでは足りない。
途中の状態は観測としてしか一致しないので、
「入力の観測が等しければ出力の観測も等しい」（`_congr`）を段ごとに使う。

**completeness は二つに分かれる。** 「関係を満たす状態は実行関数の結果と観測が等しい」
（余計な model が無い）と、「関係が満たせるなら実行関数は失敗しない」（実現できる）である。
前者は soundness と一意性から出る。後者は契約（`Dom/Properties/Contract.lean`）から出る。
`insert` は後者がまだ無い。`insertAt` の step 4（`child` が `parent` の子であること）を
関係が述べていないためで、仕様でもその検査は呼び出し側（pre-insert）にある。

record を積む step は種類ごとに切り出してある。childList（`remove` の step 21 と
`insert` の step 4.2 / 9）は `Dom.Spec.TreeRecordQueued`、characterData
（`replace data` の step 4）は `Dom.Spec.CharacterDataRecordQueued` である。
後者は oldValue が載る条件（interested な registration のどれかが
`characterDataOldValue` を持つこと）まで書いてある。

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
| pre-insert | 1 validity / 2-3 reference child のずらし / 4 insert | `preInsert` | success `preInsert_succeeds_iff`、exception `preInsert_error_iff`、preservation `admissible_preInsert`、委譲 `insertBefore_refines_preInsert`、reference child `ensurePreInsertionValidity_shift` | 同上 | `test_wpt_node_mutation.rb` | 済 |
| insert | 1-3 nodes と count / 4 fragment の children を外す / 5 live range の offset 調整 / 6 previousSibling / 7 adopt して入れる / 9 record | `insert`, `insertNodesAt`, `insertEachAt`, `insertEach` | preservation `admissible_insert`、success `insert_isOk_of_validity`（`Insertable`）、effect `insert_parentOf` `insert_children_split` `insert_preserves_endpoints`、frame `insertAt_frame`、negative `exists_insert_breaking_boundaryLE` | `basic-insert-remove`, `range-adjust-order-on-before`, `range-order-broken-by-insert` | `test_wpt_live_range_insert_order.rb`, `test_wpt_mutation_record_insertion_point.rb` | 済 |
| append | 1 pre-insert(child=null) | `append` | success `append_succeeds_iff`、委譲 `append_refines_preInsert`、preservation `admissible_append` | `basic-insert-remove` | `test_wpt_node_mutation.rb` | 済 |
| remove | 1-2 parent の assert / 3 live range の pre-remove / 4 NodeIterator の pre-remove / 14 children から外す / 20 transient observer / 21 record | `remove`, `detachWithLiveAdjust`, `detach` | preservation `admissible_remove`、success `remove_succeeds_iff`、exception `remove_error_iff`、effect `remove_parentOf` `remove_not_mem_childrenOf` `remove_ranges` `remove_iterators`、frame `detach_frame` | `basic-insert-remove`, `iterator-adjust-on-remove`, `iterator-adjust-pointer-before` | `test_wpt_mutation_primitives.rb`, `test_wpt_transient_registered_observer.rb` | 済 |
| pre-remove | 1 parent の一致 / 2 remove | `preRemove` | success `preRemove_succeeds_iff`、exception `preRemove_error_iff` `preRemove_error_notFound`、委譲 `removeChild_refines_preRemove` | `basic-insert-remove` | `test_wpt_node_methods_on_every_node.rb` | 済 |
| replace | 1 validity(child を除外) / 2-3 reference child / 4 previousSibling / 6 adopt / 7 child を外す / 9 insert / 10 record | `replace` | success `replace_succeeds_iff`、exception `replace_error_iff`、preservation `admissible_replace`、exception `replace_cycle_precedes_notFound`、effect `replace_reference_head` | `replacewith-bypasses-validity` | `test_wpt_mutation_record_insertion_point.rb` | 済 |
| replace all | 1-3 removedNodes と addedNodes / 4 children を全部外す / 5 insert / 7 record | `replaceAll` | relation `ReplaceAllSpec`、success `replaceAll_isOk`、preservation `admissible_replaceAll`、effect `removeEach_childrenOf_nil` | `replacechildren-bypasses-validity` | `test_wpt_node_mutation.rb` | 済 |
| move | 1 同じ root / 2 cycle / 3 reference child / 4 node の kind / 5 Text と Document / 6 Document の element と doctype / 10-11 pre-remove / 14 外す / 16 offset 調整 / 18 入れる / 23-24 record | `move`, `moveValidity`, `moveBefore` | preservation `admissible_move` `admissible_moveBefore`、success `moveBefore_succeeds_iff` `move_isOk_of_validity`、exception `moveBefore_error_iff` `moveBefore_error_receiver`、exception 順序 `moveValidity_step1`〜`_step4`、step 7-9 の assert `moveValidity_parentOf_isSome`、effect `move_eq_remove_insertAt` `move_parentOf` `move_childrenOf` `move_ranges` `move_iterators` | `range-adjust-order-on-move` | `test_wpt_move_before.rb` | 済 |

## §4.4 `Node.normalize()`

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| normalize | 1 descendant exclusive Text を順に / 2 長さ 0 なら外す / 3-4 続く兄弟の data を足す / 5-6 live range の引き渡し / 7 兄弟を外す | `normalize`, `normalizeList`, `normalizeRun`, `followingTexts`, `normalizeMergeOne`, `normalizeMergeBP` | relation `NormalizeResult`（兄弟ごとの読み）、success `normalize_isOk`、preservation `admissible_normalize`、`endpointsValid_normalizeMerge` | `normalize-merges-adjacent-text`, `normalize-record-order-per-sibling`, `normalize-empty-sibling-keeps-boundary`, `normalize-parent-boundary-moves-to-join`, `normalize-descends-into-subtree`, `normalize-moves-iterator-off-merged-text` | （Dommy に normalize の WPT 由来 test は無い） | 済（record は engine の読み） |

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
| replace data | 1-2 IndexSizeError / 3 count の切り詰め / 4 record / 5-7 data の差し替え / 8-11 live range の調整 | `replaceData` と `appendData` / `insertData` / `deleteData` / `setData` | relation `ReplaceDataResult`（success と exception を含む）、preservation `admissible_replaceData` ほか四つ、effect `replaceData_ok` | `characterdata-index-size-and-clamp`, `characterdata-replace-data-ranges` | `test_wpt_character_data.rb` | 済 |

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
| set the start / set the end | 1 doctype / 2 offset / 3-5 反対の端の正規化 | `rangeSetStart`, `rangeSetEnd`, `setStartBP`, `setEndBP`, `rangeBoundaryError` | relation `SetStartResult` / `SetEndResult`（`StartSet`・`EndSet`、`RangeValid` を仮定、等号で complete）、preservation `admissible_rangeSetStart` `admissible_rangeSetEnd` | `range-setstart-past-end-collapses`, `range-setstart-other-root-carries-range`, `range-setstart-errors` | `test_wpt_range_mutations.rb` | 済 |
| `Node` 引数の変換（WebIDL） | 引数変換は method の step より先 / `Range` の `Node` は non-nullable | `Operation` の `Option Nat`、`Dom.Exec.withNode` | — | `range-null-node-argument` | `test_range_node_arguments.rb` | 済 |
| `setStartBefore` / `setStartAfter` / `setEndBefore` / `setEndAfter` | 1 parent / 2 null なら InvalidNodeTypeError / 3 set the start(end) | `rangeSetStartSibling`, `rangeSetEndSibling`, `siblingBP` | relation `SetStartSiblingResult` / `SetEndSiblingResult`、preservation `admissible_rangeSetStartSibling` ほか | `range-sibling-setters-and-collapse`, `range-boundary-needs-parent` | 同上 | 済 |
| `collapse(toStart)` | 1-2 | `rangeCollapse` | relation `CollapseResult`、preservation `admissible_rangeCollapse` | `range-sibling-setters-and-collapse` | 同上 | 済 |
| `selectNode(node)` | 1 parent / 2 null なら InvalidNodeTypeError / 3-5 両端 | `rangeSelectNode` | relation `SelectNodeResult`、preservation `admissible_rangeSelectNode` | `range-select-node-and-contents`, `range-boundary-needs-parent` | 同上 | 済 |
| `selectNodeContents(node)` | 1 doctype / 2-4 両端 | `rangeSelectNodeContents` | relation `SelectNodeContentsResult`、preservation `admissible_rangeSelectNodeContents` | 同上 | 同上 | 済 |
| `isPointInRange(node, offset)` | 1-5 | `rangeIsPointInRange` | `Spec.rangeIsPointInRange_eq_iff`（`Dom/Spec/RangeQuery.lean`、例外込み） | `range-point-predicates` | 同上 | 済 |
| `intersectsNode(node)` | 1-6 | `rangeIntersectsNode` | `Spec.rangeIntersectsNode_eq_iff`（同上） | 同上 | 同上 | 済 |
| `compareBoundaryPoints(how, source)` | 1 NotSupportedError / 2 WrongDocumentError / 3-4 位置 | `rangeCompareBoundaryPoints` | `Spec.rangeCompareBoundaryPoints_eq_iff`（同上） | `range-compare-boundary-points` | 同上 | 済 |
| `comparePoint(node, offset)` | 1 WrongDocumentError / 2 doctype / 3 offset / 4-6 位置 | `rangeComparePoint` | `Spec.rangeComparePoint_eq_iff`（同上） | 同上 | 同上 | 済 |

## §5.5 `Range` の API（木を変える側）

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `deleteContents()` | 1 collapsed / 3 同じ CharacterData / 4 nodes to remove / 5-6 新しい端点 / 7-9 削除と切り詰め / 10 両端 | `rangeDeleteContents`, `nodesToRemove`, `containedInRange`, `deleteContentsNewBP` | relation `DeleteContentsResult`（`Contained`・`NodesToRemove`・`DeleteNewBP`）、step 10 の端点の妥当性 `deleteContentsNewBP_valid`（妥当な range では実行時検査の fallback に落ちない）、preservation `admissible_rangeDeleteContents` | `range-delete-contents-within-text`, `-across-nodes`, `-ancestor-start`, `-collapsed-is-noop`, `range-delete-contents-partially-contained-end`, `-start` | `test_wpt_range_contents.rb` | 済 |
| `insertNode(node)` | 1 HierarchyRequestError / 4-5 referenceNode と parent / 6 pre-insert validity / 8-9 referenceNode と remove / 10-11 newOffset / 12 pre-insert / 13 collapsed なら end | `rangeInsertNode` | relation `InsertNodeResult`（`ChildAtOffset`・`NewOffset`。step 13 の「最後に入った node の次」と step 10-11 の newOffset の一致は `insertTail_spec`）、preservation `admissible_rangeInsertNode`, `validBoundaryPoint_of_siblingBP` | `range-insert-node-wraps-inserted`, `-fragment`, `-errors`, `-self-is-hierarchy-error`, `-moves-preceding-sibling`, `-start-text-is-self`, `-detached-text-start`, `range-insert-node-null-leaves-text-alone` | 同上 | 済（step 7 の split text は対象外） |

`extractContents` / `cloneContents` / `surroundContents` / `cloneRange` は node を生むので
Text を分割して node を作るので model の対象外である。`insertNode` の step 7（start node が Text なら split する）も
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
| dispatch | 1-5, 12-13, 14-18 | `dispatchEvent`, `eventPath`, `runPass` | relation `DispatchResult`（`EventPathSpec`・`PassRan`・`Invoked`・`InnerInvoked`）、`dispatchEvent_result_sound` / `_complete`（等号）、preservation `admissible_dispatchEvent`, `listenersOnly_dispatchEvent` | `event-dispatch-phases`, `event-dispatch-at-character-data-target` | `test_wpt_event_dispatch.rb` | 済（shadow / activation は対象外） |
| invoke | 1-9 | `invokeItem` | 同上 | `event-listener-flags` | 同上 | 済 |
| inner invoke | 1-3 | `innerInvoke`, `invokeOne` | 同上 | 同上 | 同上 | 済 |
| add an event listener / `addEventListener` | add 5 | `addListener`, `addEventListener` | relation `AddEventListenerResult`（`ListenerAdded`）、`addEventListener_result_sound` / `_complete`、preservation `admissible_addEventListener` | `event-listener-add-and-remove` | 同上 | 済（`signal` / `passive` は対象外） |
| remove an event listener / `removeEventListener` | remove 2 | `removeListenerAt`, `removeEventListener` | relation `RemoveEventListenerResult`（`ListenerRemovedAt`）、`removeEventListener_result_sound` / `_complete`、preservation `admissible_removeEventListener` | 同上 | 同上 | 済 |
| `stopPropagation` / `stopImmediatePropagation` / `preventDefault` | — | `runAction` | relation `CallbackRan` | `event-listener-flags` | 同上 | 済 |

## §4.4 値を返すだけの `Node` の method / §4.9 attribute の getter / §5.5 stringifier

木も live object も変えないので、差分テストでは戻り値だけを比べる。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `compareDocumentPosition(other)` | 1, 6-10 | `compareDocumentPosition` | `compareDocumentPosition_disconnected_consistent`, `Spec.compareDocumentPosition_spec`, `Spec.compareDocumentPosition_eq_iff`（`Dom/Spec/NodeQuery.lean`） | `node-query-position-and-containment`, `compare-document-position-disconnected-is-consistent` | `test_wpt_node_edges.rb` | 済（`Attr` の step 3-5 は下の `compareDocumentPositionRef` の行） |
| `contains(other)` / `getRootNode()` | — | `nodeContains`, `getRootNode` | `Spec.nodeContains_eq_true_iff`, `Spec.getRootNode_eq_iff`（同上） | `node-query-position-and-containment` | 同上 | 済（`composed` は対象外） |
| `equals` / `isEqualNode(other)` | equals | `nodeEquals`, `nodeOwnPropertiesEqual`, `attrEquals` | — | `node-query-is-equal-node` | 同上 | 済（DocumentType の name ほかは対象外） |
| get text content / `textContent` getter | — | `getTextContent`, `descendantTextContent` | — | `node-query-text-content` | 同上 | 済（setter は node を作るので対象外） |
| `nodeValue` getter | — | `getNodeValue` | — | 同上 | 同上 | 済 |
| substring data / `substringData(offset, count)` | 1-4 | `substringData` | — | `characterdata-substring-data`, `-index-size` | `test_wpt_character_data.rb` | 済 |
| `getAttribute` / `hasAttribute` / `getAttributeNames` | 1-2 ほか | `getAttribute`, `hasAttribute`, `getAttributeNames`, `attrNameFor` | — | `attribute-getters` | `test_wpt_attributes.rb` | 済 |
| `Range` の stringifier | 1-6 | `rangeToString` | — | `range-to-string`, `-within-one-text` | `test_wpt_range_contents.rb` | 済 |
| locate a namespace / `lookupNamespaceURI(prefix)` | Element 1-6 / Document 1-2 / lookupNamespaceURI 1-2 | `locateNamespace`, `locateNamespaceIn`, `elementChain` | `lookupNamespaceURI_lookupPrefix_own`、`lookup_round_trip_fails`（negative）、`find?_xmlnsDecl_eq` | `namespace-lookup-chain`, `namespace-lookup-edges`, `namespace-lookup-is-not-a-round-trip` | `test_wpt_node_namespace.rb` | 済（Attr は対象外） |
| locate a namespace prefix / `lookupPrefix(namespace)` | 1-4 / lookupPrefix 1-2 | `lookupPrefix`, `locateNamespacePrefixIn` | — | 同上 | 同上 | 済 |
| `isDefaultNamespace(namespace)` | 1-3 | `isDefaultNamespace` | — | 同上 | 同上 | 済 |

`compareDocumentPosition` の step 6（同じ木にない）は PRECEDING と FOLLOWING の
どちらを返すかを実装に任せている。差分テストはその二 bit を落として比べる
（`test/compare.rb` の `normalize_returned`）。一貫性そのものは model 側の定理で見る。
同じ木にある場合の値は `Spec.compareDocumentPosition_eq_iff` が §4.2 の語彙
（`Ancestor` と構造で書いた tree order `PrecedesStruct`）だけで一意に決めている。

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
`TreeWalker` を作る API（`createTreeWalker`）は model に無いので、
scenario が最初から walker を与える形にしてある。

## §4.3 MutationObserver

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| queue a mutation record | 1-2 inclusive ancestor を辿って observer を集める / 2.3 registration ごとの条件（型・scope・attributeFilter）/ 2.3.3 oldValue / 3-6 record を積む | `queueMutationRecord`, `interestedObservers`, `Registration.interestedIn` | preservation `preservesRegs_*` | `observer-uninterested-registration-does-not-shadow`, `observer-attribute-filter-does-not-shadow`, `observer-attribute-filter-skips-namespaced`, `observer-old-value-from-any-registration` | `test_wpt_mutation_record_details.rb`, `test_wpt_mutation_observer_order.rb`, `test_wpt_mutation_observer_attribute_options.rb` | 済 |
| queue a tree mutation record | 1 assert / 2 queue | `queueTreeMutationRecord` | 同上 | 同上 | `test_wpt_mutation_record_insertion_point.rb` | 済 |
| transient registered observer | remove step 20 | `addTransientObservers` | `preservesRegs_remove` | `observer-transient-follows-existing-registration` | `test_wpt_transient_registered_observer.rb` | 済 |
| queue a mutation observer microtask | 1-3 | `queueMutationObserverMicrotask`, `addPendingObserver` | preservation `admissible_*`（配送は木を触らない） | `observer-delivery` | `test_wpt_mutation_observer_order.rb` | 済 |
| notify mutation observers | 1-5 | `notifyMutationObservers`, `notifyEach`, `notifyOne`, `removeTransients` | `admissible_notifyMutationObservers`, `notifyMutationObservers_tree/_ranges/_iterators` | 同上 | 同上 | 済 |
| `observe(target, options)` | 1-8（step 1-2 の省略の解決と step 3-6 の TypeError を含む） | `MutationObserver.observe`, `MutationObserverInit.resolve`, `observeOptionsError` | relation `ObserveResult`（`AttributesResolved`・`CharacterDataResolved`・`ObserveOptionsRejected`、等号で complete）、`admissible_observe`, `observe_tree/_ranges/_iterators` | `observer-uninterested-registration-does-not-shadow` | 同上 | 済 |
| `disconnect()` | 1-2 | `MutationObserver.disconnect` | `admissible_disconnect`, `disconnect_tree/_ranges/_iterators` | （生成 scenario の `disconnect`） | 同上 | 済 |
| `takeRecords()` | 1-3 | `MutationObserver.takeRecords` | `admissible_takeRecords`, `takeRecords_tree/_ranges/_iterators` | （生成 scenario の `takeRecords`） | 同上 | 済 |

## §4.9 Attr / §1.3 名前の検査

attribute は element の状態として持つが、**同一性は `AttrId` で持つ**。
新しい attribute の id は `freshStateAttrId`（木にある id と detach された `Attr` の id を合わせた最大より
一つ大きいもの）で、
runner も同じ規則で振るので差分テストの比較対象に入っている
（`test/README.md` の「作った attribute の id」）。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| valid namespace prefix / valid attribute local name | §1.3 | `isValidNamespacePrefix`, `isValidAttributeLocalName` | — | （生成 scenario の `setAttributeNS`） | `test_wpt_attr.rb` | 済 |
| validate and extract（"attribute" / "element"） | 1-12 | `validateAndExtractAttribute`, `validateAndExtractElement`, `validateAndExtractError` | `validateAndExtractAttribute_ok`（step 1 と step 8）、`validateAndExtractAttribute_wellFormed` と `validateAndExtractElement_wellFormed`（step 8-11、`NamespaceWellFormed`） | 同上 | 同上 | 済（step 11 の prefix がある側は性質に入れていない） |
| get an attribute by name | 1-2 | `getAttributeByName`, `attrNameFor` | `setAttribute_getAttribute` | `attribute-by-name-uses-qualified-name`, `attribute-name-case-follows-namespace` | `test_wpt_attribute_qualified_name.rb` | 済 |
| valid element local name | §1.3 | `isValidElementLocalName` | — | （loader が検査する） | — | 済 |
| `Element.tagName` | §4.8 | `tagName` | — | `attribute-name-case-follows-namespace` | `test_wpt_attribute_qualified_name.rb` | 済 |
| get an attribute by namespace and local name | 1-2 | `getAttributeByKey` | — | （生成 scenario の `removeAttributeNS`） | 同上 | 済 |
| handle attribute changes | 1（2-3 は hook の位置のみ） | `handleAttributeChanges` | relation `AttributeChangeHandled`（`AttributeRecordQueued`）、`handleAttributeChanges_spec`、congruence `attributeChangeHandled_congr`、preservation `admissible_setAttribute` ほか | `observer-attribute-filter-does-not-shadow` | `test_wpt_mutation_observer_attribute_options.rb` | 済 |
| change an attribute | 1-3 | `changeAttribute` | relation `AttributeChanged`、`changeAttribute_spec`、`attributesValid_change` | 同上 | 同上 | 済 |
| append an attribute | 1-4 | `appendAttribute` | relation `AttributeAppended`、`appendAttribute_spec`、`attributesValid_append` | 同上 | 同上 | 済 |
| create an attribute（"set an attribute value" step 2 と `setAttribute` step 6 の中） | 新しい `Attr` を作る | `freshStateAttrId` | `ne_freshStateAttrId_tree`, `ne_freshStateAttrId_detached` | `attribute-identity-survives-value-change` | — | 済（`Attr` を返す口は下の `createAttribute` の行） |
| remove an attribute | 1-4 | `removeAttributeFrom` | relation `AttributeRemoved`、`removeAttributeFrom_spec`、`attributesValid_erase`, `removeAttribute_erases` | `attribute-by-name-uses-qualified-name` | `test_wpt_attribute_qualified_name.rb` | 済 |
| set an attribute value | 1-3 | `setAttributeValue` | relation `SetAttributeValueResult`（結果込み、sound / 一意 / complete）、`attrOpResult_setAttributeValue` | （生成 scenario の `setAttributeNS`） | `test_wpt_attr.rb` | 済 |
| `setAttribute(qualifiedName, value)` | 1-2, 4-7（step 3 は Trusted Types なので非対象） | `setAttribute`, `attrNameFor` | relation `SetAttributeResult`（結果込み）、`setAttribute_result_complete`、`admissible_setAttribute`, `setAttribute_getAttribute` | `attribute-by-name-uses-qualified-name`, `attribute-name-case-follows-namespace`, `attribute-identity-survives-value-change` | `test_wpt_attribute_qualified_name.rb` | 済 |
| `setAttributeNS(namespace, qualifiedName, value)` | 1, 3（step 2 は Trusted Types なので非対象） | `setAttributeNS` | `admissible_setAttributeNS` | （生成 scenario） | `test_wpt_attr.rb` | 済 |
| `removeAttribute` / `removeAttributeNS` | 全 | `removeAttribute`, `removeAttributeNS` | relation `RemoveAttributeResult` / `RemoveAttributeNSResult`（結果込み）、`admissible_removeAttribute`, `admissible_removeAttributeNS` | `attribute-by-name-uses-qualified-name` | `test_wpt_attribute_qualified_name.rb` | 済 |
| `toggleAttribute(qualifiedName, force)` | 1-6 | `toggleAttribute`, `attrNameFor` | relation `ToggleAttributeResult`（結果込み）、`toggleAttribute_result_complete`、`admissible_toggleAttribute` | 同上 | 同上 | 済 |
| create an attribute / `createAttribute` / `createAttributeNS` | createAttribute 1-3 / createAttributeNS 1-2 | `createAttributeIn`, `createAttribute`, `createAttributeNS` | preservation `admissible_createAttribute`, `admissible_createAttributeNS` | `attr-node-identity-moves` | — | 済 |
| `getAttributeNode` / `getAttributeNodeNS` | 全 | `getAttributeNode`, `getAttributeNodeNS` | — | 同上 | — | 済 |
| set an attribute / `setAttributeNode` | 2 InUseAttributeError / 3-4 同じ鍵を引く / 7 replace / 8 append（step 1 と 6 は Trusted Types なので非対象） | `setAttributeNode`, `replaceAttributeWith` | relation `SetAttributeNodeResult`（結果込み、sound / 一意 / complete）、preservation `admissible_setAttributeNode`、`attributesValid_replace` | 同上 | — | 済（`setAttributeNodeNS` は step が同一なので別に置かない） |
| replace an attribute | 1-6 | `replaceAttributeWith` | relation `AttributeReplacedWith`、`replaceAttributeWith_spec`、`attributesValid_replace` | 同上 | — | 済 |
| `removeAttributeNode` | 1 NotFoundError / 2-3 | `removeAttributeNode`, `detachAttribute` | relation `RemoveAttributeNodeResult`（結果込み）・`AttributeDetached`、preservation `admissible_removeAttributeNode` | `remove-attribute-node-checks-the-element` | — | 済 |
| `NamedNodeMap.removeNamedItem` | 1-2 | `removeNamedItem` | relation `RemoveNamedItemResult`（結果込み）、preservation `admissible_removeNamedItem` | `attr-node-identity-moves` | — | 済（`item` / `length` は attribute list の観測で足りる） |
| `Attr` の node document（create・append・replace・adopt） | create an attribute / append an attribute 3 / replace an attribute 4 / adopt 3.3.1 | `Attr.ownerDocument`, `createAttributeIn`, `appendAttribute`, `replaceAttributeWith`, `NodeData.withOwnerDocument`（`setOwnerDocument`） | `DocumentAssigned`（`Dom/Spec/Adopt.lean`）、`documentAssigned_setOwnerDocument` | `adopting-an-element-moves-its-attributes` | — | 済 |
| `adoptNode` / `importNode` / `cloneNode` に `Attr` を渡す | adoptNode 1-4 / adopt 1-3 / clone a single node の `Attr` の枝 | `adoptAttr`, `importAttr`, `cloneAttr`, `cloneAttrIn` | `admissible_adoptAttr`, `admissible_importAttr`, `admissible_cloneAttr`, `cloneAttrIn_spec` | `adopt-node-keeps-an-attribute-on-its-element`, `attr-values-and-copies` | — | 済（element から外さない。browser は外す） |
| set an existing attribute value（`value`・`nodeValue`・`textContent` の setter） | 1-2, 5（3-4 は Trusted Types なので非対象） | `setAttrValue` | `admissible_setAttrValue` | `attr-values-and-copies` | — | 済 |
| `Attr` の `parentNode`・`getRootNode`・`isConnected`・`hasChildNodes`・`nodeName` ほか | §4.4 の各 getter | `attrParentNode`, `attrGetRootNode`, `attrQueryValue` | — | `attr-is-a-node-outside-the-tree` | — | 済 |
| `compareDocumentPosition` の step 3-5（`Attr`） | 3-9 | `compareDocumentPositionRef` | `compareDocumentPositionRef_nodes`, `compareDocumentPositionRef_self`, `compareDocumentPositionRef_disconnected_consistent` | `attr-position-follows-its-element` | — | 済 |
| `contains` / `isEqualNode` / namespace の探索に `Attr` | contains / equals の `Attr` の枝 / locate a namespace の `Attr` の枝 | `nodeContainsRef`, `nodeRefEquals`, `attrLookupNamespaceURI`, `attrLookupPrefix`, `attrIsDefaultNamespace` | `nodeContainsRef_attr_attr`, `nodeContainsRef_node_attr` | `attr-position-follows-its-element` | — | 済 |
| `appendChild` の親か子に `Attr` | ensure pre-insertion validity 1・4 | `appendChildRef` | `appendChildRef_attr_fails`, `admissible_appendChildRef` | `attr-cannot-be-a-child`, `attr-cannot-have-children` | — | 済 |
| reflect（`id` / `className` / `slot`、HTML の `title` / `lang` / `accessKey` / `inert` / `autofocus`） | DOM §4.9・HTML §2.6.1 の getter と setter（DOMString と boolean） | `reflectSpec`, `getReflectedProp`, `setReflectedProp`, `setReflectedBool` | `SameNullNsView.getReflected`、preservation `admissible_setReflectedProp`, `admissible_setReflectedBool` | `reflect-reads-the-null-namespace-attribute`, `reflect-writes-the-null-namespace-attribute` | — | 済（enumerated・URL・数値の reflect は対象外） |
| `DOMTokenList`（`classList`） | §7.1 add 1-3 / remove 1-3 / toggle 1-4 / replace 1-6 / contains / update steps 1-2 | `classListAdd`, `classListRemove`, `classListToggle`, `classListReplace`, `classListContains`, `tokenListUpdate` | `SameNullNsView.classListContains`、preservation `admissible_classListAdd` ほか | `class-list-ignores-namespaced-class`, `class-list-add-nothing-creates-no-attribute` | — | 済（`value` と `supports` は対象外） |
| `HTMLCollection.namedItem(key)`（`children`） | §4.2.10.1 1-2 | `childrenNamedItem` | `SameNullNsView.childrenNamedItem` | `named-item-ignores-namespaced-id-and-name` | — | 済 |
| `dataset`（`DOMStringMap`） | HTML §3.2.6.8 name-value pairs 1-3 / setter 1-5 / deleter 1-3 | `datasetPairs`, `datasetGet`, `datasetKeys`, `datasetSet`, `datasetDelete` | preservation `admissible_datasetSet`, `admissible_datasetDelete` | `dataset-reads-by-qualified-name`, `dataset-writes-the-null-namespace-attribute`, `dataset-deletes-by-qualified-name`, `dataset-only-on-html-and-svg` | — | 済（本文の字面どおり。どの browser も字面どおりではない。MathML の element は扱っていない） |

## normative branch の網羅

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

## §4.5 Document の factory / §4.4 `cloneNode`

作った node には、runner が model の `freshId` と同じ規則で id を振る。
それで差分テストの比較対象に入っている（`test/README.md` の「作った node の id」）。
生成 scenario も、**必ず成功する形だけ**を作る（`docs/status.md` を参照）。

| Algorithm | WHATWG steps | Evaluator | Contracts | Scenario | WPT | Status |
| --- | --- | --- | --- | --- | --- | --- |
| createElement | 1 valid element local name / 2 HTML document なら ASCII lowercase / 4 HTML document なら HTML namespace | `createElement`, `requireDocument`, `withFresh` | effect `createElement_creates`、preservation `admissible_createsNode` | `create-element-lowercases-in-html-document` | — | 済（custom element の step 3 と 5 は対象外。XML document の側は harness が作れない） |
| createElementNS | validate and extract（context は "element"）してから element を作る | `createElementNS`, `validateAndExtractElement` | effect `createElementNS_creates` | `create-element-lowercases-in-html-document` | — | 済 |
| createTextNode / createComment / createDocumentFragment | node を一つ作り node document を this にする | `createTextNode`, `createComment`, `createDocumentFragment` | effect `createTextNode_creates` ほか | `create-node-is-detached-and-owned` | — | 済 |
| clone a single node | 2 element は create an element で / 2.1 attribute ごとに clone を作る / 3 それ以外は同じ interface で / 3.1 Document の copy の node document は copy 自身 | `cloneSingle`, `cloneData`, `cloneDocumentOf` | effect `cloneNodeIn_shallow_spec`、`cloneData_shapeAnon`（id 以外は同じ） | `clone-node-copies-shape-not-identity`, `import-node-keeps-attribute-namespace` | — | 済（shadow root と custom element は対象外） |
| clone a node | 2 copy を作る / 4 parent が非 null なら copy を append / 5 subtree なら children を tree order で clone（document は引数のまま） | `cloneNode`, `cloneNodeIn`, `cloneMany`, `cloneAppend` | `cloneNode_cloneOf`（同じ形）、`cloneNode_ne`（別の id）、preservation `admissible_cloneNode`、totality `cloneNode_isOk`、frame `cloneNode_keep` と `cloneNode_ranges` | `clone-node-copies-shape-not-identity` | — | 済（step 6 の shadow root は対象外） |
| importNode | 1 Document なら NotSupportedError / 最終 step で clone a node を document = this、subtree = options で呼ぶ | `importNode` | `importNode_ne`（別の id）、`importNode_cloneOf`（同じ形）、`importNode_ownerDocument`、preservation `admissible_importNode`、totality `importNode_isOk`、frame `importNode_keep` と `importNode_ranges` | `import-node-copies-into-the-receiver` | — | 済（options の dictionary 形と custom element registry は対象外） |
| adoptNode | 1 Document なら NotSupportedError / 3 adopt する / 4 node を返す | `adoptNode` | `adoptNode_id`（同じ id）、`adoptNode_ownerDocument`、`adoptNode_detached`、`adoptNode_shape`、preservation `admissible_adoptNode` | `adopt-node-moves-the-same-node` | — | 済（step 2 の shadow root は対象外） |

step 4 の append は §4.2.3 の `append` をそのまま呼ぶ。だから妥当性の保存も
live range の調整も mutation record も、そちらの証明が効く。step 5 が children に渡す
`document` は copy ではなく引数のままで、Document を clone したときに children の
node document が copy になるのは `append` の中の adopt による。
`docs/status.md` の「clone を入れた」を参照。

## 未対応と対象外

| 項目 | 扱い | 根拠 |
| --- | --- | --- |
| Shadow DOM（shadow-including root / slot） | 未対応 | shadow tree を表す構造が model に無い。`move` step 1 は shadow-including root ではなく root で近似している |
| MutationObserver の callback 本体 | 対象外 | callback は model の外。`notifyMutationObservers` は「どの observer に何が配送されるか」を返すところまで |
| `Attr` の node としての性質 | 部分対応 | model の attribute は element の状態で node tree に入らない。node document（`Attr.ownerDocument`）、parent が null であること、root が自分であること、`compareDocumentPosition` の step 3-5、value の setter、clone / import / adopt、子を持てないことは扱う（`Dom/Attribute/AsNode.lean`）。`Attr` を target にした event の配送と、`insertBefore` などの child 側に `Attr` を渡す形は扱わない |
| ProcessingInstruction の attribute map（§4.11 の `setAttribute` ほか） | 対象外 | element の attribute list とは別の仕組みで、attribute の mutation record を積まない。Dommy も未実装なので差分テストで裏を取れない |
| custom element / insertion steps / removing steps | 対象外 | hook の位置だけを保っている |
| UTF-16 の lone surrogate | 部分モデル | 長さと offset は code unit で数える（`Dom/Basic/Utf16.lean`）。surrogate pair を割った切り出しだけは Lean の `Char` で表せないので `DOMException.outsideModel` を返し、差分テストはその step 以降を比較しない。boundary point が pair の途中を指すことは扱える |
| node 生成と可変長引数の変換 | 部分対応 | §4.5 の factory・§4.4 の `cloneNode`・§4.5 の `importNode` / `adoptNode` は model にあり、固定 scenario でも生成 scenario でも差分テストに出ている。生成側は必ず成功する形だけを作る。`convert nodes into a node` は呼び出し側で済ませた形で受け取る |
| method の戻り値 | 済 | `returnValueOf`（`Dom/Exec/Eval.lean`）。`Node?` / boolean / record 列を kind つきで観測する。`undefined` と `null` は区別する |
| wrapper の object identity | 対象外 | model は wrapper を持たないので wrapper を作る API の同一性は観測できない。node を返す method の戻り値は `NodeId` で比べるので「返ってきたのは渡した node そのものか」は観測できる |
| `normalize()` の record の並び | engine に合わせた | 仕様を字義どおり読むと run ごとに characterData が一つだが、Blink・WebCore・Gecko は兄弟ごとに積む。WPT が固定しているのは childList の側だけである。木と live range の最終状態はどちらの読みでも同じ |
| `Attr` の identity | 済 | attribute は element の状態だが、同一性は `AttrId` で持つ。element から外れた `Attr` は `detachedAttrs` にいる。`setAttributeNode` / `removeAttributeNode` / `NamedNodeMap.removeNamedItem` / `InUseAttributeError` は関係で特徴付けてあり（`SetAttributeNodeResult` ほか）、id の一意性は全操作で保たれる（`AttrIdsUnique`） |
| `NodeFilter` の callback | 対象外 | callback は model の外なので filter は常に null。`whatToShow` は純粋なので扱う |
| WebIDL の TypeError | 近似 | `observe` の step 3-6、attribute の method の receiver が Element でない場合、`moveBefore` の receiver が ParentNode でない場合（`move-receiver-must-be-parentnode`）を `DOMException.typeError` で表す。名前は一致するが実際には `DOMException` ではない |

## §1.3 Selectors / §4.2.6 `ParentNode` / §4.8 `Element`

selector は CSS の仕様なので、参照する版は `docs/selectors-spec-version.md` に
別に固定してある。形式化の範囲もそこに書いた。木も live object も変えないので、
差分テストでは戻り値だけを比べる。

| Algorithm | 仕様 | Evaluator | Contracts | Scenario | Status |
| --- | --- | --- | --- | --- | --- |
| tokenization | CSS Syntax §3.3・§4 | `tokenize`（`Selectors/Token.lean`） | `tokenAt_le`, `nextToken_lt`（停止性）、`TokenizesInput.iff_tokenize` ほか（関係意味論、`Selectors/Spec/Token*.lean`） | `escapes-in-selectors`, `escape-out-of-range-is-replacement`, `string-backslash-newline-continues` ほか | 済（url-token / unicode-range-token は対象外） |
| consume a list of component values | CSS Syntax §5.4.6 | `toComponents`（`Selectors/Component.lean`） | `splitBlock_size` | `unclosed-block-is-closed-at-eof` | 済 |
| `parse a selector` | Selectors §19.1 | `parseSelector`（`Selectors/Parser.lean`） | `dropToComma_size`, `splitAtOf_size`（停止性）、`parseSelector_spec`, `scan_spec`（関係意味論、`Selectors/Spec/Scan*.lean`） | `universal-selector-takes-subclasses`, `id-selector-needs-an-identifier` | 部分（namespace prefix と pseudo-element は対象外） |
| `<a-n-plus-b>` の構文 | CSS Syntax §9.2 | `parseAnB` | — | `structural-pseudo-classes-count-elements` | 済 |
| `<a-n-plus-b>` が表す index | CSS Syntax §9.1 | `anbMatches` | `anbMatches_iff`（関係意味論） | `nth-child-with-negative-coefficient` | 済 |
| match a selector against an element | Selectors §17.1 | `matchSelList`（`Dom/Selector/Match.lean`） | `sSize_lt_cpSize`, `cxSize_lt_lSize`（停止性）、`matchSelList_iff_spec`, `matchSimple_iff_spec`, `mem_matchTree_iff_spec`（関係意味論、`Dom/Spec/SelectorMatch.lean`） | `structural-pseudo-classes-count-elements` | 部分（状態の pseudo-class は対象外） |
| combinator が結ぶ element | Selectors §16 | `combCandidates` | `mem_combCandidates_descendant` 〜 `_nextSibling`, `mem_combCandidates_iff`（関係意味論） | `sibling-combinators-pick-the-right-neighbour` | 済 |
| attribute selector の値の照合 | Selectors §6.3 | `attrTestHolds` | `attrTestHolds_iff`, `includes_empty_never`, `includes_whitespace_never` | `attribute-selectors-compare-values`, `attribute-includes-needs-a-whole-word` | 済（`~=` の語境界は定理にしていない） |
| type selector の大文字小文字 | Selectors §6.1 | `typeHolds` | `typeHolds_iff` | `type-selector-case-follows-namespace` | 済 |
| `:root` / `:empty` | Selectors §14.1・§14.2 | `matchSimple` の枝、`emptyOk` | `matchSimple_root_iff`, `emptyOk_iff`, `matchSimple_empty_iff` | `structural-pseudo-classes-count-elements`, `empty-pseudo-allows-white-space` | 済 |
| `:has()` の候補 | Selectors §14.10 | `matchSimple` の `.has` の枝 | `matchSimple_has_iff` | `has-can-look-at-siblings` | 済 |
| attribute selector の namespace | Selectors §6.4 | `selectorAttrOk`, `plainAttr` | `selectorAttrOk_iff`, `matchSimple_attr_iff`, `plainAttr_some`, `plainAttr_none` | `selector-attributes-have-no-namespace` | 済 |
| `:nth-*()` が数える列 | Selectors §14.3-14.7 | `elementSiblings`, `matchSimple` の `.nth` の枝 | `mem_elementSiblings_iff`, `sameTypeAs_iff`, `matchSimple_nth_iff` | `nth-of-type-counts-only-its-own-type`, `detached-element-is-its-own-only-sibling`, `structural-pseudo-classes-count-elements` | 済 |
| match a selector against a tree / scope-match a selectors string | Selectors §17.3 / DOM §1.3 | `matchTree`, `scopeMatch`（`Dom/Selector/Api.lean`） | `matchTree_sublist`, `matchTree_nodup`, `mem_matchTree_iff` | `query-selector-finds-in-tree-order`, `scope-pseudo-is-the-scoping-root`, `scope-pseudo-is-the-document-element`, `scope-pseudo-virtual-root-is-featureless` | 済 |
| `querySelector(selectors)` / `querySelectorAll(selectors)` | DOM §4.2.6 | `querySelector`, `querySelectorAll` | `admissible_mapConst`, `querySelector_eq_head`, `querySelectorAll_eq_matchTree` | `query-selector-finds-in-tree-order`, `selector-is-parsed-before-matching` | 済 |
| 受け手の種別検査（WebIDL の TypeError） | DOM §4.2.6・§4.8 | `requireParentNode`, `requireElementNode` | — | `query-selector-needs-a-parent-node`, `matches-needs-an-element` | 済 |
| scoped selector（subject だけが scope 内） | Selectors §4.4 | `matchTree` | `mem_matchTree_iff` | `only-the-subject-must-be-in-scope`, `query-selector-on-detached-and-fragment` | 済 |
| `matches(selectors)` / `closest(selectors)` | DOM §4.8 | `matchesSelector`, `closest` | `matchesSelector_eq`, `closest_spec`, `closest_first`, `closest_eq_none_iff`, `closest_self`, `mem_matchTree_iff_matches` | `matches-and-closest-walk-up` | 済 |
| `:scope` が scoping root を表すこと | Selectors §8.2 | `Simple.scope` | `scope_irrelevant`, `matchSelList_scope_irrelevant` | `scope-pseudo-is-the-scoping-root`, `scope-pseudo-is-the-document-element`, `scope-pseudo-virtual-root-is-featureless` | 済 |
| class・id selector の大文字小文字と document の mode | HTML §"Case-sensitivity of selectors"・DOM §4.5 | `inQuirksModeOf`, `quirksFold`, `matchSimple` の `.id`・`.cls` の枝 | `inQuirksModeOf_iff`, `quirksFold_eq_iff`, `classWordIn_iff`, `matchSimple_iff_spec` | `quirks-mode-folds-class-and-id`, `quirks-mode-belongs-to-the-node-document` | 済（limited-quirks は no-quirks と同じ） |
| `getElementById(elementId)` | DOM §4.2.4 | `getElementById`, `elementIdOf`（`Dom/Query/Lookup.lean`） | `getElementById_eq_some`, `getElementById_eq_none_iff`, `getElementById_error_iff`, `elementIdOf_eq_some_iff`（`Dom/Spec/Lookup.lean`） | `lookups-compare-attribute-values` | 済（tree order で最初であることは `List.find?` そのもの） |
| `getElementsByClassName(classNames)` / ordered set parser | DOM §4.5・§4.9・§2.3 | `getElementsByClassName`, `orderedSetParse`, `elementClassesOf` | `mem_getElementsByClassName_iff`, `mem_orderedSetParse_iff`, `mem_elementClassesOf_iff` | `lookups-compare-attribute-values`, `class-names-keep-case-without-quirks`, `quirks-mode-folds-class-and-id` | 済 |
| `getElementsByName(elementName)` | HTML §3.1.5 | `getElementsByName` | `mem_getElementsByName_iff` | `lookups-compare-attribute-values`, `get-elements-by-name-finds-only-html-elements` | 済 |

## `cloneNode` / `adoptNode` の全域性

| Algorithm | 仕様 | 定理 | 内容 |
| --- | --- | --- | --- |
| `cloneNode(deep)` | DOM §4.4 | `cloneNode_isOk` | 妥当な木の上では `HierarchyRequestError` にならない |
| `importNode(node, subtree)` | DOM §4.5 | `importNode_isOk` | 同上（Document でない node なら） |
| `adopt` | DOM §4.5 | `adopt_isOk` | 木にある node に対して必ず成功する |
| `adoptNode(node)` | DOM §4.5 | `adoptNode_isOk` | Document でない node なら必ず成功する |

## 仕様改訂時の手順

1. `docs/spec-version.md` の commit から新しい commit までの `dom.bs` の差分を取る。
2. 差分に現れた algorithm 名でこの表を検索し、その行を review する。
3. step 要約が変わっていれば要約を直し、意味が変わっていれば evaluator と契約を直す。
4. 影響を受けた行の固定 scenario を再実行し、期待結果の根拠（`_note`）を更新する。
5. `docs/spec-version.md` の commit を進める。

step 番号だけを見て追従しないこと。番号は挿入・削除で簡単にずれる。
