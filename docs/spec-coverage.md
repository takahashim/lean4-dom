# 仕様の step との対応（自動生成）

このファイルは `ruby spec-trace/check.rb --write` が `Trace/` の対応表と `spec-trace/dom.json` から作る。手で編集しない。

対象は `dom.bs` commit `a2331a45360129e8645ef7e0a04740241b6e3726` である。algorithm の鍵は描画された仕様の anchor で、各行はその commit の snapshot に張ってある。

| 項目 | 数 |
| --- | --- |
| `dom.bs` の algorithm | 391 |
| 表に載せたもの | 221 |
| 対象外としたもの | 170 |
| 表に載せた algorithm の step | 980 |
| そのうち実装したもの | 558 |
| そのうち近似したもの | 222 |
| そのうち外したもの | 200 |

step の数は入れ子の step も一つと数える。step を持たない一文の algorithm は一つと数える。
「関係」の列は `Dom/Spec/` にある、仕様本文から独立に書いた関係である。

## 表に載せた algorithm

### §1.2（`ordered-sets`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-ordered-set-parser](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-ordered-set-parser) | 2/4（近似 2） | `Dom.orderedSetParse`<br>`Dom.splitWsAux` | `Dom.Spec.ClassToken` |
| [concept-ordered-set-serializer](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-ordered-set-serializer) | 0/1（近似 1） | `Dom.tokenListUpdate` |  |

### §1.3（`selectors`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [scope-match-a-selectors-string](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#scope-match-a-selectors-string) | 2/3（近似 1） | `Dom.scopeMatch`<br>`Dom.matchTree`<br>`Selectors.parseSelector`<br>`Dom.matchSelList` | `Dom.Spec.ScopeMatchResult`<br>`Dom.Spec.MatchAgainstTree`<br>`Dom.Spec.SelectorListMatches` |

### §1.4（`namespaces`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [valid-namespace-prefix](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#valid-namespace-prefix) | 1/1 | `Dom.isValidNamespacePrefix` |  |
| [valid-attribute-local-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#valid-attribute-local-name) | 1/1 | `Dom.isValidAttributeLocalName` |  |
| [valid-element-local-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#valid-element-local-name) | 7/7 | `Dom.isValidElementLocalName` |  |
| [validate-and-extract](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#validate-and-extract) | 14/15 | `Dom.validateAndExtractAttribute`<br>`Dom.validateAndExtractElement`<br>`Dom.validateAndExtractError`<br>`Dom.splitAtFirstColon`<br>`Dom.normalizeNamespace` | `Dom.Spec.validateAndExtractSteps`<br>`Dom.Spec.validateAndExtractAttribute_eq_steps`<br>`Dom.Spec.validateAndExtractElement_eq_steps` |

### §2.2（`interface-event`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-event-stoppropagation](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-event-stoppropagation) | 0/1（近似 1） | `Dom.runAction` | `Dom.Spec.CallbackRan` |
| [dom-event-stopimmediatepropagation](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-event-stopimmediatepropagation) | 0/1（近似 1） | `Dom.runAction` | `Dom.Spec.CallbackRan` |
| [set-the-canceled-flag](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#set-the-canceled-flag) | 0/1（近似 1） | `Dom.runAction` | `Dom.Spec.CallbackRan` |
| [dom-event-preventdefault](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-event-preventdefault) | 0/1（近似 1） | `Dom.runAction` | `Dom.Spec.CallbackRan` |

### §2.7（`interface-eventtarget`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [add-an-event-listener](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#add-an-event-listener) | 0/7（近似 1） | `Dom.addListener` | `Dom.Spec.ListenerAdded` |
| [dom-eventtarget-addeventlistener](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-eventtarget-addeventlistener) | 0/2（近似 2） | `Dom.addEventListener`<br>`Dom.addListener` | `Dom.Spec.AddEventListenerResult` |
| [remove-an-event-listener](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#remove-an-event-listener) | 0/2（近似 1） | `Dom.removeListenerAt` | `Dom.Spec.ListenerRemovedAt` |
| [dom-eventtarget-removeeventlistener](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-eventtarget-removeeventlistener) | 1/2（近似 1） | `Dom.removeEventListener`<br>`Dom.removeListenerAt` | `Dom.Spec.RemoveEventListenerResult` |
| [dom-eventtarget-dispatchevent](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-eventtarget-dispatchevent) | 0/3（近似 1） | `Dom.dispatchEvent` | `Dom.Spec.DispatchResult` |

### §2.9（`dispatching-events`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-event-dispatch](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-event-dispatch) | 1/58（近似 22） | `Dom.dispatchEvent`<br>`Dom.eventPath`<br>`Dom.runPass`<br>`Dom.invokeItem` | `Dom.Spec.DispatchResult`<br>`Dom.Spec.EventPathSpec`<br>`Dom.Spec.PassRan` |
| [concept-event-path-append](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-event-path-append) | 0/5（近似 1） | `Dom.eventPath` | `Dom.Spec.EventPathSpec` |
| [concept-event-listener-invoke](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-event-listener-invoke) | 2/15（近似 2） | `Dom.invokeItem`<br>`Dom.innerInvoke` | `Dom.Spec.Invoked`<br>`Dom.Spec.ListenersOf` |
| [concept-event-listener-inner-invoke](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-event-listener-inner-invoke) | 6/21 | `Dom.innerInvoke`<br>`Dom.invokeOne`<br>`Dom.runAction`<br>`Dom.removeListenerAt` | `Dom.Spec.InnerInvoked`<br>`Dom.Spec.CallbackRan` |

### §4.2（`node-trees`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-node-length](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-length) | 2/3（近似 1） | `Dom.lengthOf`<br>`Dom.NodeData.length` |  |

### §4.2.3（`mutation-algorithms`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-node-ensure-pre-insertion-validity](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-ensure-pre-insertion-validity) | 17/17 | `Dom.ensurePreInsertionValidity` | `Dom.Spec.PreInsertValidity` |
| [concept-node-pre-insert](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-pre-insert) | 5/5 | `Dom.preInsert`<br>`Dom.preInsertReferenceChild` | `Dom.Spec.PreInsertResult` |
| [concept-node-insert](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-insert) | 15/31 | `Dom.insert`<br>`Dom.insertNodesAt`<br>`Dom.insertEachAt`<br>`Dom.insertEach`<br>`Dom.insertPrevSibling` | `Dom.Spec.InsertSpec` |
| [concept-node-append](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-append) | 1/1 | `Dom.append` |  |
| [move](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#move) | 20/33（近似 1） | `Dom.move`<br>`Dom.moveValidity` | `Dom.Spec.MoveSpec`<br>`Dom.Spec.MoveValidity` |
| [concept-node-replace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-replace) | 13/13 | `Dom.replace` | `Dom.Spec.ReplaceSpec`<br>`Dom.Spec.ReplaceResult` |
| [concept-node-replace-all](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-replace-all) | 7/7 | `Dom.replaceAll`<br>`Dom.replaceAllNodes` | `Dom.Spec.ReplaceAllSpec` |
| [concept-node-pre-remove](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-pre-remove) | 3/3 | `Dom.preRemove` |  |
| [concept-node-remove](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-remove) | 9/21 | `Dom.remove`<br>`Dom.detachWithLiveAdjust` | `Dom.Spec.RemoveSpec`<br>`Dom.Spec.RemoveResult` |

### §4.2.4（`interface-nonelementparentnode`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [get-an-element-by-id](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#get-an-element-by-id) | 1/1 | `Dom.getElementById`<br>`Dom.descendantElements`<br>`Dom.elementIdOf` |  |
| [dom-nonelementparentnode-getelementbyid](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nonelementparentnode-getelementbyid) | 1/1 | `Dom.getElementById`<br>`Dom.requireNonElementParentNode` |  |

### §4.2.6（`interface-parentnode`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-parentnode-children](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-children) | 0/1（近似 1） | `Dom.elementChildrenOf` |  |
| [dom-parentnode-append](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-append) | 1/2（近似 1） | `Dom.append` |  |
| [dom-parentnode-replacechildren](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-replacechildren) | 2/3（近似 1） | `Dom.replaceChildren`<br>`Dom.ensurePreInsertionValidity`<br>`Dom.replaceAll` | `Dom.Spec.ReplaceChildrenResult` |
| [dom-parentnode-movebefore](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-movebefore) | 3/3 | `Dom.moveBefore`<br>`Dom.move` | `Dom.Spec.MoveResult` |
| [dom-parentnode-queryselector](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-queryselector) | 1/1 | `Dom.querySelector`<br>`Dom.scopeMatch`<br>`Dom.matchTree`<br>`Dom.requireParentNode` |  |
| [dom-parentnode-queryselectorall](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-parentnode-queryselectorall) | 0/1（近似 1） | `Dom.querySelectorAll`<br>`Dom.scopeMatch`<br>`Dom.matchTree`<br>`Dom.requireParentNode` |  |

### §4.2.8（`interface-childnode`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-childnode-before](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-childnode-before) | 5/6（近似 1） | `Dom.before`<br>`Dom.viablePreviousSibling`<br>`Dom.preInsert` | `Dom.Spec.BeforeResult`<br>`Dom.Spec.ViablePreviousSibling` |
| [dom-childnode-after](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-childnode-after) | 4/5（近似 1） | `Dom.after`<br>`Dom.viableNextSibling`<br>`Dom.preInsert` | `Dom.Spec.AfterResult`<br>`Dom.Spec.ViableNextSibling` |
| [dom-childnode-replacewith](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-childnode-replacewith) | 3/6（近似 3） | `Dom.replaceWith`<br>`Dom.viableNextSibling`<br>`Dom.replace`<br>`Dom.preInsert` | `Dom.Spec.ReplaceWithResult`<br>`Dom.Spec.ViableNextSibling` |
| [dom-childnode-remove](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-childnode-remove) | 2/2 | `Dom.nodeRemove`<br>`Dom.remove` | `Dom.Spec.NodeRemoveResult` |

### §4.2.10.2（`interface-htmlcollection`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-htmlcollection-nameditem](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-htmlcollection-nameditem) | 0/2（近似 2） | `Dom.childrenNamedItem`<br>`Dom.elementIdOf` |  |

### §4.3（`mutation-observers`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [queue-a-mutation-observer-compound-microtask](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#queue-a-mutation-observer-compound-microtask) | 2/3（近似 1） | `Dom.queueMutationObserverMicrotask` |  |
| [notify-mutation-observers](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#notify-mutation-observers) | 6/11（近似 2） | `Dom.notifyMutationObservers`<br>`Dom.notifyEach`<br>`Dom.notifyOne`<br>`Dom.MutationObserver.takeRecords`<br>`Dom.removeTransients` |  |

### §4.3.1（`interface-mutationobserver`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-mutationobserver-observe](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-mutationobserver-observe) | 9/12（近似 3） | `Dom.MutationObserver.observeMethod`<br>`Dom.MutationObserver.observe`<br>`Dom.MutationObserverInit.resolve`<br>`Dom.MutationObserver.observeOptionsError` | `Dom.Spec.ObserveResult`<br>`Dom.Spec.ObserveOptionsRejected` |
| [dom-mutationobserver-disconnect](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-mutationobserver-disconnect) | 1/2（近似 1） | `Dom.MutationObserver.disconnect` |  |
| [dom-mutationobserver-takerecords](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-mutationobserver-takerecords) | 3/3 | `Dom.MutationObserver.takeRecords` |  |

### §4.3.2（`queueing-a-mutation-record`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [queue-a-mutation-record](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#queue-a-mutation-record) | 13/13 | `Dom.queueMutationRecord`<br>`Dom.interestedObservers`<br>`Dom.Registration.interestedIn`<br>`Dom.addInterested`<br>`Dom.enqueueRecord`<br>`Dom.addPendingObserver`<br>`Dom.queueMutationObserverMicrotask` | `Dom.Spec.TreeRecordQueued`<br>`Dom.Spec.CharacterDataRecordQueued`<br>`Dom.Spec.AttributeRecordQueued` |
| [queue-a-tree-mutation-record](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#queue-a-tree-mutation-record) | 2/2 | `Dom.queueTreeMutationRecord`<br>`Dom.queueMutationRecord` | `Dom.Spec.TreeRecordQueued`<br>`Dom.Spec.treeRecordQueued_of_queue` |

### §4.4（`interface-node`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [create-a-node](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-a-node) | 1/2（近似 1） | `Dom.withFresh` |  |
| [dom-node-nodetype](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-nodetype) | 0/1（近似 1） | `Dom.NodeKind.nodeType`<br>`Dom.kindOf` |  |
| [dom-node-ownerdocument](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-ownerdocument) | 0/1（近似 1） | `Dom.ownerDocumentOf`<br>`Dom.Exec.attrQueryValue` |  |
| [dom-node-getrootnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-getrootnode) | 0/1（近似 1） | `Dom.getRootNode`<br>`Dom.attrGetRootNode` | `Dom.Spec.IsRoot` |
| [dom-node-parentnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-parentnode) | 1/1 | `Dom.parentOf`<br>`Dom.attrParentNode` |  |
| [dom-node-parentelement](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-parentelement) | 1/1 | `Dom.parentElement` |  |
| [dom-node-haschildnodes](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-haschildnodes) | 1/1 | `Dom.childrenOf` |  |
| [dom-node-childnodes](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-childnodes) | 0/1（近似 1） | `Dom.childrenOf` |  |
| [dom-node-firstchild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-firstchild) | 1/1 | `Dom.childrenOf` |  |
| [dom-node-lastchild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-lastchild) | 1/1 | `Dom.childrenOf` |  |
| [dom-node-previoussibling](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-previoussibling) | 1/1 | `Dom.previousSibling` |  |
| [dom-node-nextsibling](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-nextsibling) | 1/1 | `Dom.nextSibling` |  |
| [dom-node-nodevalue](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-nodevalue) | 1/1 | `Dom.getNodeValue`<br>`Dom.Exec.attrQueryValue` |  |
| [dom-node-nodevalue/setter](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-nodevalue) | 0/1（近似 1） | `Dom.setAttrValue`<br>`Dom.setData` |  |
| [get-text-content](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#get-text-content) | 1/1 | `Dom.getTextContent`<br>`Dom.descendantTextContent`<br>`Dom.Exec.attrQueryValue` |  |
| [dom-node-textcontent](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-textcontent) | 1/1 | `Dom.getTextContent`<br>`Dom.Exec.attrQueryValue` |  |
| [dom-node-normalize](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-normalize) | 3/13（近似 10） | `Dom.normalize`<br>`Dom.normalizeList`<br>`Dom.normalizeRun`<br>`Dom.normalizeMergeOne`<br>`Dom.normalizeMergeRange`<br>`Dom.normalizeMergeBP`<br>`Dom.followingTexts` | `Dom.Spec.NormalizeSpec`<br>`Dom.Spec.NormalizeResult` |
| [concept-node-clone](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-clone) | 5/14 | `Dom.cloneNodeIn`<br>`Dom.cloneMany`<br>`Dom.cloneAppend` |  |
| [clone-a-single-node](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#clone-a-single-node) | 11/18（近似 3） | `Dom.cloneSingle`<br>`Dom.cloneData`<br>`Dom.cloneDocumentOf`<br>`Dom.cloneAttrIn` |  |
| [dom-node-clonenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-clonenode) | 1/2 | `Dom.cloneNode`<br>`Dom.cloneAttr` |  |
| [concept-node-equals](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-equals) | 0/1（近似 1） | `Dom.nodeEqualsFuel`<br>`Dom.nodeOwnPropertiesEqual`<br>`Dom.attrEquals`<br>`Dom.nodeRefEquals` |  |
| [dom-node-isequalnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-isequalnode) | 0/1（近似 1） | `Dom.nodeEquals`<br>`Dom.nodeRefEquals` |  |
| [dom-node-comparedocumentposition](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-comparedocumentposition) | 15/15 | `Dom.compareDocumentPosition`<br>`Dom.compareDocumentPositionRef` | `Dom.Spec.DocumentPositionSpec` |
| [dom-node-contains](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-contains) | 0/1（近似 1） | `Dom.nodeContains`<br>`Dom.nodeContainsRef` |  |
| [locate-a-namespace-prefix](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#locate-a-namespace-prefix) | 4/4 | `Dom.locateNamespacePrefixIn`<br>`Dom.elementChain` |  |
| [locate-a-namespace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#locate-a-namespace) | 6/6 | `Dom.locateNamespace`<br>`Dom.locateNamespaceIn`<br>`Dom.elementChain`<br>`Dom.attrLookupNamespaceURI` |  |
| [dom-node-lookupprefix](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-lookupprefix) | 8/8 | `Dom.lookupPrefix`<br>`Dom.attrLookupPrefix` |  |
| [dom-node-lookupnamespaceuri](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-lookupnamespaceuri) | 2/2 | `Dom.lookupNamespaceURI`<br>`Dom.attrLookupNamespaceURI` |  |
| [dom-node-isdefaultnamespace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-isdefaultnamespace) | 3/3 | `Dom.isDefaultNamespace`<br>`Dom.attrIsDefaultNamespace` |  |
| [dom-node-insertbefore](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-insertbefore) | 1/1 | `Dom.insertBefore` |  |
| [dom-node-appendchild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-appendchild) | 1/1 | `Dom.appendChild`<br>`Dom.appendChildRef` |  |
| [dom-node-replacechild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-replacechild) | 1/1 | `Dom.replaceChild` |  |
| [dom-node-removechild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-node-removechild) | 1/1 | `Dom.removeChild` |  |

### §4.5（`interface-document`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-document-compatmode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-compatmode) | 1/1 | `Dom.inQuirksModeOf` |  |
| [dom-document-documentelement](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-documentelement) | 1/1 | `Dom.documentElement` |  |
| [dom-document-getelementsbyclassname](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-getelementsbyclassname) | 0/1（近似 1） | `Dom.getElementsByClassName`<br>`Dom.orderedSetParse`<br>`Dom.elementClassesOf`<br>`Dom.receiverInQuirksMode` |  |
| [dom-document-createelement](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createelement) | 2/5（近似 2） | `Dom.createElement`<br>`Dom.isValidElementLocalName`<br>`Dom.Exec.idlCheck` |  |
| [internal-createelementns-steps](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#internal-createelementns-steps) | 1/3（近似 1） | `Dom.createElementNS`<br>`Dom.validateAndExtractElement` |  |
| [dom-document-createelementns](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createelementns) | 0/1（近似 1） | `Dom.createElementNS`<br>`Dom.Exec.idlCheck` |  |
| [dom-document-createdocumentfragment](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createdocumentfragment) | 1/1 | `Dom.createDocumentFragment` |  |
| [dom-document-createtextnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createtextnode) | 1/1 | `Dom.createTextNode` |  |
| [dom-document-createcomment](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createcomment) | 1/1 | `Dom.createComment` |  |
| [dom-document-importnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-importnode) | 2/10（近似 2） | `Dom.importNode`<br>`Dom.importAttr`<br>`Dom.cloneNodeIn`<br>`Dom.Exec.idlCheck` |  |
| [concept-node-adopt](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-adopt) | 2/14（近似 4） | `Dom.adopt`<br>`Dom.setOwnerDocument`<br>`Dom.NodeData.withOwnerDocument`<br>`Dom.adoptAttr` | `Dom.Spec.AdoptSpec` |
| [dom-document-adoptnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-adoptnode) | 3/4 | `Dom.adoptNode`<br>`Dom.adoptAttr`<br>`Dom.Exec.idlCheck` |  |
| [dom-document-createattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createattribute) | 3/3 | `Dom.createAttribute`<br>`Dom.isValidAttributeLocalName`<br>`Dom.createAttributeIn` |  |
| [dom-document-createattributens](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-document-createattributens) | 2/2 | `Dom.createAttributeNS`<br>`Dom.validateAndExtractAttribute`<br>`Dom.createAttributeIn` |  |

### §4.7（`interface-documentfragment`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-tree-host-including-inclusive-ancestor](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-tree-host-including-inclusive-ancestor) | 0/1（近似 1） | `Dom.isInclusiveAncestorOf` |  |
| [create-a-document-fragment](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-a-document-fragment) | 1/1 | `Dom.createDocumentFragment` |  |

### §4.9（`interface-element`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [element-html-uppercased-qualified-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#element-html-uppercased-qualified-name) | 3/3 | `Dom.tagName`<br>`Dom.isHTMLDocumentOf`<br>`Dom.NodeData.qualifiedName` |  |
| [concept-create-element](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-create-element) | 4/40（近似 1） | `Dom.createElement`<br>`Dom.createElementNS`<br>`Dom.withFresh` |  |
| [create-an-element-internal](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-an-element-internal) | 2/4（近似 2） | `Dom.withFresh` |  |
| [handle-attribute-changes](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#handle-attribute-changes) | 1/3 | `Dom.handleAttributeChanges` | `Dom.Spec.AttributeChangeHandled`<br>`Dom.Spec.AttributeRecordQueued` |
| [concept-element-attributes-change](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-change) | 2/3（近似 1） | `Dom.changeAttribute` | `Dom.Spec.AttributeChanged` |
| [concept-element-attributes-append](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-append) | 3/4（近似 1） | `Dom.appendAttribute` | `Dom.Spec.AttributeAppended` |
| [concept-element-attributes-remove](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-remove) | 3/4（近似 1） | `Dom.detachAttribute`<br>`Dom.removeAttributeFrom` | `Dom.Spec.AttributeDetached`<br>`Dom.Spec.AttributeRemoved` |
| [concept-element-attributes-replace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-replace) | 4/6（近似 2） | `Dom.replaceAttributeWith` | `Dom.Spec.AttributeReplacedWith` |
| [concept-element-attributes-get-by-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-get-by-name) | 2/2 | `Dom.getAttributeByName`<br>`Dom.attrNameFor` | `Dom.Spec.AttrByName`<br>`Dom.Spec.AttrNameNormalized` |
| [concept-element-attributes-get-by-namespace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-get-by-namespace) | 2/2 | `Dom.getAttributeByKey`<br>`Dom.normalizeNamespace` | `Dom.Spec.AttrByKey` |
| [concept-element-attributes-get-value](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-get-value) | 3/3 | `Dom.getAttributeValue` |  |
| [concept-element-attributes-set](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-set) | 6/8（近似 1） | `Dom.setAttributeNode`<br>`Dom.findAttr`<br>`Dom.removeDetached` | `Dom.Spec.SetAttributeNodeResult` |
| [concept-element-attributes-set-value](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-set-value) | 3/3 | `Dom.setAttributeValue` | `Dom.Spec.SetAttributeValueResult` |
| [concept-element-attributes-remove-by-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-remove-by-name) | 2/3（近似 1） | `Dom.removeAttribute`<br>`Dom.removeNamedItem` | `Dom.Spec.RemoveAttributeResult`<br>`Dom.Spec.RemoveNamedItemResult` |
| [concept-element-attributes-remove-by-namespace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-element-attributes-remove-by-namespace) | 2/3（近似 1） | `Dom.removeAttributeNS` | `Dom.Spec.RemoveAttributeNSResult` |
| [dom-element-namespaceuri](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-namespaceuri) | 1/1 | `Dom.NodeData.namespace` |  |
| [dom-element-prefix](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-prefix) | 1/1 | `Dom.NodeData.prefix` |  |
| [dom-element-localname](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-localname) | 1/1 | `Dom.NodeData.localName` |  |
| [dom-element-tagname](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-tagname) | 1/1 | `Dom.tagName` |  |
| [concept-reflect](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-reflect) | 1/1 | `Dom.getReflected`<br>`Dom.getReflectedProp`<br>`Dom.setReflectedProp` |  |
| [dom-element-classlist](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-classlist) | 0/1（近似 1） | `Dom.classTokenSet`<br>`Dom.classListContains`<br>`Dom.classListAdd` |  |
| [dom-element-getattributenames](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-getattributenames) | 1/1 | `Dom.getAttributeNames` |  |
| [dom-element-getattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-getattribute) | 3/3 | `Dom.getAttribute`<br>`Dom.getAttributeByName` |  |
| [dom-element-setattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-setattribute) | 6/7 | `Dom.setAttribute`<br>`Dom.attrNameFor`<br>`Dom.isValidAttributeLocalName` | `Dom.Spec.SetAttributeResult` |
| [dom-element-setattributens](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-setattributens) | 2/3 | `Dom.setAttributeNS`<br>`Dom.validateAndExtractAttribute`<br>`Dom.setAttributeValue` | `Dom.Spec.SetAttributeValueResult` |
| [dom-element-removeattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-removeattribute) | 1/1 | `Dom.removeAttribute` | `Dom.Spec.RemoveAttributeResult` |
| [dom-element-removeattributens](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-removeattributens) | 1/1 | `Dom.removeAttributeNS` | `Dom.Spec.RemoveAttributeNSResult` |
| [dom-element-hasattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-hasattribute) | 2/2 | `Dom.hasAttribute`<br>`Dom.getAttributeByName` |  |
| [dom-element-toggleattribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-toggleattribute) | 8/8 | `Dom.toggleAttribute` | `Dom.Spec.ToggleAttributeResult` |
| [dom-element-getattributenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-getattributenode) | 1/1 | `Dom.getAttributeNode` |  |
| [dom-element-getattributenodens](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-getattributenodens) | 1/1 | `Dom.getAttributeNodeNS` |  |
| [dom-element-setattributenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-setattributenode) | 1/1 | `Dom.setAttributeNode` | `Dom.Spec.SetAttributeNodeResult` |
| [dom-element-removeattributenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-removeattributenode) | 3/3 | `Dom.removeAttributeNode`<br>`Dom.detachAttribute` | `Dom.Spec.RemoveAttributeNodeResult` |
| [dom-element-closest](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-closest) | 3/5（近似 2） | `Dom.closest`<br>`Dom.inclusiveAncestorElements` |  |
| [dom-element-matches](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-matches) | 1/3（近似 2） | `Dom.matchesSelector` |  |
| [dom-element-webkitmatchesselector](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-webkitmatchesselector) | 1/3（近似 2） | `Dom.matchesSelector` |  |
| [dom-element-getelementsbyclassname](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-element-getelementsbyclassname) | 0/1（近似 1） | `Dom.getElementsByClassName`<br>`Dom.elementClassesOf` |  |

### §4.9.1（`interface-namednodemap`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-namednodemap-getnameditem](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-namednodemap-getnameditem) | 0/1（近似 1） | `Dom.getAttributeNode`<br>`Dom.getAttributeByName` |  |
| [dom-namednodemap-getnameditemns](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-namednodemap-getnameditemns) | 0/1（近似 1） | `Dom.getAttributeNodeNS`<br>`Dom.getAttributeByKey` |  |
| [dom-namednodemap-setnameditem](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-namednodemap-setnameditem) | 0/1（近似 1） | `Dom.setAttributeNode` |  |
| [dom-namednodemap-setnameditemns](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-namednodemap-setnameditemns) | 0/1（近似 1） | `Dom.setAttributeNode` |  |
| [dom-namednodemap-removenameditem](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-namednodemap-removenameditem) | 3/3 | `Dom.removeNamedItem`<br>`Dom.removeAttributeNode` | `Dom.Spec.RemoveNamedItemResult` |

### §4.9.2（`interface-attr`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [create-an-attribute](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-an-attribute) | 2/3（近似 1） | `Dom.createAttributeIn`<br>`Dom.Attr.normalized` |  |
| [dom-attr-namespaceuri](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-namespaceuri) | 1/1 | `Dom.findAttr`<br>`Dom.Attr.namespace` |  |
| [dom-attr-prefix](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-prefix) | 1/1 | `Dom.findAttr`<br>`Dom.Attr.prefix` |  |
| [dom-attr-localname](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-localname) | 1/1 | `Dom.findAttr`<br>`Dom.Attr.localName` |  |
| [dom-attr-name](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-name) | 1/1 | `Dom.findAttr`<br>`Dom.Attr.qualifiedName` |  |
| [dom-attr-value](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-value) | 1/1 | `Dom.findAttr`<br>`Dom.Attr.value` |  |
| [set-an-existing-attribute-value](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#set-an-existing-attribute-value) | 3/5 | `Dom.setAttrValue`<br>`Dom.modifyAttr`<br>`Dom.changeAttribute` |  |
| [dom-attr-value/setter](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-value) | 1/1 | `Dom.setAttrValue` |  |
| [dom-attr-ownerelement](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-attr-ownerelement) | 1/1 | `Dom.attrOwnerElement`<br>`Dom.ownerElementOf` |  |

### §4.10（`interface-characterdata`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-cd-replace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-cd-replace) | 8/13（近似 3） | `Dom.replaceData`<br>`Dom.adjustedCount`<br>`Dom.spliceData?`<br>`Dom.queueCharacterDataRecord`<br>`Dom.replaceDataAdjustRange`<br>`Dom.replaceDataAdjustBP` | `Dom.Spec.ReplaceDataSpec`<br>`Dom.Spec.ReplaceDataResult` |
| [concept-cd-substring](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-cd-substring) | 2/4（近似 2） | `Dom.substringData`<br>`Dom.adjustedCount` |  |
| [dom-characterdata-data](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-data) | 1/1 | `Dom.NodeData.data`<br>`Dom.setData` | `Dom.Spec.SetDataResult` |
| [dom-characterdata-length](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-length) | 1/1 | `Dom.NodeData.length`<br>`Dom.Utf16.length` |  |
| [dom-characterdata-substringdata](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-substringdata) | 1/1 | `Dom.substringData` |  |
| [dom-characterdata-appenddata](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-appenddata) | 1/1 | `Dom.appendData` | `Dom.Spec.AppendDataResult` |
| [dom-characterdata-insertdata](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-insertdata) | 1/1 | `Dom.insertData` | `Dom.Spec.ReplaceDataResult` |
| [dom-characterdata-deletedata](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-deletedata) | 1/1 | `Dom.deleteData` | `Dom.Spec.ReplaceDataResult` |
| [dom-characterdata-replacedata](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-characterdata-replacedata) | 1/1 | `Dom.replaceData` | `Dom.Spec.ReplaceDataResult` |

### §4.11（`interface-text`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [exclusive-text-node](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#exclusive-text-node) | 1/1 | `Dom.isExclusiveText` | `Dom.Spec.ExclusiveText` |
| [contiguous-exclusive-text-nodes](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#contiguous-exclusive-text-nodes) | 0/1（近似 1） | `Dom.followingTexts`<br>`Dom.isExclusiveText` | `Dom.Spec.FollowingContiguousTexts` |
| [concept-descendant-text-content](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-descendant-text-content) | 1/1 | `Dom.descendantTextContent` |  |
| [create-a-text-node](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-a-text-node) | 3/3 | `Dom.createTextNode`<br>`Dom.withFresh` |  |

### §4.14（`interface-comment`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [create-a-comment-node](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#create-a-comment-node) | 3/3 | `Dom.createComment`<br>`Dom.withFresh` |  |

### §5.2（`boundary-points`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-range-bp-position](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-range-bp-position) | 6/8（近似 2） | `Dom.bpPosition`<br>`Dom.bpPositionDown`<br>`Dom.childTowards` | `Dom.Spec.BPBefore` |

### §5.3（`interface-abstractrange`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [range-collapsed](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#range-collapsed) | 0/1（近似 1） | `Dom.rangeDeleteContents`<br>`Dom.rangeInsertNode` |  |
| [dom-range-startcontainer](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-startcontainer) | 1/1 | `Dom.RangeState.start`<br>`Dom.BoundaryPoint.node`<br>`Dom.observe` |  |
| [dom-range-startoffset](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-startoffset) | 1/1 | `Dom.RangeState.start`<br>`Dom.BoundaryPoint.offset`<br>`Dom.observe` |  |
| [dom-range-endcontainer](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-endcontainer) | 1/1 | `Dom.RangeState.end`<br>`Dom.BoundaryPoint.node`<br>`Dom.observe` |  |
| [dom-range-endoffset](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-endoffset) | 1/1 | `Dom.RangeState.end`<br>`Dom.BoundaryPoint.offset`<br>`Dom.observe` |  |

### §5.5（`interface-range`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [live-range-pre-remove-steps](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#live-range-pre-remove-steps) | 7/7 | `Dom.liveRangePreRemove`<br>`Dom.liveRangePreRemoveRange`<br>`Dom.liveRangePreRemoveBP`<br>`Dom.rangeMoveOutOfSubtree`<br>`Dom.rangeShiftAfterRemove` | `Dom.Spec.RangeAdjusted`<br>`Dom.Spec.BoundaryAdjusted`<br>`Dom.liveRangePreRemoveBP_comm` |
| [concept-range-bp-set](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-range-bp-set) | 3/8（近似 5） | `Dom.setStartBP`<br>`Dom.setEndBP`<br>`Dom.rangeBoundaryError`<br>`Dom.rangeNeedsCollapse` | `Dom.Spec.StartSet`<br>`Dom.Spec.EndSet`<br>`Dom.Spec.BoundaryPointError`<br>`Dom.Spec.BoundaryPointOk` |
| [dom-range-setstart](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setstart) | 1/1 | `Dom.rangeSetStart` | `Dom.Spec.SetStartResult` |
| [dom-range-setend](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setend) | 1/1 | `Dom.rangeSetEnd` | `Dom.Spec.SetEndResult` |
| [dom-range-setstartbefore](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setstartbefore) | 3/3 | `Dom.rangeSetStartSibling`<br>`Dom.siblingBP` | `Dom.Spec.SetStartSiblingResult`<br>`Dom.Spec.SiblingPoint` |
| [dom-range-setstartafter](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setstartafter) | 3/3 | `Dom.rangeSetStartSibling`<br>`Dom.siblingBP` | `Dom.Spec.SetStartSiblingResult`<br>`Dom.Spec.SiblingPoint` |
| [dom-range-setendbefore](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setendbefore) | 3/3 | `Dom.rangeSetEndSibling`<br>`Dom.siblingBP` | `Dom.Spec.SetEndSiblingResult`<br>`Dom.Spec.SiblingPoint` |
| [dom-range-setendafter](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-setendafter) | 3/3 | `Dom.rangeSetEndSibling`<br>`Dom.siblingBP` | `Dom.Spec.SetEndSiblingResult`<br>`Dom.Spec.SiblingPoint` |
| [dom-range-collapse](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-collapse) | 1/1 | `Dom.rangeCollapse` | `Dom.Spec.CollapseResult` |
| [concept-range-select](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-range-select) | 5/5 | `Dom.rangeSelectNode` | `Dom.Spec.SelectNodeResult` |
| [dom-range-selectnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-selectnode) | 1/1 | `Dom.rangeSelectNode` | `Dom.Spec.SelectNodeResult` |
| [dom-range-selectnodecontents](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-selectnodecontents) | 4/4 | `Dom.rangeSelectNodeContents` | `Dom.Spec.SelectNodeContentsResult` |
| [dom-range-compareboundarypoints](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-compareboundarypoints) | 5/5 | `Dom.rangeCompareBoundaryPoints`<br>`Dom.bpPosition` | `Dom.Spec.CompareBoundaryPointsResult`<br>`Dom.Spec.compareHowPoints`<br>`Dom.Spec.PositionResult` |
| [dom-range-deletecontents](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-deletecontents) | 16/16 | `Dom.rangeDeleteContents`<br>`Dom.nodesToRemove`<br>`Dom.containedInRange`<br>`Dom.deleteContentsNewBP`<br>`Dom.removeEach`<br>`Dom.replaceData` | `Dom.Spec.DeleteContentsResult`<br>`Dom.Spec.NodesToRemove`<br>`Dom.Spec.Contained`<br>`Dom.Spec.DeleteNewBP`<br>`Dom.Spec.rangeDeleteContents_result_sound` |
| [concept-range-insert](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-range-insert) | 12/13 | `Dom.rangeInsertNode`<br>`Dom.ensurePreInsertionValidity`<br>`Dom.preInsert`<br>`Dom.remove`<br>`Dom.siblingBP` | `Dom.Spec.InsertNodeResult`<br>`Dom.Spec.InsertNodeTail`<br>`Dom.Spec.NewOffset`<br>`Dom.Spec.InsertNodeHierarchyError`<br>`Dom.Spec.ChildAtOffset` |
| [dom-range-insertnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-insertnode) | 1/1 | `Dom.rangeInsertNode` | `Dom.Spec.InsertNodeResult` |
| [dom-range-ispointinrange](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-ispointinrange) | 5/5 | `Dom.rangeIsPointInRange` | `Dom.Spec.IsPointInRangeResult` |
| [dom-range-comparepoint](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-comparepoint) | 6/6 | `Dom.rangeComparePoint` | `Dom.Spec.ComparePointResult` |
| [dom-range-intersectsnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-intersectsnode) | 6/6 | `Dom.rangeIntersectsNode` | `Dom.Spec.IntersectsNodeResult` |
| [dom-range-stringifier](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-range-stringifier) | 2/6（近似 4） | `Dom.rangeToString`<br>`Dom.containedInRange`<br>`Dom.substringData` |  |

### §6（`traversal`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-node-filter](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-node-filter) | 2/8（近似 1） | `Dom.showsNode`<br>`Dom.walkerAccepts` |  |

### §6.1（`interface-nodeiterator`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [nodeiterator-pre-removing-steps](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#nodeiterator-pre-removing-steps) | 1/2 | `Dom.iteratorPreRemove`<br>`Dom.iteratorPreRemoveOne` | `Dom.Spec.IteratorAdjusted` |
| [nodeiterator-adjust-a-node-pointer](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#nodeiterator-adjust-a-node-pointer) | 6/6 | `Dom.adjustNodePointer`<br>`Dom.firstFollowingOutside` | `Dom.Spec.PointerAdjusted`<br>`Dom.Spec.FirstFollowingOutside`<br>`Dom.Spec.LastBeforeRemoval` |
| [dom-nodeiterator-root](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-root) | 1/1 | `Dom.IteratorState.root`<br>`Dom.observe` |  |
| [dom-nodeiterator-referencenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-referencenode) | 1/1 | `Dom.IteratorState.reference`<br>`Dom.observe` |  |
| [dom-nodeiterator-pointerbeforereferencenode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-pointerbeforereferencenode) | 1/1 | `Dom.IteratorState.pointerBeforeReference`<br>`Dom.observe` |  |
| [dom-nodeiterator-whattoshow](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-whattoshow) | 1/1 | `Dom.IteratorState.whatToShow`<br>`Dom.observe` |  |
| [concept-nodeiterator-traverse](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-nodeiterator-traverse) | 1/21（近似 20） | `Dom.nextNode`<br>`Dom.previousNode`<br>`Dom.iteratorCollection`<br>`Dom.showsNode`<br>`Dom.Exec.stepIterator` |  |
| [dom-nodeiterator-nextnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-nextnode) | 1/1 | `Dom.nextNode`<br>`Dom.Exec.stepIterator` |  |
| [dom-nodeiterator-previousnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-nodeiterator-previousnode) | 1/1 | `Dom.previousNode`<br>`Dom.Exec.stepIterator` |  |

### §6.2（`interface-treewalker`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [dom-treewalker-root](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-root) | 1/1 | `Dom.WalkerState.root`<br>`Dom.observe` |  |
| [dom-treewalker-whattoshow](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-whattoshow) | 1/1 | `Dom.WalkerState.whatToShow`<br>`Dom.observe` |  |
| [dom-treewalker-currentnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-currentnode) | 1/1 | `Dom.WalkerState.current`<br>`Dom.observe` |  |
| [dom-treewalker-parentnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-parentnode) | 2/5（近似 3） | `Dom.walkerParentNode`<br>`Dom.takeUntilIncl`<br>`Dom.walkerStep`<br>`Dom.walkerRun` |  |
| [concept-traverse-children](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-traverse-children) | 1/15（近似 14） | `Dom.walkerFirstChild`<br>`Dom.walkerLastChild`<br>`Dom.mirrorPreorder`<br>`Dom.walkerStep`<br>`Dom.walkerRun` |  |
| [dom-treewalker-firstchild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-firstchild) | 1/1 | `Dom.walkerFirstChild`<br>`Dom.walkerStep` |  |
| [dom-treewalker-lastchild](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-lastchild) | 1/1 | `Dom.walkerLastChild`<br>`Dom.walkerStep` |  |
| [concept-traverse-siblings](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-traverse-siblings) | 2/13（近似 11） | `Dom.walkerSibling`<br>`Dom.walkerSiblingSearch`<br>`Dom.siblingCandidates`<br>`Dom.followingSiblings`<br>`Dom.precedingSiblings`<br>`Dom.walkerStep`<br>`Dom.walkerRun` |  |
| [dom-treewalker-nextsibling](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-nextsibling) | 1/1 | `Dom.walkerSibling`<br>`Dom.walkerStep` |  |
| [dom-treewalker-previoussibling](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-previoussibling) | 1/1 | `Dom.walkerSibling`<br>`Dom.walkerStep` |  |
| [dom-treewalker-previousnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-previousnode) | 2/15（近似 13） | `Dom.walkerPreviousNode`<br>`Dom.walkerBase`<br>`Dom.walkerStep`<br>`Dom.walkerRun` |  |
| [dom-treewalker-nextnode](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-treewalker-nextnode) | 2/18（近似 16） | `Dom.walkerNextNode`<br>`Dom.walkerBase`<br>`Dom.walkerStep`<br>`Dom.walkerRun` |  |

### §7.1（`interface-domtokenlist`）

| algorithm | step | 実行関数 | 関係 |
| --- | --- | --- | --- |
| [concept-dtl-update](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-dtl-update) | 0/2（近似 2） | `Dom.tokenListUpdate`<br>`Dom.getAttributeByKey`<br>`Dom.setAttributeValue` |  |
| [concept-dtl-serialize](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#concept-dtl-serialize) | 0/1（近似 1） | `Dom.getAttributeValue` |  |
| [algorithm:DOMTokenList/attribute change steps](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#algorithm:DOMTokenList/attribute change steps) | 0/2（近似 2） | `Dom.classTokenSet`<br>`Dom.orderedSetParse` |  |
| [algorithm:DOMTokenList/created](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#algorithm:DOMTokenList/created) | 0/4（近似 4） | `Dom.classTokenSet` |  |
| [dom-domtokenlist-contains](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-domtokenlist-contains) | 1/1 | `Dom.classListContains`<br>`Dom.classTokenSet` |  |
| [dom-domtokenlist-add](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-domtokenlist-add) | 5/5 | `Dom.classListAdd`<br>`Dom.validateTokens`<br>`Dom.validateToken`<br>`Dom.orderedSetAppend`<br>`Dom.tokenListUpdate` |  |
| [dom-domtokenlist-remove](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-domtokenlist-remove) | 5/5 | `Dom.classListRemove`<br>`Dom.validateTokens`<br>`Dom.validateToken`<br>`Dom.tokenListUpdate` |  |
| [dom-domtokenlist-toggle](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-domtokenlist-toggle) | 7/7 | `Dom.classListToggle`<br>`Dom.validateToken`<br>`Dom.tokenListUpdate` |  |
| [dom-domtokenlist-replace](https://dom.spec.whatwg.org/commit-snapshots/a2331a45360129e8645ef7e0a04740241b6e3726/#dom-domtokenlist-replace) | 6/6 | `Dom.classListReplace`<br>`Dom.orderedSetReplace`<br>`Dom.tokenListUpdate` |  |

## 外した step

| algorithm | step | 理由 |
| --- | --- | --- |
| validate-and-extract | 5 | other：assert。step 4.3 の分岐から従うので検査しない |
| add-an-event-listener | 1 | host |
| add-an-event-listener | 2 | todo：AbortSignal と listener の signal を持たない |
| add-an-event-listener | 3 | other：callback は scenario の番号で、null にならない |
| add-an-event-listener | 4 | todo：passive を持たない |
| add-an-event-listener | 6 | todo：AbortSignal と listener の signal を持たない |
| remove-an-event-listener | 1 | host |
| dom-eventtarget-dispatchevent | 1 | other：Event object を持たず、配送ごとに新しい EventState を作るので、dispatch flag が立った event や初期化されていない event は渡せない |
| dom-eventtarget-dispatchevent | 2 | other：isTrusted を持たない（常に false として扱う） |
| concept-event-dispatch | 1 | other：dispatch flag を持たない。callback が model の外で、配送中に同じ event を配送し直すことが起きない |
| concept-event-dispatch | 3 | hook |
| concept-event-dispatch | 4 | shadow |
| concept-event-dispatch | 5 | shadow |
| concept-event-dispatch | 6.1-6.2 | shadow |
| concept-event-dispatch | 6.4-6.5 | hook |
| concept-event-dispatch | 6.6-6.7 | shadow |
| concept-event-dispatch | 6.9.1-6.9.5 | shadow |
| concept-event-dispatch | 6.9.6.1 | hook |
| concept-event-dispatch | 6.9.7 | shadow |
| concept-event-dispatch | 6.9.8 | shadow |
| concept-event-dispatch | 6.9.10 | shadow |
| concept-event-dispatch | 6.10-6.11 | shadow |
| concept-event-dispatch | 6.12 | hook |
| concept-event-dispatch | 11 | shadow |
| concept-event-dispatch | 12 | hook |
| concept-event-path-append | 1-4 | shadow |
| concept-event-listener-invoke | 1-3 | other：Event の target 属性を持たない（shadow tree が無いので配送中は常に target で、callback は model の外なので観測されない） |
| concept-event-listener-invoke | 4-5 | shadow |
| concept-event-listener-invoke | 9 | shadow |
| concept-event-listener-invoke | 11 | other：isTrusted が常に false なので起きない |
| concept-event-listener-inner-invoke | 1 | other：found を計算しない。使い道の invoke step 11 が isTrusted=false で起きない |
| concept-event-listener-inner-invoke | 2.2 | other：found を計算しない |
| concept-event-listener-inner-invoke | 2.6-2.8 | host |
| concept-event-listener-inner-invoke | 2.9 | todo：passive と in passive listener flag を持たない |
| concept-event-listener-inner-invoke | 2.10 | host |
| concept-event-listener-inner-invoke | 2.11.1-2.11.2 | host |
| concept-event-listener-inner-invoke | 2.12 | todo：passive と in passive listener flag を持たない |
| concept-event-listener-inner-invoke | 2.13 | host |
| concept-event-listener-inner-invoke | 3 | other：found を返さない |
| concept-node-insert | 7.4-7.6 | shadow |
| concept-node-insert | 7.7.1 | hook |
| concept-node-insert | 7.7.2-7.7.4 | custom-elements |
| concept-node-insert | 9 | hook |
| concept-node-insert | 10-12 | hook |
| move | 14-16 | shadow |
| move | 21-23 | shadow |
| move | 24.1-24.2 | hook |
| move | 24.3 | custom-elements |
| concept-node-remove | 8-10 | shadow |
| concept-node-remove | 11 | hook |
| concept-node-remove | 12-13 | custom-elements |
| concept-node-remove | 14.1 | hook |
| concept-node-remove | 14.2 | custom-elements |
| concept-node-remove | 17 | hook |
| notify-mutation-observers | 4-5 | shadow |
| notify-mutation-observers | 7 | shadow |
| concept-node-clone | 3 | hook |
| concept-node-clone | 6 | shadow |
| clone-a-single-node | 2.1-2.3 | custom-elements |
| clone-a-single-node | 5.2 | custom-elements |
| dom-node-clonenode | 1 | shadow |
| dom-document-createelement | 3 | custom-elements |
| internal-createelementns-steps | 2 | custom-elements |
| dom-document-importnode | 3 | custom-elements |
| dom-document-importnode | 5.1 | todo：ImportNodeOptions の dictionary の形を受けない（boolean の形だけ） |
| dom-document-importnode | 5.2-5.3 | custom-elements |
| dom-document-importnode | 6 | custom-elements |
| concept-node-adopt | 3.2 | shadow |
| concept-node-adopt | 3.3.2 | custom-elements |
| concept-node-adopt | 3.3.3 | custom-elements |
| concept-node-adopt | 3.4 | hook |
| dom-document-adoptnode | 2 | shadow |
| concept-create-element | 2-5 | custom-elements |
| concept-create-element | 6.3 | custom-elements |
| handle-attribute-changes | 2 | custom-elements |
| handle-attribute-changes | 3 | hook |
| concept-element-attributes-set | 1 | other：Trusted Types（get trusted type compliant attribute value）は対象外 |
| dom-element-setattribute | 3 | other：Trusted Types（get trusted type compliant attribute value）は対象外 |
| dom-element-setattributens | 2 | other：Trusted Types（get trusted type compliant attribute value）は対象外 |
| set-an-existing-attribute-value | 3 | other：Trusted Types（get trusted type compliant attribute value）は対象外 |
| set-an-existing-attribute-value | 4 | other：step 3 が script を走らせないので、attribute の element は step 1 の判定から変わらない |
| concept-cd-replace | 12 | todo：ProcessingInstruction の attribute map（update attributes from data）が model に無い |
| concept-cd-replace | 13 | hook |
| concept-range-insert | 7 | todo：Text node の split（§4.11 split a Text node）が model に無い。start node が Text なら step 6 の validity を通った後で outsideModel を返す |
| concept-node-filter | 1 | host |
| concept-node-filter | 5-8 | host |
| nodeiterator-pre-removing-steps | 2 | other：candidate reference は traverse の途中（filter の callback の中）でしか非 null にならず、filter が null なので状態に持たない |

## 近似した step

| algorithm | step | 仕様との違い |
| --- | --- | --- |
| concept-ordered-set-parser | 2-3 | ordered set を List String で持ち、`eraseDups` で後から重複を落とす（最初の出現を残すので append を繰り返したのと同じ列） |
| concept-ordered-set-serializer | * | 専用の関数は無く、DOMTokenList の update steps（`tokenListUpdate`）の中で `" ".intercalate` として書いている |
| scope-match-a-selectors-string | 1 | parse a selector は model の selector 文法（`parseSelector` が受け付ける部分集合）で行う。受け付けない構文は failure（SyntaxError）になる |
| dom-event-stoppropagation | * | callback の中の呼び出しではなく、listener の `ListenerAction.stopPropagation` として callback の後に一度だけ走る |
| dom-event-stopimmediatepropagation | * | listener の `ListenerAction.stopImmediatePropagation` として走る |
| set-the-canceled-flag | * | in passive listener flag を持たない（passive を扱わない）ので、cancelable だけで決まる |
| dom-event-preventdefault | * | listener の `ListenerAction.preventDefault` として走る |
| add-an-event-listener | 5 | listener list を EventTarget ごとではなく一本の list に `target` 付きで持つ。外した listener は `removed` を立てて残すので、それを除いて重複を探す |
| dom-eventtarget-addeventlistener | 1 | options の flatten は harness が済ませ、capture と once を Bool で受け取る。passive と signal は無い |
| dom-eventtarget-addeventlistener | 2 | callback は scenario の `source` 番の listener のもの（番号と `ListenerAction`）を使い回す。target か source が無ければ（model の都合で）NotFoundError |
| remove-an-event-listener | 2 | list から取り除かず `removed` を立てるだけにする。以後の検索と配送は `removed` の listener を飛ばす |
| dom-eventtarget-removeeventlistener | 1 | options の flatten は harness が済ませ、capture を Bool で受け取る |
| dom-eventtarget-dispatchevent | 3 | event は引数の type・bubbles・cancelable からその場で作る（`new Event(type, {bubbles, cancelable})` と dispatchEvent を合わせた形） |
| concept-event-dispatch | 2 | legacy target override flag（Window の場合）が無いので targetOverride は target そのもの |
| concept-event-dispatch | 6 | relatedTarget を持たない（null）ので、条件は常に真として step 6 の中身を走らせる |
| concept-event-dispatch | 6.3 | event path の item は node だけを持ち、shadow-adjusted target を持つのは先頭の target だけ（`runPass` の `isTarget`） |
| concept-event-dispatch | 6.8 | get the parent は parent をそのまま返す。Document の get the parent は（Window が無いので）null |
| concept-event-dispatch | 6.9.6 | shadow tree が無いので、parent は常に target と同じ tree にあり、この分岐を常に取る（shadow-adjusted target は null） |
| concept-event-dispatch | 6.9.9 | get the parent は parent をそのまま返す。Document の get the parent は（Window が無いので）null |
| concept-event-dispatch | 6.13-6.14 | legacyOutputDidListenersThrowFlag を渡さない（callback が例外を投げない） |
| concept-event-dispatch | 7-10 | EventState を配送の終わりに捨てるので、フラグと eventPhase の後始末は結果に現れない |
| concept-event-path-append | 5 | item は invocation target の node だけ。shadow-adjusted target は `runPass` が先頭（target）かどうかで決め、relatedTarget と touch target list は持たない |
| concept-event-listener-invoke | 7 | currentTarget は event に持たず、`innerInvoke` の引数 `cur` として呼び出しの記録（`Invocation`）に残す |
| concept-event-listener-invoke | 8 | clone は listener の index の列。外された listener は clone の時点で除き、その後に外されたものは inner invoke が現在の状態の `removed` を見て飛ばす |
| concept-event-listener-inner-invoke | 2.11 | callback を呼ぶ代わりに、listener の `ListenerAction`（stopPropagation・preventDefault・listener の追加と削除など）を `runAction` で走らせる。callback は例外を投げない |
| concept-node-length | 1 | Attr は木の node ではない（NodeKind に無い）ので、DocumentType だけが 0 になる |
| move | 1 | shadow-including root ではなく root で比べる（shadow tree が無いので同じ値） |
| dom-parentnode-children | * | live な HTMLCollection は作らない。collection が表す element children をその時点の list として返す。harness に操作は無く、`childrenNamedItem` の中でだけ使う |
| dom-parentnode-append | 1 | 可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る |
| dom-parentnode-replacechildren | 1 | 可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る |
| dom-parentnode-queryselectorall | * | static な NodeList ではなく、element の list を返す |
| dom-childnode-before | 4 | 可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る。そのため step 1-3 は変換の後の木で評価され、nodes は [node] になる |
| dom-childnode-after | 4 | 可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る。そのため step 1-3 は変換の後の木で評価され、nodes は [node] になる |
| dom-childnode-replacewith | 4 | 可変長の nodes と文字列を node にまとめる変換はしない。呼び出し側がまとめた一つの node を受け取る。step 1-3 は変換の後の木で評価され、nodes は [node] になる |
| dom-childnode-replacewith | 5-6 | step 1 と step 5 の間で木が変わらないので、step 5 の条件は常に真になる（this が nodes に入っていて fragment に移る場合を区別しない） |
| dom-htmlcollection-nameditem | * | collection は `ParentNode.children` のものに限る（他の HTMLCollection は model に無い） |
| queue-a-mutation-observer-compound-microtask | 3 | microtask は積まず、flag を立てるだけである。notify mutation observers は harness の `notify` 操作として呼ぶ |
| notify-mutation-observers | 6.3 | node list の node に限らず、その observer の transient registered observer を全部外す。remove が transient を置いた node を node list にも足す（`addTransientObservers`）ので同じ結果になる |
| notify-mutation-observers | 6.4 | callback は呼ばない。records が空でない observer と records の組を返り値に並べる |
| dom-mutationobserver-observe | 7 | target の registered observer list のうち transient でないものだけを見る。transient registered observer しか無ければ step 8 に進む。固定版の本文は transient も探すが、whatwg/dom 3071e5f で本文もこの読みに改められた |
| dom-mutationobserver-observe | 7.1 | node list の node に限らず、source が target のこの observer の transient を全部外す。source は registered observer ではなく、その node で表す |
| dom-mutationobserver-disconnect | 1 | node list の node に限らず、この observer の registered observer を全部外す |
| create-a-node | 2 | realm を持たない。node document を与えた `NodeData` を `freshId` の位置に置く |
| dom-node-nodetype | * | `NodeKind` に Attr が無いので ATTRIBUTE_NODE (2) は返らない（`Attr` は木の外の別の型）。harness に getter の操作は無い |
| dom-node-ownerdocument | * | `ownerDocumentOf` は Document に対して null ではなく自分自身を返す（model の Document は自分を node document に持つ） |
| dom-node-getrootnode | * | options["composed"] を受けず、常に root を返す（shadow tree が無いので shadow-including root と同じ値） |
| dom-node-childnodes | * | live な NodeList ではなく、読んだ時点の children の列を返す |
| dom-node-nodevalue/setter | * | setter として振り分ける関数は無い。Attr の枝は `setAttrValue`（harness の `setAttrValue` の via = nodeValue）、CharacterData の枝は同じ replace data をする `setData` が担う。「Otherwise 何もしない」の枝と null → 空文字列の変換は model に無い |
| dom-node-normalize | 3-4 | run 全体を一度に連結して replace data を一回呼ぶのではなく、engine に合わせて兄弟ごとに replace data する（data が空の兄弟では呼ばない）。木と range の最終状態は同じで、characterData record の並びが違う |
| dom-node-normalize | 6 | 兄弟ごとに boundary point を渡してからその兄弟を remove する。step 6 と step 7 を兄弟ごとに交互に行う |
| dom-node-normalize | 7 | 兄弟ごとに step 6 の直後に remove する（上と同じ） |
| clone-a-single-node | 2.4 | create an element を呼ばず、`NodeData` を写して element を作る（is value・custom element の処理は無い） |
| clone-a-single-node | 5 | DocumentType の name・public ID・system ID と ProcessingInstruction の target を model が持たないので写さない |
| clone-a-single-node | 5.1 | Document の持ち物のうち model にあるのは type（`isHTMLDocument`）と mode だけで、それを写す。encoding・content type・URL・origin・allow declarative shadow roots は無い |
| concept-node-equals | * | DocumentType の name・public ID・system ID と ProcessingInstruction の target は model に無いので比べない（harness はどちらも固定値で作る） |
| dom-node-isequalnode | * | otherNode に null を受けない |
| dom-node-contains | * | other に null を受けない |
| dom-document-getelementsbyclassname | * | live な HTMLCollection ではなく、呼んだ時点の element の列を返す |
| dom-document-createelement | 4 | content type を持たないので、namespace は「HTML document なら HTML namespace、そうでなければ null」で決める。content type が application/xhtml+xml の XML document でも null になる。runner は HTML document しか作れないので、XML document の側は差分テストで比べていない |
| dom-document-createelement | 5 | create an element を呼ばず、`NodeData` を直に作る（is・synchronous custom elements flag・registry は無い） |
| internal-createelementns-steps | 3 | create an element を呼ばず、`NodeData` を直に作る（is・registry は無い） |
| dom-document-createelementns | * | options を受けない |
| dom-document-importnode | 1 | Document だけを弾く。shadow root は model に無いので検査しない |
| dom-document-importnode | 7 | fallbackRegistry を渡さない（custom element registry が無い） |
| concept-node-adopt | 3 | shadow-including inclusive descendant ではなく inclusive descendant をたどる（shadow tree が無いので同じ集合） |
| concept-tree-host-including-inclusive-ancestor | * | host を見ない。shadow root が無いので inclusive ancestor と同じ |
| concept-create-element | 6.1 | element interface を持たない。interface は namespace と local name から決まるものとして扱う |
| create-an-element-internal | 1 | interface を持たない。node kind が element の `NodeData` を作る |
| create-an-element-internal | 2 | custom element registry・custom element state・is value は持たない（custom element は対象外）。namespace・prefix・local name・node document だけを置く |
| concept-element-attributes-change | 2 | attribute は element の状態なので、attribute list の中の同じ鍵の要素を差し替える |
| concept-element-attributes-append | 2 | attribute の element は持たず、attribute list に入っていることで表す |
| concept-element-attributes-remove | 3 | element を null にした `Attr` は detachedAttrs に足して表す。ただし名前で消す経路（removeAttributeFrom：removeAttribute・removeAttributeNS・toggleAttribute・reflect の boolean setter・dataset の deleter）は `Attr` を捨てる |
| concept-element-attributes-replace | 3 | newAttribute の element は attribute list に入っていることで表す |
| concept-element-attributes-replace | 5 | oldAttribute の element を null にすることを、detachedAttrs の末尾に足して表す |
| concept-element-attributes-set | 5 | step 1 が無いので verifiedValue は attr の value と同じで、書き換えは何もしない |
| concept-element-attributes-remove-by-name | 3 | removeAttribute は戻り値を捨てるので、取り除いた `Attr` を状態に残さない（removeNamedItem は残す） |
| concept-element-attributes-remove-by-namespace | 3 | removeAttributeNS は戻り値を捨てるので、取り除いた `Attr` を状態に残さない |
| dom-element-classlist | * | DOMTokenList object を持たず、各 method が element を受けて class attribute の値から token set を読み直す |
| dom-element-closest | 1-2 | parse a selector は model の Selectors の部分集合（`Dom/Selector/`） |
| dom-element-matches | 1-2 | parse a selector は model の Selectors の部分集合（`Dom/Selector/`） |
| dom-element-webkitmatchesselector | 1-2 | parse a selector は model の Selectors の部分集合（`Dom/Selector/`） |
| dom-element-getelementsbyclassname | * | live な HTMLCollection ではなく、呼んだ時点の element の列を返す |
| dom-namednodemap-getnameditem | * | NamedNodeMap object を持たない。同じ algorithm（get an attribute by name）を呼ぶ getAttributeNode で計算する |
| dom-namednodemap-getnameditemns | * | NamedNodeMap object を持たない。同じ algorithm を呼ぶ getAttributeNodeNS で計算する |
| dom-namednodemap-setnameditem | * | NamedNodeMap object を持たない。同じ algorithm（set an attribute）を呼ぶ setAttributeNode で計算する |
| dom-namednodemap-setnameditemns | * | NamedNodeMap object を持たない。同じ algorithm（set an attribute）を呼ぶ setAttributeNode で計算する |
| create-an-attribute | 1 | node tree には入れず、detachedAttrs に足す。id は freshStateAttrId |
| concept-cd-replace | 5-7 | offset か offset + count が surrogate pair の途中なら、結果の文字列を Lean の String で表せないので __outsideModel__ を返す |
| concept-cd-substring | 3-4 | offset か offset + count が surrogate pair の途中なら、結果の文字列を Lean の String で表せないので __outsideModel__ を返す |
| contiguous-exclusive-text-nodes | * | node より後ろの兄弟だけを集める（normalize が run の先頭から呼ぶので前側は空になる）。前後両側を集める関数は無い |
| concept-range-bp-position | 1 | assert は書かない。呼び出し側（`BoundaryLE`・`rangeNeedsCollapse` など）が root を別に比べる |
| concept-range-bp-position | 3 | 自分自身を入れ替えて呼ぶ代わりに、`bpPositionDown` を入れ替えて呼んだ結果を `swap` する（入れ子は高々一段） |
| range-collapsed | * | 専用の定義は無く、使う側（deleteContents step 1・insert step 13）が `r.start == r.end` を直に書く |
| concept-range-bp-set | 4 | set the start では range の root を start node ではなく end node の root で比べる（妥当な range では同じ。spec 側は start node の root で書き、定理が RangeValid を仮定する） |
| dom-range-stringifier | 2-5 | UTF-16 の code unit で切り出す。surrogate pair の途中を指すと outsideModel になる |
| concept-node-filter | 4 | filter は常に null として扱うので、ここで必ず FILTER_ACCEPT を返す |
| concept-nodeiterator-traverse | 1-4 | candidate reference を持たず、iterator collection を reference で二つに分けて、pointer before に応じて reference 自身を候補に足した列から whatToShow を満たす最初の node を探す。filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある |
| dom-treewalker-parentnode | 2 | current の祖先を root まで（root を含む）並べ、accept される最初のものを取る |
| concept-traverse-children | 2-4 | current の（自身を除く）部分木を tree order（last なら鏡像）に並べた列で探す。filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある |
| concept-traverse-siblings | 3 | 段ごとに兄弟の部分木を順に並べた列で探し、見つからなければ親へ上がる。filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある |
| dom-treewalker-previousnode | 2 | `walkerBase`（current が root の外なら current 側の木の根）を根とする preorder を current の手前から逆にたどる。filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある |
| dom-treewalker-nextnode | 3 | `walkerBase` を根とする preorder を current の次からたどる。filter は常に null。whatToShow の bit だけで決まるので FILTER_REJECT が出ず、仕様の loop を「候補列の中で accept される最初の node」に書き直してある |
| concept-dtl-update | * | DOMTokenList は classList だけで、element と attribute name は（受け手の element, "class"）に固定 |
| concept-dtl-serialize | * | DOMTokenList は classList だけで、element と attribute name は（受け手の element, "class"）に固定。value の getter が無いので、serialize steps を直接呼ぶ所は無い |
| algorithm:DOMTokenList/attribute change steps | * | token set を状態に持たない。attribute change steps で更新する代わりに、使うたびに attribute の値から読み直す（値が無ければ空文字列なので空の set になる） |
| algorithm:DOMTokenList/created | * | DOMTokenList object を作らない。token set は使うたびに attribute の値から読み直す |

## 対象外とした algorithm

| 理由 | algorithm |
| --- | --- |
| custom-elements | dom-documentorshadowroot-customelementregistry, dom-element-customelementregistry, flatten-element-creation-options |
| hook | concept-node-adopt-ext, concept-node-children-changed-ext, concept-node-insert-ext, concept-node-move-ext, concept-node-post-connection-ext, concept-node-remove-ext |
| host | concept-event-create, dom-comment-comment, dom-document-document, dom-documentfragment-documentfragment, dom-nodeiterator-filter, dom-range-range, dom-text-text, dom-treewalker-filter, dom-window-event, inner-event-creation-steps, legacy-obtain-service-worker-fetch-event-listener-callbacks |
| legacy | dom-attr-specified, dom-customevent-initcustomevent, dom-domimplementation-hasfeature, dom-event-initevent, dom-event-srcelement, dom-nodeiterator-detach, dom-range-detach |
| other：HTML（document.open()）が使う道具。model の操作からは呼ばれず、実行関数も無い | remove-all-event-listeners |
| other：XPath（§8）は model の対象外。XPath の評価器を持たない | dom-xpathevaluatorbase-creatensresolver |
| other：callback（script の関数）は model の外。observer は scenario の初期状態でだけ作り、constructor に当たる操作は無い | dom-mutationobserver-mutationobserver |
| other：options の IDL 変換は harness が済ませ、capture・once を Bool で渡す | concept-flatten-options |
| other：options の IDL 変換は harness が済ませる。passive と signal は持たない | event-flatten-more |
| other：他の仕様（と §3 の abort steps）が使う道具。model の操作からは呼ばれない | concept-event-fire |
| shadow | assign-a-slot, assign-slotables, assign-slotables-for-a-tree, concept-attach-a-shadow-root, dom-element-attachshadow, dom-element-shadowroot, dom-shadowroot-clonable, dom-shadowroot-delegatesfocus, dom-shadowroot-host, dom-shadowroot-mode, dom-shadowroot-serializable, dom-shadowroot-slotassignment, dom-slotable-assignedslot, exclusive-documentfragment-node, find-a-slot, find-flattened-slotables, find-slotables, retarget, signal-a-slot-change |
| todo：AbortController と AbortSignal（abort reason・abort algorithms・dependent signal）が無い | abortcontroller-signal-abort, abortsignal-add, abortsignal-remove, abortsignal-signal-abort, create-a-dependent-abort-signal, dom-abortcontroller-abort, dom-abortcontroller-abortcontroller, dom-abortcontroller-signal, dom-abortsignal-abort, dom-abortsignal-aborted, dom-abortsignal-any, dom-abortsignal-reason, dom-abortsignal-throwifaborted, dom-abortsignal-timeout, run-the-abort-steps |
| todo：DOMImplementation object を持たない | dom-document-implementation |
| todo：DOMImplementation（createDocumentType・createDocument・createHTMLDocument）が無い。document を作る関数も、DocumentType の name・public ID・system ID も model に無い | dom-domimplementation-createdocument, dom-domimplementation-createdocumenttype, dom-domimplementation-createhtmldocument |
| todo：Document を作る関数が無い（clone a single node の step 3 だけは `cloneSingle` が `NodeData` を写して作る）。harness の document は scenario が与える | create-a-document |
| todo：DocumentType の name・public ID・system ID を持たない（create a doctype と三つの getter） | create-a-doctype, dom-documenttype-name, dom-documenttype-publicid, dom-documenttype-systemid |
| todo：Element・DocumentFragment の枝（string replace all）が無い。Attr の枝は `setAttrValue`（via = textContent）、CharacterData の枝は `setData` と同じ処理だが、set text content として振り分ける関数は無い | set-text-content |
| todo：Event object を作る API が無い（`dispatchEvent` が型・bubbles・cancelable から event を組む）。step 7 の timeStamp は host | dom-document-createevent |
| todo：Event object を持たず、composed flag も無い | dom-event-composed |
| todo：Event object を持たない。dispatchEvent が type・bubbles・cancelable から EventState をその場で作り、constructor・dictionary・timeStamp は無い | concept-event-constructor |
| todo：Event object を持たない。dispatchEvent が type・bubbles・cancelable から EventState をその場で作る | concept-event-initialize |
| todo：Event object を持たないので cancelBubble の getter が無い | dom-event-cancelbubble |
| todo：Event object を持たないので defaultPrevented の getter が無い（dispatchEvent の戻り値としてだけ canceled flag が見える） | dom-event-defaultprevented |
| todo：Event object を持たないので returnValue の getter が無い | dom-event-returnvalue |
| todo：Event object を持たないので target の getter が無い | dom-event-target |
| todo：HTMLCollection の supported property names（WebIDL の named property）の実行関数が無い | interface-htmlcollection/supported-property-names |
| todo：HTMLCollection を表す構造が無く、item の実行関数も無い | dom-htmlcollection-item |
| todo：HTMLCollection を表す構造が無く、length の実行関数も無い | dom-htmlcollection-length |
| todo：NamedNodeMap object を持たない（item(index) が無い） | dom-namednodemap-item |
| todo：NamedNodeMap object を持たない（length が無い） | dom-namednodemap-length |
| todo：NamedNodeMap object（element の attributes getter）を持たない | dom-element-attributes |
| todo：NamedNodeMap の named property が無い | interface-namednodemap/supported-property-names |
| todo：Node の nodeName を返す関数が無い（Element は `tagName`、Attr は harness の attrQuery で qualified name を読むだけ）。DocumentType の name と ProcessingInstruction の target も model に無い | dom-node-nodename |
| todo：NodeIterator を作る API が無い（iterator は scenario が与える） | dom-document-createnodeiterator |
| todo：ProcessingInstruction の target・attribute map・createProcessingInstruction が無い（XML Name production も無い） | create-a-processing-instruction-node, dom-processinginstruction-getattribute, dom-processinginstruction-getattributenames, dom-processinginstruction-hasattribute, dom-processinginstruction-hasattributes, dom-processinginstruction-processinginstruction, dom-processinginstruction-removeattribute, dom-processinginstruction-setattribute, dom-processinginstruction-target, dom-processinginstruction-toggleattribute, get-a-processing-instruction-attribute, processinginstruction-initialize, update-attributes-from-data, update-data-from-attributes |
| todo：Range object を作る API が無い（range は scenario が与える。`Dom/Range/Api.lean` の注） | dom-document-createrange |
| todo：Range object を新しく作る操作が model に無い（range は初期状態で与える） | dom-range-clonerange |
| todo：StaticRange が model に無い | dom-staticrange-staticrange, staticrange-valid |
| todo：TreeWalker を作る API が無い（walker は scenario が与える） | dom-document-createtreewalker |
| todo：cancelBubble の setter が無い（ListenerAction に無い） | dom-event-cancelbubble/setter |
| todo：child text content を計算する関数が無い | concept-child-text-content |
| todo：clone the contents が未実装 | concept-range-clone, dom-range-clonecontents |
| todo：collapsed getter を返す操作が harness に無い（両端は観測に出るので導ける） | dom-range-collapsed |
| todo：common ancestor を求める定義が無い（使う extract・clone the contents が未実装） | get-the-common-ancestor |
| todo：commonAncestorContainer getter が無い | dom-range-commonancestorcontainer |
| todo：composedPath() が無い（shadow tree が無いので event path を逆順に invocation target を並べたものになるはずだが、実行関数が無い） | dom-event-composedpath |
| todo：contiguous Text nodes（CDATASection を含む前後両側）を集める関数が無い。使う側の wholeText も未実装 | contiguous-text-nodes |
| todo：createCDATASection が無い（`Dom/Mutation/Create.lean` の注） | dom-document-createcdatasection |
| todo：createProcessingInstruction が無い。target の Name production と ProcessingInstruction の target を model が持たない | dom-document-createprocessinginstruction |
| todo：currentNode を設定する操作が harness に無い（初期状態の current だけを与えられる） | dom-treewalker-currentnode/setter |
| todo：doctype の子を返す関数が無い | dom-document-doctype |
| todo：document の URL を持たない | dom-document-documenturi, dom-document-url |
| todo：document の URL（document base URL）を持たない | dom-node-baseuri |
| todo：document の content type を持たない（type は `isHTMLDocument` で持つ） | dom-document-contenttype |
| todo：document の encoding を持たない | dom-document-characterset, dom-document-charset, dom-document-inputencoding |
| todo：extract が未実装 | dom-range-extractcontents |
| todo：extract に依存するので未実装 | dom-range-surroundcontents |
| todo：extract（DocumentFragment への移し替えと部分 clone）が未実装 | concept-range-extract |
| todo：getAttributeNS() の関数が無い（getAttributeByKey はあるが null と value を返す method が無い） | dom-element-getattributens |
| todo：getter の実行関数も harness の操作も無い | dom-nondocumenttypechildnode-nextelementsibling, dom-nondocumenttypechildnode-previouselementsibling, dom-parentnode-childelementcount, dom-parentnode-firstelementchild, dom-parentnode-lastelementchild |
| todo：harness に操作が無い（`NodeId` の等号そのもので、実行関数を持たない） | dom-node-issamenode |
| todo：hasAttributeNS() の関数が無い | dom-element-hasattributens |
| todo：hasAttributes() の関数と harness の op が無い | dom-element-hasattributes |
| todo：insert adjacent が無い | dom-element-insertadjacentelement, dom-element-insertadjacenttext, insert-adjacent |
| todo：item() が無い | dom-domtokenlist-item |
| todo：length の getter が無い（token set は classTokenSet で読めるが API が無い） | dom-domtokenlist-length |
| todo：list of elements with namespace and local name が無い | dom-document-getelementsbytagnamens |
| todo：list of elements with namespace and local name（getElementsByTagNameNS）が無い | dom-element-getelementsbytagnamens |
| todo：list of elements with qualified name が無い | dom-document-getelementsbytagname |
| todo：list of elements with qualified name（getElementsByTagName）が無い | dom-element-getelementsbytagname |
| todo：node の connected を返す関数が無い（Attr だけ harness の attrQuery が false を返す） | dom-node-isconnected |
| todo：node 以外の EventTarget を作れない（listener の target は NodeId） | dom-eventtarget-eventtarget |
| todo：passive を持たない（判定には Window・Document の body も要る） | default-passive-value |
| todo：prepend に当たる関数（this の first child の前への pre-insert）が無い。harness にも操作が無い | dom-parentnode-prepend |
| todo：removeNamedItemNS() の関数が無い（removeAttributeNS は NotFoundError も `Attr` を返すことも無い） | dom-namednodemap-removenameditemns |
| todo：returnValue の setter が無い（ListenerAction に無い） | dom-event-returnvalue/setter |
| todo：set text content が無い（同上） | dom-node-textcontent/setter |
| todo：split a Text node が無い（docs/status.md の未着手。固定 scenario でも skip） | concept-text-split |
| todo：splitText() が無い（split a Text node が未実装） | dom-text-splittext |
| todo：supports() が無い（validation steps が未実装） | dom-domtokenlist-supports |
| todo：validation steps（supported tokens）が無い。classList の class は supported tokens を定めないので TypeError になるはずの所 | concept-domtokenlist-validation |
| todo：value の getter が無い（値は className の reflect getter と同じだが、DOMTokenList 側の API は無い） | dom-domtokenlist-value |
| todo：value の setter が無い（className の reflect setter と同じ効果だが、DOMTokenList 側の API は無い） | dom-domtokenlist-value/setter |
| todo：wholeText の getter が無い | dom-text-wholetext |
| todo：文字列から Text node を作って replace all する関数が無い | string-replace-all |
| todo：文字列から Text を作り、複数の node を DocumentFragment にまとめる変換。model の method は変換済みの一つの node を受け取る（呼び出し側で済ませる） | convert-nodes-into-a-node |
