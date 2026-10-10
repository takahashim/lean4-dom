import Trace.Basic
import Dom

/-!
# §4.3 Mutation observers

callback は model の外なので、`notifyMutationObservers` は
「どの observer に何が配送されるか」を返す形になっている（`Dom/Observer/Deliver.lean`）。
-/

namespace Trace.Dom.Observer

open Trace

def entries : List Entry := [
  { alg := "queue-a-mutation-observer-compound-microtask"
    impl := [``Dom.queueMutationObserverMicrotask]
    approx := [("3", "microtask は積まず、flag を立てるだけである。notify mutation observers は harness の `notify` 操作として呼ぶ")] },
  { alg := "notify-mutation-observers"
    impl := [``Dom.notifyMutationObservers, ``Dom.notifyEach, ``Dom.notifyOne,
             ``Dom.MutationObserver.takeRecords, ``Dom.removeTransients]
    omitted := [("4-5", .shadow), ("7", .shadow)]
    approx := [("6.3", "node list の node に限らず、その observer の transient registered observer を全部外す。remove が transient を置いた node を node list にも足す（`addTransientObservers`）ので同じ結果になる"),
               ("6.4", "callback は呼ばない。records が空でない observer と records の組を返り値に並べる")] },
  { alg := "dom-mutationobserver-observe"
    impl := [``Dom.MutationObserver.observe, ``Dom.MutationObserverInit.resolve,
             ``Dom.MutationObserver.observeOptionsError]
    spec := [``Dom.Spec.ObserveResult, ``Dom.Spec.ObserveOptionsRejected]
    approx := [("1-2", "options の attributeOldValue / characterDataOldValue は「存在する」ではなく「true である」で見る（IDL の既定値が false なので、step 4・6 を通すと結論は同じ）"),
               ("3-6", "TypeError を `DOMException.typeError` で表す"),
               ("7", "target の registered observer list のうち transient でないものだけを見る。transient registered observer しか無ければ step 8 に進む"),
               ("7.1", "node list の node に限らず、source が target のこの observer の transient を全部外す。source は registered observer ではなく、その node で表す")] },
  { alg := "dom-mutationobserver-disconnect"
    impl := [``Dom.MutationObserver.disconnect]
    approx := [("1", "node list の node に限らず、この observer の registered observer を全部外す")] },
  { alg := "dom-mutationobserver-takerecords"
    impl := [``Dom.MutationObserver.takeRecords] },
  { alg := "queue-a-mutation-record"
    impl := [``Dom.queueMutationRecord, ``Dom.interestedObservers, ``Dom.Registration.interestedIn,
             ``Dom.addInterested, ``Dom.enqueueRecord, ``Dom.addPendingObserver,
             ``Dom.queueMutationObserverMicrotask]
    spec := [``Dom.Spec.TreeRecordQueued, ``Dom.Spec.CharacterDataRecordQueued,
             ``Dom.Spec.AttributeRecordQueued] },
  { alg := "queue-a-tree-mutation-record"
    impl := [``Dom.queueTreeMutationRecord, ``Dom.queueMutationRecord]
    spec := [``Dom.Spec.TreeRecordQueued]
    approx := [("1", "assert の代わりに、addedNodes と removedNodes が両方空なら何もしない")] }
]

def exclusions : List Exclusion := [
  { target := "dom-mutationobserver-mutationobserver"
    reason := .other "callback（script の関数）は model の外。observer は scenario の初期状態でだけ作り、constructor に当たる操作は無い" }
]

end Trace.Dom.Observer
