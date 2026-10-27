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
    spec := [``Dom.Spec.NotifyResult, ``Dom.Spec.NotifiedEach, ``Dom.Spec.ObserverNotified,
             ``Dom.Spec.notifyMutationObservers_sound, ``Dom.Spec.notifyMutationObservers_complete]
    omitted := [("4-5", .shadow), ("7", .shadow)]
    approx := [("2", "creation index は `observers` の添字である。observer は scenario の初期状態でだけ作り、その並びが作った順である"),
               ("6.4", "callback は呼ばない。records が空でない observer と records の組を返り値に並べる")] },
  { alg := "add-transient-registered-observers"
    impl := [``Dom.addTransientObservers, ``Dom.newTransients, ``Dom.collectTransient,
             ``Dom.hasTransientFrom, ``Dom.Registration.sourceNode, ``Dom.Registration.transientOn,
             ``Dom.transientStep, ``Dom.pendTransient]
    spec := [``Dom.Spec.TransientAdded, ``Dom.Spec.transientsFor, ``Dom.Spec.transientAdded_of_add]
    approx := [("1.3-1.4", "source は registered observer ではなく、その node で表す。source が同じかどうかは observer と node で比べる（一つの observer が一つの node に持つ transient でない registered observer は高々一つ）"),
               ("1.5", "options は source のものではなく registered のものを写す。registered が transient でも、その options は source の options と等しい（`observe()` step 8.1 は options を差し替える前に、その source の transient を外す）"),
               ("1.6", "transient node set は node list と合わせて一つの list（`ObserverState.nodeList`）で持つ")] },
  { alg := "remove-transient-registered-observers"
    impl := [``Dom.removeTransients]
    spec := [``Dom.Spec.ObserverNotified, ``Dom.Spec.notifyMutationObservers_sound]
    approx := [("1", "transient node set の node に限らず、この observer の transient registered observer を全部外す。admissible な状態では registration の node はその observer の node list にある（`ObserverRegistrationsValid` の `ListedIn`）ので同じ結果になる（`filter_listed`、`notifyMutationObservers_sound`）"),
               ("2", "transient node set は node list と合わせて持つので、空にしない。残った node には この observer の transient が無いので、観測に出ない")] },
  { alg := "dom-mutationobserver-observe"
    -- step 3-6 の TypeError は `DOMException` ではなく `IdlException.typeError`（`observeMethod`）。
    impl := [``Dom.MutationObserver.observeMethod, ``Dom.MutationObserver.observe,
             ``Dom.MutationObserverInit.resolve, ``Dom.MutationObserver.observeOptionsError,
             ``Dom.Idl.toMutationObserverInit]
    spec := [``Dom.Spec.ObserveResult, ``Dom.Spec.ObserveOptionsRejected]
    approx := [("8.1", "transient node set の node に限らず、source が target のこの observer の transient を全部外す。source は registered observer ではなく、その node で表す")] },
  { alg := "dom-mutationobserver-disconnect"
    impl := [``Dom.MutationObserver.disconnect]
    spec := [``Dom.Spec.DisconnectResult, ``Dom.Spec.disconnect_sound, ``Dom.Spec.disconnect_complete]
    approx := [("1-2", "node list と transient node set の node に限らず、この observer の registered observer を全部外す。admissible な状態では同じ結果になる（`disconnect_sound`）"),
               ("3", "model の node list は transient node set と合わせたもので、両方をここで空にする")] },
  { alg := "dom-mutationobserver-takerecords"
    impl := [``Dom.MutationObserver.takeRecords]
    spec := [``Dom.Spec.TakeRecordsResult, ``Dom.Spec.takeRecords_sound, ``Dom.Spec.takeRecords_complete] },
  { alg := "queue-a-mutation-record"
    impl := [``Dom.queueMutationRecord, ``Dom.interestedObservers, ``Dom.Registration.interestedIn,
             ``Dom.addInterested, ``Dom.enqueueRecord, ``Dom.addPendingObserver,
             ``Dom.queueMutationObserverMicrotask]
    spec := [``Dom.Spec.TreeRecordQueued, ``Dom.Spec.CharacterDataRecordQueued,
             ``Dom.Spec.AttributeRecordQueued] },
  { alg := "queue-a-tree-mutation-record"
    impl := [``Dom.queueTreeMutationRecord, ``Dom.queueMutationRecord]
    -- step 1 の assert の代わりに、両方空なら何もしない。replace all の step 7（どちらかが空でなければ積む）は
    -- この guard が担う。それ以外の呼び出し元（insert・remove・replace・move）は、関係の soundness の証明が
    -- `treeRecordQueued_of_queue` の仮定（どちらかが空でない）を示しているので、guard は効かない。
    spec := [``Dom.Spec.TreeRecordQueued, ``Dom.Spec.treeRecordQueued_of_queue] }
]

def exclusions : List Exclusion := [
  { target := "dom-mutationobserver-mutationobserver"
    reason := .other "callback（script の関数）は model の外。observer は scenario の初期状態でだけ作り、constructor に当たる操作は無い。creation index（step 2-3）は `observers` の添字である" }
]

end Trace.Dom.Observer
