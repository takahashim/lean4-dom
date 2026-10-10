import Trace.Basic
import Dom

/-!
# §2 Events・§3 Aborting ongoing activities

model の event は `Dom/Event/Dispatch.lean` にある。Event object も EventTarget object も独立には持たず、
harness の `dispatchEvent(target, type, bubbles, cancelable)` が配送用の `EventState` をその場で作り、
配送が終わったら捨てる。listener の callback は model の外で、scenario が `ListenerAction` として
宣言した副作用（`stopPropagation` など）を callback の代わりに走らせる。
AbortController / AbortSignal は model に無い。
-/

namespace Trace.Dom.Event

open Trace

def entries : List Entry := [
  /- ## §2.2 Event の method（`ListenerAction` として宣言されたときだけ起きる） -/
  { alg := "dom-event-stoppropagation"
    impl := [``Dom.runAction]
    spec := [``Dom.Spec.CallbackRan]
    approx := [("*", "callback の中の呼び出しではなく、listener の `ListenerAction.stopPropagation` として callback の後に一度だけ走る")] },
  { alg := "dom-event-stopimmediatepropagation"
    impl := [``Dom.runAction]
    spec := [``Dom.Spec.CallbackRan]
    approx := [("*", "listener の `ListenerAction.stopImmediatePropagation` として走る")] },
  { alg := "set-the-canceled-flag"
    impl := [``Dom.setCanceledFlag, ``Dom.runAction]
    spec := [``Dom.Spec.CallbackRan] },
  { alg := "dom-event-preventdefault"
    impl := [``Dom.runAction]
    spec := [``Dom.Spec.CallbackRan]
    approx := [("*", "listener の `ListenerAction.preventDefault` として走る")] },

  /- ## §2.7 EventTarget -/
  { alg := "add-an-event-listener"
    impl := [``Dom.addListener, ``Dom.addEventListener, ``Dom.defaultPassiveValue]
    spec := [``Dom.Spec.ListenerAdded, ``Dom.Spec.AddEventListenerResult, ``Dom.Spec.DefaultPassive]
    omitted := [("1", .host), ("2", .todo "AbortSignal と listener の signal を持たない"),
                ("3", .other "callback は scenario の番号で、null にならない"),
                ("6", .todo "AbortSignal と listener の signal を持たない")]
    approx := [("5", "listener list を EventTarget ごとではなく一本の list に `target` 付きで持つ。外した listener は `removed` を立てて残すので、それを除いて重複を探す")] },
  { alg := "dom-eventtarget-addeventlistener"
    impl := [``Dom.addEventListener, ``Dom.addListener, ``Dom.flattenMoreOptions,
             ``Dom.Idl.toAddEventListenerOptions]
    spec := [``Dom.Spec.AddEventListenerResult]
    approx := [("1", "signal を持たない。AbortSignal の値は表せないので、undefined でない signal は WebIDL の変換で TypeError になり、method steps に入らない"),
               ("2", "callback は scenario の `source` 番の listener のもの（番号と `ListenerAction`）を使い回す。target か source が無ければ（model の都合で）NotFoundError")] },
  { alg := "remove-an-event-listener"
    impl := [``Dom.removeListenerAt]
    spec := [``Dom.Spec.ListenerRemovedAt]
    omitted := [("1", .host)]
    approx := [("2", "list から取り除かず `removed` を立てるだけにする。以後の検索と配送は `removed` の listener を飛ばす")] },
  { alg := "dom-eventtarget-removeeventlistener"
    impl := [``Dom.removeEventListener, ``Dom.removeListenerAt, ``Dom.flattenOptions,
             ``Dom.Idl.toEventListenerOptions]
    spec := [``Dom.Spec.RemoveEventListenerResult] },
  { alg := "concept-flatten-options"
    impl := [``Dom.flattenOptions] },
  { alg := "event-flatten-more"
    impl := [``Dom.flattenMoreOptions]
    omitted := [("4.3", .todo "AbortSignal と listener の signal を持たない（undefined でない signal は WebIDL の変換で TypeError になる）")]
    approx := [("3", "signal を持たないので passive だけを null（`none`）で始める"),
               ("5", "signal を返さない")] },
  { alg := "default-passive-value"
    impl := [``Dom.defaultPassiveValue, ``Dom.bodyElementOf]
    spec := [``Dom.Spec.DefaultPassive, ``Dom.Spec.BodyElement]
    approx := [("1", "Window を持たないので、eventTarget が Window である場合は無い")] },
  { alg := "dom-eventtarget-dispatchevent"
    impl := [``Dom.dispatchEvent]
    spec := [``Dom.Spec.DispatchResult]
    omitted := [("1", .other "Event object を持たず、配送ごとに新しい EventState を作るので、dispatch flag が立った event や初期化されていない event は渡せない"),
                ("2", .other "isTrusted を持たない（常に false として扱う）")]
    approx := [("3", "event は引数の type・bubbles・cancelable からその場で作る（`new Event(type, {bubbles, cancelable})` と dispatchEvent を合わせた形）")] },

  /- ## §2.9 Dispatching events -/
  { alg := "concept-event-dispatch"
    impl := [``Dom.dispatchEvent, ``Dom.eventPath, ``Dom.runPass, ``Dom.invokeItem]
    spec := [``Dom.Spec.DispatchResult, ``Dom.Spec.EventPathSpec, ``Dom.Spec.PassRan]
    omitted := [("1", .other "dispatch flag を持たない。callback が model の外で、配送中に同じ event を配送し直すことが起きない"),
                ("3", .hook), ("4", .shadow), ("5", .shadow),
                ("6.1-6.2", .shadow), ("6.4-6.5", .hook), ("6.6-6.7", .shadow),
                ("6.9.1-6.9.5", .shadow), ("6.9.6.1", .hook),
                ("6.9.7", .shadow), ("6.9.8", .shadow), ("6.9.10", .shadow),
                ("6.10-6.11", .shadow), ("6.12", .hook), ("11", .shadow), ("12", .hook)]
    approx := [("2", "legacy target override flag（Window の場合）が無いので targetOverride は target そのもの"),
               ("6", "relatedTarget を持たない（null）ので、条件は常に真として step 6 の中身を走らせる"),
               ("6.3", "event path の item は node だけを持ち、shadow-adjusted target を持つのは先頭の target だけ（`runPass` の `isTarget`）"),
               ("6.8", "get the parent は parent をそのまま返す。Document の get the parent は（Window が無いので）null"),
               ("6.9.6", "shadow tree が無いので、parent は常に target と同じ tree にあり、この分岐を常に取る（shadow-adjusted target は null）"),
               ("6.9.9", "get the parent は parent をそのまま返す。Document の get the parent は（Window が無いので）null"),
               ("6.13-6.14", "legacyOutputDidListenersThrowFlag を渡さない（callback が例外を投げない）"),
               ("7-10", "EventState を配送の終わりに捨てるので、フラグと eventPhase の後始末は結果に現れない")] },
  { alg := "concept-event-path-append"
    impl := [``Dom.eventPath]
    spec := [``Dom.Spec.EventPathSpec]
    omitted := [("1-4", .shadow)]
    approx := [("5", "item は invocation target の node だけ。shadow-adjusted target は `runPass` が先頭（target）かどうかで決め、relatedTarget と touch target list は持たない")] },
  { alg := "concept-event-listener-invoke"
    impl := [``Dom.invokeItem, ``Dom.innerInvoke]
    spec := [``Dom.Spec.Invoked, ``Dom.Spec.ListenersOf]
    omitted := [("1-3", .other "Event の target 属性を持たない（shadow tree が無いので配送中は常に target で、callback は model の外なので観測されない）"),
                ("4-5", .shadow), ("9", .shadow),
                ("11", .other "isTrusted が常に false なので起きない")]
    approx := [("7", "currentTarget は event に持たず、`innerInvoke` の引数 `cur` として呼び出しの記録（`Invocation`）に残す"),
               ("8", "clone は listener の index の列。外された listener は clone の時点で除き、その後に外されたものは inner invoke が現在の状態の `removed` を見て飛ばす")] },
  { alg := "concept-event-listener-inner-invoke"
    impl := [``Dom.innerInvoke, ``Dom.invokeOne, ``Dom.runAction, ``Dom.removeListenerAt]
    spec := [``Dom.Spec.InnerInvoked, ``Dom.Spec.CallbackRan]
    omitted := [("1", .other "found を計算しない。使い道の invoke step 11 が isTrusted=false で起きない"),
                ("2.2", .other "found を計算しない"),
                ("2.6-2.8", .host),
                ("2.10", .host), ("2.11.1-2.11.2", .host),
                ("2.13", .host),
                ("3", .other "found を返さない")]
    approx := [("2.11", "callback を呼ぶ代わりに、listener の `ListenerAction`（stopPropagation・preventDefault・listener の追加と削除など）を `runAction` で走らせる。callback は例外を投げない")] }
]

def exclusions : List Exclusion := [
  /- §2.2 Event の attribute と method -/
  { target := "dom-event-target", reason := .todo "Event object を持たないので target の getter が無い" },
  { target := "dom-event-srcelement", reason := .legacy },
  { target := "dom-event-composedpath", reason := .todo "composedPath() が無い（shadow tree が無いので event path を逆順に invocation target を並べたものになるはずだが、実行関数が無い）" },
  { target := "dom-event-cancelbubble", reason := .todo "Event object を持たないので cancelBubble の getter が無い" },
  { target := "dom-event-cancelbubble/setter", reason := .todo "cancelBubble の setter が無い（ListenerAction に無い）" },
  { target := "dom-event-returnvalue", reason := .todo "Event object を持たないので returnValue の getter が無い" },
  { target := "dom-event-returnvalue/setter", reason := .todo "returnValue の setter が無い（ListenerAction に無い）" },
  { target := "dom-event-defaultprevented", reason := .todo "Event object を持たないので defaultPrevented の getter が無い（dispatchEvent の戻り値としてだけ canceled flag が見える）" },
  { target := "dom-event-composed", reason := .todo "Event object を持たず、composed flag も無い" },
  { target := "concept-event-initialize", reason := .todo "Event object を持たない。dispatchEvent が type・bubbles・cancelable から EventState をその場で作る" },
  { target := "dom-event-initevent", reason := .legacy },
  /- §2.3 -/
  { target := "interface-window-extensions", reason := .host },
  /- §2.4 -/
  { target := "dom-customevent-initcustomevent", reason := .legacy },
  /- §2.5 -/
  { target := "concept-event-constructor", reason := .todo "Event object を持たない。dispatchEvent が type・bubbles・cancelable から EventState をその場で作り、constructor・dictionary・timeStamp は無い" },
  { target := "concept-event-create", reason := .host },
  { target := "inner-event-creation-steps", reason := .host },
  /- §2.7 -/
  { target := "dom-eventtarget-eventtarget", reason := .todo "node 以外の EventTarget を作れない（listener の target は NodeId）" },
  { target := "remove-all-event-listeners", reason := .other "HTML（document.open()）が使う道具。model の操作からは呼ばれず、実行関数も無い" },
  /- §2.8 -/
  { target := "observing-event-listeners", reason := .host },
  /- §2.10 -/
  { target := "concept-event-fire", reason := .other "他の仕様（と §3 の abort steps）が使う道具。model の操作からは呼ばれない" },
  /- §3 -/
  { target := "aborting-ongoing-activities", reason := .todo "AbortController と AbortSignal（abort reason・abort algorithms・dependent signal）が無い" }
]

end Trace.Dom.Event
