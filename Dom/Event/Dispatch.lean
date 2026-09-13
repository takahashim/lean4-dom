import Dom.Basic.Order
import Dom.Basic.State

/-!
# event の配送（§2.9）

`dispatch` / `invoke` / `inner invoke` を写す。

## model の範囲

* **shadow tree は無い**ので、retargeting も slot も composed path も要らない。
  event path は target から根までの祖先列そのものである（`eventPath`）。
* `Window` が無いので、Document の "get the parent" は null である。
  path は木の中で閉じる。
* activation behavior（`click` の既定動作）は HTML 側の hook なので扱わない。
* `isTrusted` は常に false なので、legacy な type の付け替え（invoke の step 10）は起きない。
* callback は model の外だが、**何をするか**は scenario が `ListenerAction` として宣言する。
  そのぶん配送の順序・打ち切り・listener list の変化は model で決まる。
* `passive` と `signal` は扱わない（`preventDefault` は cancelable だけで決まる）。
-/

namespace Dom

/-! ## DOM Standard §2.2 の `eventPhase` -/

namespace EventPhase

def none : Nat := 0
def capturing : Nat := 1
def atTarget : Nat := 2
def bubbling : Nat := 3

end EventPhase

/-- 配送中の event。 -/
structure EventState where
  «type» : String
  bubbles : Bool := false
  cancelable : Bool := false
  eventPhase : Nat := EventPhase.none
  /-- 仕様の stop propagation flag。 -/
  stopPropagation : Bool := false
  /-- 仕様の stop immediate propagation flag。 -/
  stopImmediate : Bool := false
  /-- 仕様の canceled flag。 -/
  canceled : Bool := false
deriving DecidableEq, Repr, Inhabited

/--
DOM Standard §2.9 dispatch の step 5（event path の構築）。

shadow tree が無いので、target から根までの祖先列がそのまま path になる。
先頭の target だけが "shadow-adjusted target" を持つ（= AT_TARGET になる）。
-/
def eventPath (t : Tree) (target : NodeId) : List NodeId :=
  target :: ancestors t target

/-- DOM Standard §2.7 "remove an event listener"。 -/
def removeListenerAt (s : DOMState) (i : Nat) : DOMState :=
  match s.listeners[i]? with
  | none => s
  | some l => { s with listeners := s.listeners.set i { l with removed := true } }

/-- DOM Standard §2.7 "add an event listener" の step 5。同じ三つ組は足さない。 -/
def addListener (s : DOMState) (l : EventListener) : DOMState :=
  if s.listeners.any fun x =>
      !x.removed && x.target == l.target && x.type == l.type &&
        x.callback == l.callback && x.capture == l.capture then s
  else { s with listeners := s.listeners ++ [l] }

/-- callback の代わりの副作用を走らせる。 -/
def runAction (s : DOMState) (e : EventState) (l : EventListener) : DOMState × EventState :=
  match l.action with
  | .none => (s, e)
  | .stopPropagation => (s, { e with stopPropagation := true })
  -- `stopImmediatePropagation()` は両方のフラグを立てる。
  | .stopImmediatePropagation => (s, { e with stopPropagation := true, stopImmediate := true })
  | .preventDefault => (s, if e.cancelable then { e with canceled := true } else e)
  | .removeListener k => (removeListenerAt s k, e)
  | .addListener tgt ty src cap =>
    match s.listeners[src]? with
    | none => (s, e)
    | some source =>
      (addListener s { target := ⟨tgt⟩, «type» := ty, callback := source.callback,
                       capture := cap, once := false, action := source.action }, e)

/--
listener を一つ走らせる。

step 2.5 の「`once` は呼ぶ前に外す」と、callback の代わりの副作用をまとめたもの。
-/
def invokeOne (s : DOMState) (e : EventState) (l : EventListener) (i : Nat) :
    DOMState × EventState :=
  runAction (if l.once then removeListenerAt s i else s) e l

/--
DOM Standard §2.9 "inner invoke"。

`idxs` は invoke の step 8 の clone にあたる（呼び出す前に取った index の列）。
clone なので配送中に足した listener は入らないが、
**外された listener は飛ばす**（step 2 の `removed` の検査）ので、
`removed` は clone ではなく現在の状態から見る。
-/
def innerInvoke (capturing : Bool) (cur : NodeId) :
    DOMState → EventState → List Invocation → List Nat →
      DOMState × EventState × List Invocation
  | s, e, log, [] => (s, e, log)
  | s, e, log, i :: rest =>
    match s.listeners[i]? with
    | none => innerInvoke capturing cur s e log rest
    | some l =>
      -- step 2 の removed と step 2.1 の type
      if l.removed || l.type != e.type then innerInvoke capturing cur s e log rest
      -- step 2.3-2.4
      else if capturing != l.capture then innerInvoke capturing cur s e log rest
      else
        -- step 2.5-2.11
        let r := invokeOne s e l i
        let log₂ := log ++ [⟨l.callback, cur, e.eventPhase⟩]
        -- step 2.14
        if r.2.stopImmediate then (r.1, r.2, log₂)
        else innerInvoke capturing cur r.1 r.2 log₂ rest

/--
DOM Standard §2.9 "invoke"。

step 5 の stop propagation flag は **その item の listener を呼ぶ前に** 見る。
-/
def invokeItem (s : DOMState) (e : EventState) (log : List Invocation)
    (capturing : Bool) (item : NodeId) (isTarget : Bool) :
    DOMState × EventState × List Invocation :=
  if e.stopPropagation then (s, e, log)
  else
    let phase :=
      if isTarget then EventPhase.atTarget
      else if capturing then EventPhase.capturing
      else EventPhase.bubbling
    let idxs := s.listeners.zipIdx.filterMap fun (l, i) =>
      if l.target == item && !l.removed then some i else none
    innerInvoke capturing item s { e with eventPhase := phase } log idxs

/--
DOM Standard §2.9 dispatch の step 12-13（capture と bubble の二周）。

bubble の周では、target 以外は `bubbles` が false なら飛ばす（step 13.2.1）。
-/
def runPass (capturing : Bool) (target : NodeId) :
    DOMState → EventState → List Invocation → List NodeId →
      DOMState × EventState × List Invocation
  | s, e, log, [] => (s, e, log)
  | s, e, log, item :: rest =>
    let isTarget := item == target
    if !capturing && !isTarget && !e.bubbles then runPass capturing target s e log rest
    else
      let (s', e', log') := invokeItem s e log capturing item isTarget
      runPass capturing target s' e' log' rest

/--
DOM Standard §2.9 `dispatchEvent(event)`（の dispatch 部分）。

返すのは「更新後の状態」「戻り値（canceled flag の否定）」「呼ばれた listener の列」である。
フラグは配送の終わりに落とすので、次の配送には持ち越さない。
-/
def dispatchEvent (s : DOMState) (target : NodeId) («type» : String)
    (bubbles cancelable : Bool) : Except DOMException (DOMState × Bool × List Invocation) :=
  match s.tree.get? target with
  | none => .error .notFoundError
  | some _ =>
    let path := eventPath s.tree target
    let e : EventState := { «type» := «type», bubbles := bubbles, cancelable := cancelable }
    let (s₁, e₁, log₁) := runPass true target s e [] path.reverse
    let (s₂, e₂, log₂) := runPass false target s₁ e₁ log₁ path
    .ok (s₂, !e₂.canceled, log₂)

/-! ## `addEventListener` / `removeEventListener` -/

/-- DOM Standard §2.7 `addEventListener(type, callback, options)`。 -/
def addEventListener (s : DOMState) (target : NodeId) («type» : String) (source : Nat)
    (capture once : Bool) : Except DOMException DOMState :=
  match s.tree.get? target with
  | none => .error .notFoundError
  | some _ =>
    match s.listeners[source]? with
    | none => .error .notFoundError
    | some src =>
      .ok (addListener s { target := target, «type» := «type», callback := src.callback,
                           capture := capture, once := once, action := src.action })

/-- DOM Standard §2.7 `removeEventListener(type, callback, options)`。 -/
def removeEventListener (s : DOMState) (target : NodeId) («type» : String) (callback : Nat)
    (capture : Bool) : Except DOMException DOMState :=
  match s.tree.get? target with
  | none => .error .notFoundError
  | some _ =>
    match (s.listeners.zipIdx.find? fun (l, _) =>
        !l.removed && l.target == target && l.type == «type» && l.callback == callback &&
          l.capture == capture) with
    | none => .ok s
    | some (_, i) => .ok (removeListenerAt s i)

end Dom
