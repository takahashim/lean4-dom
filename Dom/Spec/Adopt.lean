import Dom.Spec.Remove

/-!
# `adopt` の関係意味論（§4.5）

`Dom/Spec/Remove.lean` と同じ方針で、仕様本文から独立に書き写した関係を置く。
step 2 が `remove` を呼ぶので、関係も `RemoveSpec` を composition する。
**これは実行関数の再利用ではない。** 仕様本文が "remove node" と書いているとおりの構成である。

shadow root と custom element registry（step 3.2-3.3）は model の対象外である。
-/

namespace Dom.Spec

open Dom

/--
§4.5 adopt の step 3。

`node` の inclusive descendant だけ node document が `doc` になり、他は変わらない。
-/
structure DocumentAssigned (t t' : Tree) (node doc : NodeId) : Prop where
  /-- 部分木の中は node document が変わる。 -/
  inside : ∀ (m : NodeId) (d : NodeData), t.get? m = some d → InclusiveDescendant t m node →
    t'.get? m = some { d with ownerDocument := doc }
  /-- 外は何も変わらない。 -/
  outside : ∀ m : NodeId, ¬ InclusiveDescendant t m node → t'.get? m = t.get? m

/-- 木以外の成分が変わらないこと。node document の付け替えは木しか触らない。 -/
structure LiveObjectsUnchangedExceptTree (s s' : DOMState) : Prop where
  ranges : s'.ranges = s.ranges
  iterators : s'.iterators = s.iterators
  registrations : s'.registrations = s.registrations
  observers : s'.observers = s.observers
  pendingObservers : s'.pendingObservers = s.pendingObservers
  microtaskQueued : s'.microtaskQueued = s.microtaskQueued

/--
**§4.5 "adopt" の関係意味論。**

step 2 は「parent があれば remove する」、step 3 は
「node document が変わるなら部分木ぜんぶの node document を付け替える」である。
-/
def AdoptSpec (s : DOMState) (node doc : NodeId) (s' : DOMState) : Prop :=
  ∃ oldDoc, ownerDocumentOf s.tree node = some oldDoc ∧
    ∃ s₁ : DOMState,
      -- step 2
      ((parentOf s.tree node = none ∧ s₁ = s) ∨
        ((∃ p, parentOf s.tree node = some p) ∧ RemoveSpec s node false s₁)) ∧
      -- step 3
      (if doc = oldDoc then s' = s₁
       else DocumentAssigned s₁.tree s'.tree node doc ∧ LiveObjectsUnchangedExceptTree s₁ s')

/-- range 以外が変わらないこと。live range の調整は range しか触らない。 -/
structure LiveObjectsUnchangedExceptRanges (s s' : DOMState) : Prop where
  iterators : s'.iterators = s.iterators
  registrations : s'.registrations = s.registrations
  observers : s'.observers = s.observers
  pendingObservers : s'.pendingObservers = s.pendingObservers
  microtaskQueued : s'.microtaskQueued = s.microtaskQueued

end Dom.Spec
