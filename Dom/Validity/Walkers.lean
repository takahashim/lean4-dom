import Dom.Validity.State
import Dom.Traversal.TreeWalker

/-!
# `TreeWalker` と `AdmissibleDOMState`

`walkers` は `DOMState` の成分だが、**`AdmissibleDOMState` には入れていない**。

* §6.2 には "removing steps" が無いので、木を変える algorithm は walker を触らない。
  保つべきものが無い。
* 逆に「`current` は `root` の inclusive descendant」という強い条件は
  remove で壊れる。それは仕様どおりの挙動なので、状態の不変条件にはできない。

walker 自身の走査については `Dom/Properties/Walker.lean` の
`walkersValid_walkerStep`（root と current が木の中に留まる）で示す。
ここでは、走査が他の七成分を触らないことだけを言う。
-/

namespace Dom

/-- walker を差し替えても、木・range・iterator・observer・attribute は変わらない。 -/
theorem admissible_withWalker {s : DOMState} {i : Nat} {w : WalkerState}
    (h : AdmissibleDOMState s) : AdmissibleDOMState (withWalker s i w) :=
  ⟨h.structural, h.nodeDocuments, h.documentTrees, h.rangeEndpoints, h.iterators,
    h.observerRegistrations, h.attributes⟩

/-- **`TreeWalker` の走査は admissibility を保つ。** -/
theorem admissible_walkerStep {s s' : DOMState} {i : Nat} {m : WalkerMethod} {r : Option NodeId}
    (h : AdmissibleDOMState s) (hs : walkerStep s i m = .ok (r, s')) : AdmissibleDOMState s' := by
  unfold walkerStep walkerRun at hs
  split at hs
  · simp at hs
  · split at hs
    · have : s' = s := ((Prod.mk.injEq ..).mp (Except.ok.inj hs)).2.symm
      rw [this]; exact h
    · have : s' = withWalker s i _ := ((Prod.mk.injEq ..).mp (Except.ok.inj hs)).2.symm
      rw [this]; exact admissible_withWalker h

end Dom
