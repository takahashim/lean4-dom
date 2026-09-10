import Dom.Basic.Exception
import Dom.Basic.WellFormed

/-!
# primitive mutation：detach

PLAN §5.1 の三つの primitive のうち、node を親から外すもの。

仕様の remove（DOM Standard §4.2.3 "removing steps"）は、この primitive に加えて
Range と NodeIterator の調整を含む。ここでは木だけを変える部分を切り出す。
仕様どおりの `remove` は Phase 3 でこの primitive の上に組み立てる。
-/

namespace Dom

/--
`n` を parent `p` の children から外し、`n` の parent を `none` にした木。

`detach` の本体。`p` と `n` の `NodeData` を引数に取るのは、
定理側で `t.get?` の場合分けを繰り返さずに済ませるためである。
-/
def detachFrom (t : Tree) (n p : NodeId) (d pd : NodeData) : Tree :=
  { nodes :=
      (t.nodes.insert p { pd with children := Dom.ListUtil.removeAll pd.children n }).insert n
        { d with parent := none } }

/--
node を parent の children から外し、parent を `none` にする。parent が無ければ何もしない。

木に無い node を指定した場合は `notFoundError` を返す。
parent が木に無い場合も `notFoundError` を返すが、well-formed な木では起こらない。
-/
def detach (t : Tree) (n : NodeId) : Except DOMException Tree :=
  match t.get? n with
  | none => .error .notFoundError
  | some d =>
    match d.parent with
    | none => .ok t
    | some p =>
      match t.get? p with
      | none => .error .notFoundError
      | some pd => .ok (detachFrom t n p d pd)

/-! ## 場合分けのための equation lemma -/

theorem detach_of_get?_eq_none {t : Tree} {n : NodeId} (h : t.get? n = none) :
    detach t n = .error .notFoundError := by
  simp [detach, h]

theorem detach_of_parent_eq_none {t : Tree} {n : NodeId} {d : NodeData}
    (hd : t.get? n = some d) (hp : d.parent = none) : detach t n = .ok t := by
  simp [detach, hd, hp]

theorem detach_eq_ok {t : Tree} {n p : NodeId} {d pd : NodeData}
    (hd : t.get? n = some d) (hp : d.parent = some p) (hpd : t.get? p = some pd) :
    detach t n = .ok (detachFrom t n p d pd) := by
  simp [detach, hd, hp, hpd]

/--
`detach` が成功したときの結果は二通りしかない。
parent が無ければ木は変わらず、あれば `detachFrom` の形になる。
-/
theorem detach_ok_cases {t t' : Tree} {n : NodeId} (h : detach t n = .ok t') :
    (∃ d, t.get? n = some d ∧ d.parent = none ∧ t' = t) ∨
      (∃ d p pd, t.get? n = some d ∧ d.parent = some p ∧ t.get? p = some pd ∧
        t' = detachFrom t n p d pd) := by
  unfold detach at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · next hp => exact Or.inl ⟨d, hd, hp, (Except.ok.inj h).symm⟩
    · next p hp =>
      split at h
      · simp at h
      · next pd hpd => exact Or.inr ⟨d, p, pd, hd, hp, hpd, (Except.ok.inj h).symm⟩

end Dom
