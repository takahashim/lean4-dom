import Dom.Basic.Order
import Dom.Util.List

/-!
# 木の well-formedness

`memo.md` の `WellFormed` を PLAN §3.3 に従って具体化する。

「node は高々1個の parent を持つ」は独立した条件にしない。
`parent` が `Option` なので一つの node の parent は構造上一意であり、
二つの parent の `children` に同時に現れないことは `child_parent` から導ける。
導出は `Dom/Properties/Tree.lean` の `unique_parent` に置く。
-/

namespace Dom

/--
木が常に満たすべき性質。

* `parent_child` — parent の children に現れる node は存在し、その parent は元の node である。
* `child_parent` — parent を持つ node は、その parent の children に現れる。
* `children_nodup` — children に同じ node が二度現れない。
* `acyclic` — 自分自身の ancestor である node は無い。
* `ownerDocument_is_document` — node document は存在し、その kind は `document` である。
-/
structure WellFormed (t : Tree) : Prop where
  parent_child :
    ∀ p pd, t.get? p = some pd →
      ∀ c ∈ pd.children, ∃ cd, t.get? c = some cd ∧ cd.parent = some p
  child_parent :
    ∀ c cd p, t.get? c = some cd → cd.parent = some p →
      ∃ pd, t.get? p = some pd ∧ c ∈ pd.children
  children_nodup :
    ∀ n d, t.get? n = some d → d.children.Nodup
  acyclic :
    ∀ n, ¬ Ancestor t n n
  ownerDocument_is_document :
    ∀ n d, t.get? n = some d →
      ∃ dd, t.get? d.ownerDocument = some dd ∧ dd.kind = .document

/-! ## 実行時に検査するための boolean 版 -/

/--
store の全 entry に対する述語の検査。

`keys` を走査しつつ値は `get?` で引き直すので、
`checkAll_iff` は store の表現に重複が無いことを仮定せずに成り立つ。
-/
def NodeStore.checkAll (s : NodeStore) (p : NodeId → NodeData → Bool) : Bool :=
  s.keys.all fun k =>
    match s.get? k with
    | none => true
    | some d => p k d

namespace Tree

/-- `WellFormed.parent_child` の boolean 版。 -/
def checkParentChild (t : Tree) : Bool :=
  t.nodes.checkAll fun p pd =>
    pd.children.all fun c =>
      match t.get? c with
      | none => false
      | some cd => decide (cd.parent = some p)

/-- `WellFormed.child_parent` の boolean 版。 -/
def checkChildParent (t : Tree) : Bool :=
  t.nodes.checkAll fun c cd =>
    match cd.parent with
    | none => true
    | some p =>
      match t.get? p with
      | none => false
      | some pd => decide (c ∈ pd.children)

/-- `WellFormed.children_nodup` の boolean 版。 -/
def checkChildrenNodup (t : Tree) : Bool :=
  t.nodes.checkAll fun _ d => Dom.ListUtil.nodupB d.children

/--
`WellFormed.acyclic` の boolean 版。

各 node から parent をたどり、store の要素数以内に parent を持たない node へ
到達することを確かめる。到達できなければ鳩の巣原理により cycle がある。
-/
def checkAcyclic (t : Tree) : Bool :=
  t.nodes.keys.all fun n => parentChainTerminates t t.size n

/-- `WellFormed.ownerDocument_is_document` の boolean 版。 -/
def checkOwnerDocument (t : Tree) : Bool :=
  t.nodes.checkAll fun _ d =>
    match t.get? d.ownerDocument with
    | none => false
    | some dd => decide (dd.kind = .document)

/--
`WellFormed` に対応する実行時の検査（PLAN §3.5）。

`checkWellFormed t = true ↔ WellFormed t` を `Dom/Properties/Tree.lean` で証明する。
これにより differential testing の各 step で invariant を実際に確認できる。
-/
def checkWellFormed (t : Tree) : Bool :=
  t.checkParentChild && t.checkChildParent && t.checkChildrenNodup &&
    t.checkAcyclic && t.checkOwnerDocument

end Tree

end Dom
