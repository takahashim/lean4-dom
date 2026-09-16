import Dom.Basic.Store

/-!
# Node tree

DOM Standard §4.2 Node tree に対応する。

`Ancestor` は仕様の記述に対応する specification 側の定義であり、計算可能ではない。
root を求める、祖先を列挙する、tree order で走査する、といった実行可能な関数は
`Dom/Basic/Order.lean` に fuel 付きの再帰として置く（PLAN §3.2）。
-/

namespace Dom

/-- 本 model が扱う DOM の木構造。node の集合だけを持つ。 -/
structure Tree where
  nodes : NodeStore
deriving Repr, Inhabited

namespace Tree

/-- 空の木。 -/
def empty : Tree := ⟨NodeStore.empty⟩

/-- `n` の `NodeData`。木に無ければ `none`。 -/
@[inline] def get? (t : Tree) (n : NodeId) : Option NodeData := t.nodes.get? n

/-- `n` が木に含まれるか。 -/
@[inline] def contains (t : Tree) (n : NodeId) : Bool := t.nodes.contains n

/-- 木に含まれる node の個数。fuel の上界として使う。 -/
@[inline] def size (t : Tree) : Nat := t.nodes.size

end Tree

/-- DOM Standard §4.2 の parent。木に無い node の parent は `none` とする。 -/
def parentOf (t : Tree) (n : NodeId) : Option NodeId :=
  (t.get? n).bind (·.parent)

/-- DOM Standard §4.2 の children。木に無い node の children は空とする。 -/
def childrenOf (t : Tree) (n : NodeId) : List NodeId :=
  match t.get? n with
  | none => []
  | some d => d.children

/-- `n` の node type。 -/
def kindOf (t : Tree) (n : NodeId) : Option NodeKind :=
  (t.get? n).map (·.kind)

/-- `n` の node document。 -/
def ownerDocumentOf (t : Tree) (n : NodeId) : Option NodeId :=
  (t.get? n).map (·.ownerDocument)

/-- DOM Standard §4.4 の node length。 -/
def lengthOf (t : Tree) (n : NodeId) : Nat :=
  match t.get? n with
  | none => 0
  | some d => d.length

/--
DOM Standard §4.2 の ancestor。`Ancestor t a n` は「`a` は `n` の ancestor である」と読む。

`step` は parent そのもの、`trans` は parent の ancestor をたどる場合である。
-/
inductive Ancestor (t : Tree) : NodeId → NodeId → Prop where
  | step {a n : NodeId} : parentOf t n = some a → Ancestor t a n
  | trans {a b n : NodeId} : parentOf t n = some b → Ancestor t a b → Ancestor t a n

/-- DOM Standard §4.2 の inclusive ancestor。 -/
@[reducible] def InclusiveAncestor (t : Tree) (a n : NodeId) : Prop :=
  a = n ∨ Ancestor t a n

/-- DOM Standard §4.2 の descendant。 -/
@[reducible] def Descendant (t : Tree) (d n : NodeId) : Prop :=
  Ancestor t n d

/-- DOM Standard §4.2 の inclusive descendant。 -/
@[reducible] def InclusiveDescendant (t : Tree) (d n : NodeId) : Prop :=
  InclusiveAncestor t n d

/-- DOM Standard §4.2 の sibling。同じ parent を持つ相異なる二つの node。 -/
def Sibling (t : Tree) (a b : NodeId) : Prop :=
  a ≠ b ∧ ∃ p, parentOf t a = some p ∧ parentOf t b = some p

/--
`n` の、parent の children における位置。

parent を持たない場合と、parent の children に現れない場合は `none`。
後者は well-formed な木では起きない。
-/
def index (t : Tree) (n : NodeId) : Option Nat :=
  (parentOf t n).bind fun p => (childrenOf t p).findIdx? (fun c => decide (c = n))

/-! ## 基本的な言い換え -/

/--
`parentOf` の値。以降の証明はこの三つ（`_eq` / `_of_get?` / `_eq_none_of_get?_eq_none`）
だけを使い、本体を開かない。
-/
theorem parentOf_eq (t : Tree) (n : NodeId) : parentOf t n = (t.get? n).bind (·.parent) := rfl

theorem parentOf_of_get? {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    parentOf t n = d.parent := by
  rw [parentOf_eq, h]
  rfl

theorem parentOf_eq_none_of_get?_eq_none {t : Tree} {n : NodeId} (h : t.get? n = none) :
    parentOf t n = none := by
  rw [parentOf_eq, h]
  rfl

/-- `get?` が一致する node では `parentOf` も一致する。 -/
theorem parentOf_congr {t t' : Tree} {m : NodeId} (h : t'.get? m = t.get? m) :
    parentOf t' m = parentOf t m := by
  rw [parentOf_eq, parentOf_eq, h]

theorem childrenOf_eq_nil_of_get?_eq_none {t : Tree} {n : NodeId} (h : t.get? n = none) :
    childrenOf t n = [] := by
  simp [childrenOf, h]

theorem parentOf_eq_some {t : Tree} {n p : NodeId} (h : parentOf t n = some p) :
    ∃ d, t.get? n = some d ∧ d.parent = some p := by
  cases hd : t.get? n with
  | none => rw [parentOf_eq_none_of_get?_eq_none hd] at h; simp at h
  | some d => exact ⟨d, rfl, by rw [← parentOf_of_get? hd]; exact h⟩

theorem childrenOf_eq {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    childrenOf t n = d.children := by
  simp [childrenOf, h]

/-- ancestor 関係の推移性。木の well-formedness を要しない。 -/
theorem Ancestor.trans_ancestor {t : Tree} {a b c : NodeId}
    (hab : Ancestor t a b) (hbc : Ancestor t b c) : Ancestor t a c := by
  induction hbc with
  | step h => exact Ancestor.trans h hab
  | trans h _ ih => exact Ancestor.trans h ih

/-- ancestor である以上、下側の node は parent を持つ。 -/
theorem Ancestor.parent_isSome {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    ∃ p, parentOf t n = some p := by
  cases h with
  | step h => exact ⟨_, h⟩
  | trans h _ => exact ⟨_, h⟩

/-- ancestor 関係を parent 一段で分解する。 -/
theorem Ancestor.cases_parent {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    ∃ p, parentOf t n = some p ∧ (a = p ∨ Ancestor t a p) := by
  cases h with
  | step h => exact ⟨_, h, Or.inl rfl⟩
  | trans h ha => exact ⟨_, h, Or.inr ha⟩

/-- parent を一段登って ancestor 関係を作る。 -/
theorem Ancestor.of_parent_inclusive {t : Tree} {a p n : NodeId}
    (hp : parentOf t n = some p) (h : InclusiveAncestor t a p) : Ancestor t a n := by
  rcases h with rfl | h
  · exact Ancestor.step hp
  · exact Ancestor.trans hp h

theorem InclusiveAncestor.refl (t : Tree) (n : NodeId) : InclusiveAncestor t n n := Or.inl rfl

theorem InclusiveAncestor.of_ancestor {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    InclusiveAncestor t a n := Or.inr h

end Dom
