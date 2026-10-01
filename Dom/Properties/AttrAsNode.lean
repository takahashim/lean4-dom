import Dom.Attribute.AsNode
import Dom.Properties.NodeQuery

/-!
# `Attr` を `Node` として扱う method の性質

* `compareDocumentPositionRef` は node どうしでは `compareDocumentPosition` と同じで
  （`compareDocumentPositionRef_nodes`）、自分自身とは 0、element の無い `Attr` が絡めば
  同じ木にない扱いで、向きを入れ替えると PRECEDING と FOLLOWING が入れ替わる
  （`compareDocumentPositionRef_disconnected_consistent`、step 5 の「一貫していること」）。
* `Attr` は子にも親にもなれない（`appendChildRef_attr_fails`）。
* `contains` は `Attr` と node をまたがない（`nodeContainsRef_node_attr` ほか）。
* clone / import した `Attr` は element を持たず、namespace・local name・value が元と同じで、
  node document が渡した document になる（`cloneAttrIn_spec`）。
-/

namespace Dom

/-- **node どうしなら、`Attr` を受ける版は元の `compareDocumentPosition` と同じ。** -/
theorem compareDocumentPositionRef_nodes (s : DOMState) (n m : NodeId) :
    compareDocumentPositionRef s (.node n) (.node m) = compareDocumentPosition s.tree n m := by
  unfold compareDocumentPositionRef compareDocumentPosition
  by_cases h : n = m
  · subst h; simp
  · have h' : (n == m) = false := by simpa using h
    simp [h, h', NodeRef.elementOf, NodeRef.before, NodeRef.orderKey]
    by_cases hl : m.id < n.id <;> simp [hl]

@[simp] theorem compareDocumentPositionRef_self (s : DOMState) (x : NodeRef) :
    compareDocumentPositionRef s x x = 0 := by
  unfold compareDocumentPositionRef
  simp

theorem NodeRef.before_total {x y : NodeRef} (h : x ≠ y) : x.before y = true ∨ y.before x = true := by
  cases x with
  | node a =>
    cases y with
    | node b =>
      have : a.id ≠ b.id := fun e => h (by cases a; cases b; simp_all)
      rcases Nat.lt_or_gt_of_ne this with hl | hl
      · left; simp [NodeRef.before, NodeRef.orderKey, hl]
      · right; simp [NodeRef.before, NodeRef.orderKey, hl]
    | attr b => left; simp [NodeRef.before, NodeRef.orderKey]
  | attr a =>
    cases y with
    | node b => right; simp [NodeRef.before, NodeRef.orderKey]
    | attr b =>
      have : a.id ≠ b.id := fun e => h (by cases a; cases b; simp_all)
      rcases Nat.lt_or_gt_of_ne this with hl | hl
      · left; simp [NodeRef.before, NodeRef.orderKey, hl]
      · right; simp [NodeRef.before, NodeRef.orderKey, hl]

theorem NodeRef.before_asymm {x y : NodeRef} (h : x.before y = true) : y.before x = false := by
  cases x with
  | node a =>
    cases y with
    | node b =>
      simp only [NodeRef.before, NodeRef.orderKey, Nat.lt_irrefl, decide_false, Bool.false_or,
        beq_self_eq_true, Bool.true_and] at h
      have hab : a.id < b.id := of_decide_eq_true h
      simp [NodeRef.before, NodeRef.orderKey, Nat.not_lt.mpr (Nat.le_of_lt hab)]
    | attr b => simp [NodeRef.before, NodeRef.orderKey]
  | attr a =>
    cases y with
    | node b => simp [NodeRef.before, NodeRef.orderKey] at h
    | attr b =>
      simp only [NodeRef.before, NodeRef.orderKey, Nat.lt_irrefl, decide_false, Bool.false_or,
        beq_self_eq_true, Bool.true_and] at h
      have hab : a.id < b.id := of_decide_eq_true h
      simp [NodeRef.before, NodeRef.orderKey, Nat.not_lt.mpr (Nat.le_of_lt hab)]

/--
**element の無い `Attr` が絡めば同じ木にない扱いで、向きを入れ替えると PRECEDING と FOLLOWING が
入れ替わる。** 仕様 step 5 の "with the constraint that this is to be consistent"。
-/
theorem compareDocumentPositionRef_disconnected_consistent (s : DOMState) {x y : NodeRef}
    (hne : x ≠ y) (hnone : x.elementOf s = none ∨ y.elementOf s = none) :
    (compareDocumentPositionRef s x y = 37 ∧ compareDocumentPositionRef s y x = 35) ∨
    (compareDocumentPositionRef s x y = 35 ∧ compareDocumentPositionRef s y x = 37) := by
  have key : ∀ a b : NodeRef, a ≠ b → (a.elementOf s = none ∨ b.elementOf s = none) →
      compareDocumentPositionRef s a b = if b.before a then 35 else 37 := by
    intro a b hab hn
    unfold compareDocumentPositionRef
    rw [if_neg hab]
    rcases hn with hn | hn
    · simp only [hn]
      split <;> simp_all <;> first | rfl | (split <;> rfl)
    · simp only [hn]
      split <;> simp_all <;> first | rfl | (split <;> rfl)
  rw [key x y hne hnone, key y x (Ne.symm hne) hnone.symm]
  rcases NodeRef.before_total hne with h | h
  · rw [NodeRef.before_asymm h, h]; simp
  · rw [NodeRef.before_asymm h, h]; simp

/-- **`Attr` は子にも親にもなれない。** pre-insertion validity の step 1 か 4 で必ず失敗する。 -/
theorem appendChildRef_attr_fails (s : DOMState) {parent node : NodeRef}
    (h : (∃ a, parent = .attr a) ∨ (∃ a, node = .attr a)) (s' : DOMState) :
    appendChildRef s parent node ≠ .ok s' := by
  unfold appendChildRef
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · split <;> (try split) <;> simp_all
  · cases parent with
    | attr b => simp only; split <;> simp
    | node p =>
      simp only
      split
      · simp
      · split
        · simp
        · split <;> simp

@[simp] theorem nodeContainsRef_node_attr (s : DOMState) (n : NodeId) (a : AttrId) :
    nodeContainsRef s (.node n) (.attr a) = false := rfl

@[simp] theorem nodeContainsRef_attr_node (s : DOMState) (a : AttrId) (n : NodeId) :
    nodeContainsRef s (.attr a) (.node n) = false := rfl

/-- `Attr` の inclusive descendant は自分だけである。 -/
theorem nodeContainsRef_attr_attr (s : DOMState) (a b : AttrId) :
    nodeContainsRef s (.attr a) (.attr b) = true ↔ a = b := by
  simp [nodeContainsRef]

/--
**clone した `Attr`。** 新しい id で detach された list に入り、namespace・prefix・local name・
value は元と同じ、node document は `doc` である（"clone a single node" の `Attr` の枝）。
-/
theorem cloneAttrIn_spec (s : DOMState) (a : Attr) (doc : NodeId) :
    let r := cloneAttrIn s a doc
    r.1 = freshStateAttrId s ∧
      ∃ c ∈ r.2.detachedAttrs, c.id = r.1 ∧ c.namespace = a.namespace ∧ c.prefix = a.prefix ∧
        c.localName = a.localName ∧ c.value = a.value ∧ c.ownerDocument = doc ∧
        attrEquals c a = true := by
  simp [cloneAttrIn, attrEquals]

end Dom
