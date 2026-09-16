import Dom.Query.NodeQuery
import Dom.Properties.Tree
import Dom.Properties.TreeOrder

/-!
# `Dom/Query/NodeQuery.lean` の契約

§4.4 の「値を返すだけの method」の契約。差分テストは個々の呼び出しの一致しか
見ないので、API どうしの整合や全称的な性質はここで押さえる。

`nodeEqualsFuel` は fuel が尽きると **例外ではなく `false`** を返す。`isEqualNode`
が `false` を返すのは正常な場合でもあるので、fuel 切れは差分テストでも
「等しくないと判定した」と区別がつかない。だから足りることは証明で押さえる。
-/

namespace Dom

variable {t : Tree}

/-- 要素ごとに一致するなら `all` の値も一致する。 -/
theorem all_congr {α : Type _} : ∀ (l : List α) {p q : α → Bool},
    (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _, _, _ => rfl
  | x :: rest, p, q, h => by
    simp only [List.all_cons]
    rw [h x (List.mem_cons_self ..), all_congr rest fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- zip の要素の第一成分は元の list の要素である。 -/
theorem fst_mem_of_mem_zip {α β : Type _} :
    ∀ {l₁ : List α} {l₂ : List β} {p : α × β}, p ∈ l₁.zip l₂ → p.1 ∈ l₁
  | [], _, _, h => by simp [List.zip] at h
  | _ :: _, [], _, h => by simp [List.zip] at h
  | x :: r₁, y :: r₂, p, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zip h)

/-! ## `nodeEqualsFuel` の interface -/

theorem nodeEqualsFuel_succ_pos {a b : NodeId} {da db : NodeData} (f : Nat)
    (ha : t.get? a = some da) (hb : t.get? b = some db) :
    nodeEqualsFuel t (f + 1) a b =
      (da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2) := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha, hb]

theorem nodeEqualsFuel_succ_none_left {a b : NodeId} (f : Nat) (ha : t.get? a = none) :
    nodeEqualsFuel t (f + 1) a b = false := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha]

theorem nodeEqualsFuel_succ_none_right {a b : NodeId} {da : NodeData} (f : Nat)
    (ha : t.get? a = some da) (hb : t.get? b = none) :
    nodeEqualsFuel t (f + 1) a b = false := by
  show (match t.get? a, t.get? b with
    | some da, some db =>
      da.kind == db.kind && nodeOwnPropertiesEqual da db &&
        da.children.length == db.children.length &&
        (da.children.zip db.children).all fun p => nodeEqualsFuel t f p.1 p.2
    | _, _ => false) = _
  rw [ha, hb]

/-! ## fuel は足りる -/

/--
**`nodeEqualsFuel` は fuel が「store の要素数 − 深さ」以上なら答えが変わらない。**

`mem_preorderFuel_of_inclusive_descendant` と同じ形の induction である。
一段降りると深さが一つ増えるので、必要な fuel は一つ減る。
-/
theorem nodeEqualsFuel_eq_of_le (hwf : WellFormed t) :
    ∀ (k : Nat) (a b : NodeId) (d : NodeData), t.get? a = some d →
      t.size - depth t a ≤ k → ∀ g, k ≤ g →
      nodeEqualsFuel t k a b = nodeEqualsFuel t g a b := by
  intro k
  induction k with
  | zero =>
    intro a b d ha hk _ _
    exfalso
    have := depth_lt_size hwf ha
    omega
  | succ k ih =>
    intro a b d ha hk g hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hkg : k ≤ g := by omega
    cases hb : t.get? b with
    | none => rw [nodeEqualsFuel_succ_none_right k ha hb, nodeEqualsFuel_succ_none_right g ha hb]
    | some db =>
      have hall : (d.children.zip db.children).all (fun p => nodeEqualsFuel t k p.1 p.2)
          = (d.children.zip db.children).all (fun p => nodeEqualsFuel t g p.1 p.2) := by
        refine all_congr _ fun p hp => ?_
        have hmem : p.1 ∈ childrenOf t a := by
          rw [childrenOf_eq ha]; exact fst_mem_of_mem_zip hp
        have hpar : parentOf t p.1 = some a := parentOf_of_mem_childrenOf hwf hmem
        obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hpar
        have hdep : depth t p.1 = depth t a + 1 := depth_parent hwf hpar
        exact ih p.1 p.2 cd hcd (by omega) g hkg
      rw [nodeEqualsFuel_succ_pos k ha hb, nodeEqualsFuel_succ_pos g ha hb, hall]

/--
**fuel `t.size` で足りる。**

`nodeEquals` はそれ以上 fuel を増やしても答えが変わらない。
`isEqualNode` が fuel 切れで `false` を返すことは無い。
-/
theorem nodeEqualsFuel_eq_nodeEquals (hwf : WellFormed t) (a b : NodeId) {g : Nat}
    (hg : t.size ≤ g) : nodeEqualsFuel t g a b = nodeEquals t a b := by
  cases ha : t.get? a with
  | none =>
    cases hs : t.size with
    | zero =>
      cases g with
      | zero =>
        show _ = nodeEqualsFuel t t.size a b
        rw [hs]
      | succ g =>
        rw [nodeEqualsFuel_succ_none_left g ha]
        show _ = nodeEqualsFuel t t.size a b
        rw [hs]
        rfl
    | succ m =>
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [nodeEqualsFuel_succ_none_left g ha]
      show _ = nodeEqualsFuel t t.size a b
      rw [hs, nodeEqualsFuel_succ_none_left m ha]
  | some d =>
    exact (nodeEqualsFuel_eq_of_le hwf t.size a b d ha (by omega) g hg).symm

/-! ## `contains` / `getRootNode` -/

@[simp] theorem nodeContains_self (t : Tree) (n : NodeId) : nodeContains t n n = true :=
  isInclusiveAncestorOf_self t n

/-- `contains(other)` は「other が inclusive descendant であること」ちょうどである。 -/
theorem nodeContains_iff (hwf : WellFormed t) (n o : NodeId) :
    nodeContains t n o = true ↔ InclusiveAncestor t n o :=
  isInclusiveAncestorOf_iff hwf n o

@[simp] theorem getRootNode_eq (t : Tree) (n : NodeId) : getRootNode t n = root t n := rfl

/-- **`getRootNode()` が返す node は、元の node を `contains` する。** -/
theorem nodeContains_getRootNode (hwf : WellFormed t) (n : NodeId) :
    nodeContains t (getRootNode t n) n = true :=
  (nodeContains_iff hwf _ n).mpr (root_inclusive_ancestor t n)

/-! ## `compareDocumentPosition` -/

@[simp] theorem compareDocumentPosition_self (t : Tree) (n : NodeId) :
    compareDocumentPosition t n n = 0 := by
  unfold compareDocumentPosition
  rw [if_pos (by simp)]

/-- 同じ木にないときは、node id の順で PRECEDING か FOLLOWING を決める。 -/
theorem compareDocumentPosition_disconnected {t : Tree} {a b : NodeId} (hne : a ≠ b)
    (hr : root t b ≠ root t a) :
    compareDocumentPosition t a b = if b.id < a.id then 35 else 37 := by
  unfold compareDocumentPosition
  rw [if_neg (by simp [hne]), if_pos (by simp [hr])]
  split <;> rfl

/--
**同じ木にない二つの node については、逆に呼べば逆の答えになる。**

仕様 step 6 の "consistent" がこれである。どちらを PRECEDING にするかは実装に任されるが、
一方から見て「先行する」なら、他方から見ては「後続する」でなければならない。
-/
theorem compareDocumentPosition_disconnected_consistent {t : Tree} {a b : NodeId}
    (hne : a ≠ b) (hr : root t a ≠ root t b) :
    (compareDocumentPosition t a b = 37 ∧ compareDocumentPosition t b a = 35) ∨
    (compareDocumentPosition t a b = 35 ∧ compareDocumentPosition t b a = 37) := by
  have hid : a.id ≠ b.id := fun h => hne (by cases a; cases b; simp_all)
  rw [compareDocumentPosition_disconnected hne (Ne.symm hr),
    compareDocumentPosition_disconnected (Ne.symm hne) hr]
  rcases Nat.lt_or_ge a.id b.id with h | h
  · exact Or.inl ⟨by rw [if_neg (by omega)], by rw [if_pos (by omega)]⟩
  · have h' : b.id < a.id := by omega
    exact Or.inr ⟨by rw [if_pos (by omega)], by rw [if_neg (by omega)]⟩

/--
**`contains` と `compareDocumentPosition` は整合する。**

`node.contains(other)` が真で両者が別の node なら、`compareDocumentPosition` は
CONTAINED_BY と FOLLOWING を立てる。二つの API が別々に実装されると
ここがずれるので、差分テストではなく定理で押さえる。
-/
theorem compareDocumentPosition_of_contains (hwf : WellFormed t) {node other : NodeId}
    (hne : node ≠ other) (h : nodeContains t node other = true) :
    compareDocumentPosition t node other =
      DocumentPosition.containedBy + DocumentPosition.following := by
  rcases (nodeContains_iff hwf node other).mp h with he | ha
  · exact absurd he hne
  · have hroot : root t other = root t node := root_eq_of_ancestor hwf ha
    have hanc : isAncestorOf t node other = true := (isAncestorOf_iff hwf node other).mpr ha
    have hother : isAncestorOf t other node = false := by
      cases hb : isAncestorOf t other node with
      | false => rfl
      | true =>
        exact absurd (((isAncestorOf_iff hwf other node).mp hb).trans_ancestor ha)
          (hwf.acyclic other)
    unfold compareDocumentPosition
    rw [if_neg (by simp [hne]), if_neg (by simp [hroot]), if_neg (by simp [hother]),
      if_pos (by simp [hanc])]

/-! ## `isEqualNode` は反射的である -/

theorem attrEquals_refl (x : Attr) : attrEquals x x = true := by
  unfold attrEquals
  simp

theorem nodeOwnPropertiesEqual_refl (d : NodeData) : nodeOwnPropertiesEqual d d = true := by
  unfold nodeOwnPropertiesEqual
  cases hk : d.kind
  case element =>
    simp only [beq_self_eq_true, Bool.and_self, Bool.true_and]
    refine List.all_eq_true.mpr fun x hx => ?_
    exact List.any_eq_true.mpr ⟨x, hx, attrEquals_refl x⟩
  all_goals simp

/-- zip の要素は、同じ list どうしなら両成分が一致する。 -/
theorem fst_eq_snd_of_mem_zip_self {α : Type _} [DecidableEq α] :
    ∀ {l : List α} {p : α × α}, p ∈ l.zip l → p.1 = p.2
  | [], _, h => by simp [List.zip] at h
  | x :: r, p, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact fst_eq_snd_of_mem_zip_self h

theorem nodeEqualsFuel_refl (hwf : WellFormed t) :
    ∀ (k : Nat) (n : NodeId) (d : NodeData), t.get? n = some d →
      t.size - depth t n ≤ k → nodeEqualsFuel t k n n = true := by
  intro k
  induction k with
  | zero =>
    intro n d hn hk
    exfalso
    have := depth_lt_size hwf hn
    omega
  | succ k ih =>
    intro n d hn hk
    rw [nodeEqualsFuel_succ_pos k hn hn]
    simp only [beq_self_eq_true, Bool.true_and, nodeOwnPropertiesEqual_refl, Bool.and_self]
    refine List.all_eq_true.mpr fun p hp => ?_
    have hmem : p.1 ∈ childrenOf t n := by
      rw [childrenOf_eq hn]; exact fst_mem_of_mem_zip hp
    have hpar : parentOf t p.1 = some n := parentOf_of_mem_childrenOf hwf hmem
    obtain ⟨cd, hcd, -⟩ := parentOf_eq_some hpar
    have hdep : depth t p.1 = depth t n + 1 := depth_parent hwf hpar
    have h12 : p.1 = p.2 := by
      have := fst_eq_snd_of_mem_zip_self (l := (childrenOf t n)) (p := p)
      rw [childrenOf_eq hn] at this
      exact this hp
    rw [← h12]
    exact ih p.1 cd hcd (by omega)

/-- **`isEqualNode` は木にある node について反射的である。** -/
theorem nodeEquals_refl (hwf : WellFormed t) {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) : nodeEquals t n n = true :=
  nodeEqualsFuel_refl hwf t.size n d hn (by omega)

/-! ## `nodeValue` / `textContent` -/

theorem getNodeValue_of_characterData {t : Tree} {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.isCharacterData = true) :
    getNodeValue t n = some d.data := by
  unfold getNodeValue
  rw [hn]
  simp only [hk, if_pos]

theorem getNodeValue_of_not_characterData {t : Tree} {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.isCharacterData = false) :
    getNodeValue t n = none := by
  unfold getNodeValue
  rw [hn]
  simp [hk]

/--
**CharacterData では `textContent` と `nodeValue` が一致する。**

仕様は別々の algorithm として書いてあるが、CharacterData の枝では同じ値を返す。
-/
theorem getTextContent_eq_getNodeValue_of_characterData {t : Tree} {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind.isCharacterData = true) :
    getTextContent t n = getNodeValue t n := by
  rw [getNodeValue_of_characterData hn hk]
  show (match t.get? n with
    | none => none
    | some d =>
      match d.kind with
      | .documentFragment | .element => some (descendantTextContent t n)
      | .text | .cdataSection | .comment | .processingInstruction => some d.data
      | .document | .documentType => none) = some d.data
  simp only [hn]
  cases hkk : d.kind <;> rw [hkk] at hk <;> simp_all [NodeKind.isCharacterData]

/-- Document と DocumentType の `textContent` は null である。 -/
theorem getTextContent_eq_none {t : Tree} {n : NodeId} {d : NodeData} (hn : t.get? n = some d)
    (hk : d.kind = NodeKind.document ∨ d.kind = NodeKind.documentType) :
    getTextContent t n = none := by
  show (match t.get? n with
    | none => none
    | some d =>
      match d.kind with
      | .documentFragment | .element => some (descendantTextContent t n)
      | .text | .cdataSection | .comment | .processingInstruction => some d.data
      | .document | .documentType => none) = none
  simp only [hn]
  rcases hk with h | h <;> rw [h]

/-! ## 名前空間の探索 -/

/-- element なら element chain は自分自身から始まる。 -/
theorem elementChain_of_element {t : Tree} {e : NodeId}
    (h : kindOf t e = some NodeKind.element) : ∃ rest, elementChain t e = e :: rest := by
  unfold elementChain
  rw [List.takeWhile_cons_of_pos (by simp [h])]
  exact ⟨_, rfl⟩

/-- `takeWhile` に残るのは述語を満たす要素だけである。 -/
private theorem mem_takeWhile_pred {α : Type _} {p : α → Bool} :
    ∀ {l : List α} {x : α}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: r, x, h => by
    by_cases hp : p y = true
    · rw [List.takeWhile_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hp
      · exact mem_takeWhile_pred h
    · rw [List.takeWhile_cons_of_neg (by simpa using hp)] at h
      simp at h

/-- element chain に並ぶのは element だけである。 -/
theorem kindOf_of_mem_elementChain {t : Tree} {e x : NodeId} (h : x ∈ elementChain t e) :
    kindOf t x = some NodeKind.element := by
  unfold elementChain at h
  simpa using mem_takeWhile_pred h

/-- `parentElement` が返すのは parent であって element である。 -/
theorem parentElement_eq_some_iff {t : Tree} {n e : NodeId} :
    parentElement t n = some e ↔
      parentOf t n = some e ∧ kindOf t e = some NodeKind.element := by
  unfold parentElement
  cases hp : parentOf t n with
  | none => simp
  | some p =>
    show (if (kindOf t p == some NodeKind.element) = true then some p else none) = some e ↔ _
    by_cases hk : kindOf t p = some NodeKind.element
    · rw [if_pos (by simp [hk])]
      constructor
      · intro h
        exact ⟨h, by rw [← Option.some.inj h]; exact hk⟩
      · intro h
        exact h.1
    · rw [if_neg (by simp [hk])]
      simp only [reduceCtorEq, false_iff, not_and]
      intro h
      rw [← Option.some.inj h]
      exact hk

/-- `documentElement` が返すのは children の中の element である。 -/
theorem documentElement_spec {t : Tree} {n e : NodeId} (h : documentElement t n = some e) :
    e ∈ childrenOf t n ∧ kindOf t e = some NodeKind.element := by
  unfold documentElement at h
  obtain ⟨hmem, hk⟩ := List.find?_eq_some_iff_append.mp h |>.imp id id
  refine ⟨?_, by simpa using hmem⟩
  exact List.mem_of_find?_eq_some h

/-! ### `xml` / `xmlns` prefix -/

theorem locateNamespaceIn_xml (t : Tree) (e : NodeId) (rest : List NodeId) :
    locateNamespaceIn t (some "xml") (e :: rest) = some xmlNamespace := by
  show (if (some "xml" : Option String) == some "xml" then some xmlNamespace else _) = _
  rw [if_pos (by simp)]

theorem locateNamespaceIn_xmlns (t : Tree) (e : NodeId) (rest : List NodeId) :
    locateNamespaceIn t (some "xmlns") (e :: rest) = some xmlnsNamespace := by
  show (if (some "xmlns" : Option String) == some "xml" then some xmlNamespace
        else if (some "xmlns" : Option String) == some "xmlns" then some xmlnsNamespace
        else _) = _
  rw [if_neg (by simp), if_pos (by simp)]

/-- **element では `lookupNamespaceURI("xml")` は仕様の固定値を返す（step 1）。** -/
theorem lookupNamespaceURI_xml {t : Tree} {n : NodeId} {d : NodeData}
    (hn : t.get? n = some d) (hk : d.kind = NodeKind.element) :
    lookupNamespaceURI t n (some "xml") = some xmlNamespace := by
  obtain ⟨rest, hchain⟩ := elementChain_of_element (e := n) (t := t)
    (by rw [kindOf_of_get? hn, hk])
  show locateNamespace t n (if (some "xml" : Option String) == some "" then none
    else some "xml") = _
  rw [if_neg (by simp)]
  show (match t.get? n with
    | none => none
    | some d =>
      match d.kind with
      | .element => locateNamespaceIn t (some "xml") (elementChain t n)
      | .document =>
        match documentElement t n with
        | none => none
        | some e => locateNamespaceIn t (some "xml") (elementChain t e)
      | .documentType | .documentFragment => none
      | _ =>
        match parentElement t n with
        | none => none
        | some e => locateNamespaceIn t (some "xml") (elementChain t e)) = _
  simp only [hn, hk, hchain]
  exact locateNamespaceIn_xml t n rest

/-- **空文字列の namespace では `lookupPrefix` は null を返す。** -/
theorem lookupPrefix_empty (t : Tree) (n : NodeId) :
    lookupPrefix t n (some "") = none := rfl

@[simp] theorem lookupPrefix_none (t : Tree) (n : NodeId) :
    lookupPrefix t n none = none := rfl

/--
**`isDefaultNamespace(ns)` は `lookupNamespaceURI(null)` と同じことを言っている。**

仕様は前者を後者の言葉で定義しているので、二つが別々に実装されるとずれる。
-/
theorem isDefaultNamespace_iff (t : Tree) (n : NodeId) (ns : Option String) :
    isDefaultNamespace t n ns = true ↔
      lookupNamespaceURI t n none = (if ns == some "" then none else ns) := by
  unfold isDefaultNamespace lookupNamespaceURI
  simp

end Dom
