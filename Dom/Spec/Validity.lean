import Dom.Spec.Insert
import Dom.Properties.Mutation
import Dom.Mutation.Algorithms

/-!
# `ensure pre-insert validity` の関係意味論（§4.2.3）

`Dom/Spec/Result.lean` の `PreInsertResult` は、失敗側を実行側の
`ensurePreInsertionValidity` に委ねていた。それでは仕様の step 1-11 を読み違えて
実装しても関係がその実装に合わせて成り立つので、例外の種類については何も保証しない。

ここでは step 1-11 の条件を**実行側の関数を呼ばずに**書く。
条件は `Dom/Basic/` の語彙（`childrenOf` / `parentOf` / `kindOf` / `InclusiveAncestor`）
と list の所属だけで書き、`elementChildren` や `doctypeFollows` のような
実行側の helper は使わない。

制御の流れ（どの step が先か、どこで return するか）は仕様の `<ol>` の形をそのまま
写す。`Step` / `Return` / `Branch` / `Done` の四つの combinator で組む。

## 「following」「preceding」の読み

step 9 の「a doctype is following child」と step 11 の「an element is preceding child」の
`following` / `preceding` は、仕様では**木の順序**である。ここでは
**`parent` の children の中での前後**として書いた。

**両者が一致することは証明してある**（`Dom/Spec/ValidityOrder.lean` の
`doctypeFollowing_iff_precedes` / `elementPreceding_iff_precedes`）。
step 9 / step 11 の文脈、つまり `parent` が Document で `child` がその子であるときに、
`StructurallyValid` の下で成り立つ。
-/

namespace Dom.Spec

open Dom

/-! ## 条件の語彙 -/

/-- node が木にあり、kind が `k` であること。 -/
def KindIs (t : Tree) (n : NodeId) (k : NodeKind) : Prop :=
  ∃ d, t.get? n = some d ∧ d.kind = k

/-- node が木にあること。 -/
def InTree (t : Tree) (n : NodeId) : Prop := ∃ d, t.get? n = some d

/-- node が Text（`CDATASection` を含む）であること。 -/
def IsText (t : Tree) (n : NodeId) : Prop :=
  ∃ d, t.get? n = some d ∧ d.kind.isText = true

/-- node が CharacterData であること。 -/
def IsCharacterData (t : Tree) (n : NodeId) : Prop :=
  ∃ d, t.get? n = some d ∧ d.kind.isCharacterData = true

/-- step 1。parent は Document / DocumentFragment / Element である。 -/
def ParentIsContainer (t : Tree) (parent : NodeId) : Prop :=
  KindIs t parent .document ∨ KindIs t parent .documentFragment ∨ KindIs t parent .element

/-- step 3。reference child があれば `parent` の子である。 -/
def ChildIsChildOf (t : Tree) (child : Option NodeId) (parent : NodeId) : Prop :=
  ∀ c, child = some c → parentOf t c = some parent

/-- step 4。入れられるのは DocumentFragment / DocumentType / Element / CharacterData。 -/
def NodeIsInsertable (t : Tree) (node : NodeId) : Prop :=
  KindIs t node .documentFragment ∨ KindIs t node .documentType ∨
    KindIs t node .element ∨ IsCharacterData t node

/-- `p` が kind `k` の子を持つこと。 -/
def HasChildOfKind (t : Tree) (p : NodeId) (k : NodeKind) : Prop :=
  ∃ c ∈ childrenOf t p, KindIs t c k

/-- `p` が `excl` に入っていない kind `k` の子を持つこと。 -/
def HasChildOfKindOutside (t : Tree) (p : NodeId) (k : NodeKind) (excl : List NodeId) : Prop :=
  ∃ c ∈ childrenOf t p, KindIs t c k ∧ c ∉ excl

/-- `p` が Text の子を持つこと。 -/
def HasTextChild (t : Tree) (p : NodeId) : Prop := ∃ c ∈ childrenOf t p, IsText t c

/-- step 8.1。`p` が element の子を二つ以上持つこと。 -/
def HasTwoElementChildren (t : Tree) (p : NodeId) : Prop :=
  ∃ a ∈ childrenOf t p, ∃ b ∈ childrenOf t p, a ≠ b ∧ KindIs t a .element ∧ KindIs t b .element

/--
step 9 の「a doctype is following child」。

仕様の `following` は木の順序だが、ここでは `parent` の children の中での後ろとして
書いた。doctype の親は Document だけ（§4.1 の制約）で、木に Document は一つしか
無いので、`parent` が Document のとき両者は一致する。
step 9 へ来ているのは `parent` が Document のときだけである（step 5 が分岐する）。
木順との一致は `doctypeFollowing_iff_precedes`（`Dom/Spec/ValidityOrder.lean`）にある。

`A ++ c :: B` の形に `c ∉ A` を付けてあるのは「`c` の位置で切る」と言うためである。
children に重複が無いので条件としては同じで、`splitAt?` の意味とも合う。
-/
def DoctypeFollowing (t : Tree) (parent c : NodeId) : Prop :=
  ∃ A B, childrenOf t parent = A ++ c :: B ∧ c ∉ A ∧ ∃ d ∈ B, KindIs t d .documentType

/--
step 11 の「an element is preceding child」。読みは `DoctypeFollowing` と同じである。

element は木のどこにでもあるが、Document の子で子孫を持つものは element しかないので、
木順との一致はやはり言える（`elementPreceding_iff_precedes`）。
-/
def ElementPreceding (t : Tree) (parent c : NodeId) : Prop :=
  ∃ A B, childrenOf t parent = A ++ c :: B ∧ c ∉ A ∧ ∃ d ∈ A, KindIs t d .element

/-- step 9.1。DocumentFragment と Element を Document に入れるときの三条件。 -/
def ElementInsertionBlocked (t : Tree) (parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  HasChildOfKindOutside t parent .element excl ∨
    (∃ c, child = some c ∧ DoctypeFollowing t parent c) ∨
    (∃ c, child = some c ∧ KindIs t c .documentType ∧ c ∉ excl)

/-- step 11。doctype を Document に入れるときの三条件。 -/
def DoctypeInsertionBlocked (t : Tree) (parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  HasChildOfKindOutside t parent .documentType excl ∨
    (∃ c, child = some c ∧ ElementPreceding t parent c) ∨
    (child = none ∧ HasChildOfKindOutside t parent .element excl)

/-! ## 制御の流れ -/

/-- 検査が終わって成功すること。 -/
def Done (r : Except DOMException Unit) : Prop := r = .ok ()

/-- 「`p` なら例外 `e`、でなければ次へ」。仕様の "If ... then throw ..." である。 -/
def Step (p : Prop) (e : DOMException) (next : Except DOMException Unit → Prop)
    (r : Except DOMException Unit) : Prop :=
  (p ∧ r = .error e) ∨ (¬ p ∧ next r)

/-- 「`p` なら return、でなければ次へ」。仕様の "If ... then return" である。 -/
def Return (p : Prop) (next : Except DOMException Unit → Prop)
    (r : Except DOMException Unit) : Prop :=
  (p ∧ Done r) ∨ (¬ p ∧ next r)

/-- 「`p` なら `a`、でなければ `b`」。 -/
def Branch (p : Prop) (a b : Except DOMException Unit → Prop)
    (r : Except DOMException Unit) : Prop :=
  (p ∧ a r) ∨ (¬ p ∧ b r)

/-- 「その関係は結果を一つに決める」。 -/
def Deterministic (f : Except DOMException Unit → Prop) : Prop :=
  ∀ r₁ r₂, f r₁ → f r₂ → r₁ = r₂

theorem Done_deterministic : Deterministic Done := by
  intro r₁ r₂ h₁ h₂; rw [h₁, h₂]

theorem Step_deterministic {p : Prop} {e : DOMException}
    {next : Except DOMException Unit → Prop} (h : Deterministic next) :
    Deterministic (Step p e next) := by
  rintro r₁ r₂ (⟨hp₁, rfl⟩ | ⟨hp₁, hn₁⟩) (⟨hp₂, rfl⟩ | ⟨hp₂, hn₂⟩)
  · rfl
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · exact h _ _ hn₁ hn₂

theorem Return_deterministic {p : Prop} {next : Except DOMException Unit → Prop}
    (h : Deterministic next) : Deterministic (Return p next) := by
  rintro r₁ r₂ (⟨hp₁, hd₁⟩ | ⟨hp₁, hn₁⟩) (⟨hp₂, hd₂⟩ | ⟨hp₂, hn₂⟩)
  · rw [hd₁, hd₂]
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · exact h _ _ hn₁ hn₂

theorem Branch_deterministic {p : Prop} {a b : Except DOMException Unit → Prop}
    (ha : Deterministic a) (hb : Deterministic b) : Deterministic (Branch p a b) := by
  rintro r₁ r₂ (⟨hp₁, hn₁⟩ | ⟨hp₁, hn₁⟩) (⟨hp₂, hn₂⟩ | ⟨hp₂, hn₂⟩)
  · exact ha _ _ hn₁ hn₂
  · exact absurd hp₁ hp₂
  · exact absurd hp₂ hp₁
  · exact hb _ _ hn₁ hn₂

/-! ## 全体 -/

/--
**§4.2.3 "ensure pre-insert validity" の関係意味論。**

仕様の `<ol>` をそのまま写した形である。先頭の二つ（parent と node が木にあること）は
model の追加で、仕様の algorithm は node object を受け取るので存在を前提にしている。
-/
def PreInsertValidity (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Except DOMException Unit → Prop :=
  -- model の追加：parent と node が木にあること
  Step (¬ InTree t parent) .notFoundError <|
  Step (¬ InTree t node) .notFoundError <|
  -- step 1
  Step (¬ ParentIsContainer t parent) .hierarchyRequestError <|
  -- step 2
  Step (InclusiveAncestor t node parent) .hierarchyRequestError <|
  -- step 3
  Step (¬ ChildIsChildOf t child parent) .notFoundError <|
  -- step 4
  Step (¬ NodeIsInsertable t node) .hierarchyRequestError <|
  -- step 5
  Branch (¬ KindIs t parent .document)
    (Step (KindIs t node .documentType) .hierarchyRequestError Done)
    -- step 6
    (Step (IsText t node) .hierarchyRequestError <|
     -- step 7
     Return (IsCharacterData t node) <|
     -- step 8
     Branch (KindIs t node .documentFragment)
       (Step (HasTwoElementChildren t node ∨ HasTextChild t node) .hierarchyRequestError <|
        Return (¬ HasChildOfKind t node .element) <|
        Step (ElementInsertionBlocked t parent child excl) .hierarchyRequestError Done)
       -- step 9
       (Branch (KindIs t node .element)
          (Step (ElementInsertionBlocked t parent child excl) .hierarchyRequestError Done)
          -- step 10-11（node は doctype）
          (Step (DoctypeInsertionBlocked t parent child excl) .hierarchyRequestError Done)))

/-! ## 実行側との橋

条件が実行側の判定と一致することを言う。**関係の定義は実行側を呼ばないが、
橋の定理は両方に触れてよい**（`ruby test/spec_dependence.rb` が見るのは `def` の本体だけ）。
-/

theorem kindIs_iff {t : Tree} {n : NodeId} {k : NodeKind} :
    KindIs t n k ↔ kindOf t n = some k := by
  unfold KindIs
  rw [kindOf_eq]
  cases h : t.get? n with
  | none => simp
  | some d => simp

theorem inTree_iff {t : Tree} {n : NodeId} : InTree t n ↔ (t.get? n).isSome := by
  unfold InTree
  cases h : t.get? n <;> simp

theorem isText_iff {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    IsText t n ↔ d.kind.isText = true := by
  unfold IsText
  rw [h]
  simp

theorem isCharacterData_iff {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    IsCharacterData t n ↔ d.kind.isCharacterData = true := by
  unfold IsCharacterData
  rw [h]
  simp

theorem parentIsContainer_iff {t : Tree} {parent : NodeId} {pd : NodeData}
    (h : t.get? parent = some pd) :
    ParentIsContainer t parent ↔
      (pd.kind = .document ∨ pd.kind = .documentFragment ∨ pd.kind = .element) := by
  unfold ParentIsContainer KindIs
  rw [h]
  simp

theorem nodeIsInsertable_iff {t : Tree} {node : NodeId} {nd : NodeData}
    (h : t.get? node = some nd) :
    NodeIsInsertable t node ↔
      (nd.kind = .documentFragment ∨ nd.kind = .documentType ∨ nd.kind = .element ∨
        nd.kind.isCharacterData = true) := by
  unfold NodeIsInsertable KindIs IsCharacterData
  rw [h]
  simp

theorem childIsChildOf_iff {t : Tree} {child : Option NodeId} {parent : NodeId} :
    ChildIsChildOf t child parent ↔ childHasParent t child parent = true := by
  unfold ChildIsChildOf
  cases child with
  | none => simp
  | some c => rw [childHasParent_some_iff]; simp

theorem hasChildOfKind_iff {t : Tree} {p : NodeId} {k : NodeKind} :
    HasChildOfKind t p k ↔ ((childrenOf t p).filter (fun c => kindOf t c == some k)) ≠ [] := by
  unfold HasChildOfKind
  constructor
  · rintro ⟨c, hc, hk⟩ he
    have hm : c ∈ (childrenOf t p).filter (fun c => kindOf t c == some k) :=
      List.mem_filter.mpr ⟨hc, by simp [kindIs_iff.mp hk]⟩
    rw [he] at hm
    simp at hm
  · intro h
    cases hq : (childrenOf t p).filter (fun c => kindOf t c == some k) with
    | nil => exact absurd hq h
    | cons x xs =>
      have hx : x ∈ (childrenOf t p).filter (fun c => kindOf t c == some k) := by rw [hq]; simp
      obtain ⟨hm, hk⟩ := List.mem_filter.mp hx
      exact ⟨x, hm, kindIs_iff.mpr (by simpa using hk)⟩

theorem hasChildOfKindOutside_iff {t : Tree} {p : NodeId} {k : NodeKind} {excl : List NodeId} :
    HasChildOfKindOutside t p k excl ↔
      ((childrenOf t p).filter (fun c => kindOf t c == some k)).any
        (fun c => !excl.contains c) = true := by
  unfold HasChildOfKindOutside
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hk, hex⟩
    exact ⟨c, List.mem_filter.mpr ⟨hc, by simp [kindIs_iff.mp hk]⟩, by simpa using hex⟩
  · rintro ⟨c, hm, hex⟩
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hm
    exact ⟨c, hc, kindIs_iff.mpr (by simpa using hk), by simpa using hex⟩

theorem hasTextChild_iff {t : Tree} {p : NodeId} : HasTextChild t p ↔ textChildren t p ≠ [] := by
  unfold HasTextChild textChildren IsText
  constructor
  · rintro ⟨c, hc, d, hd, hk⟩ he
    have hm : c ∈ (childrenOf t p).filter (fun c => match kindOf t c with
        | some k => k.isText | none => false) :=
      List.mem_filter.mpr ⟨hc, by rw [kindOf_of_get? hd]; exact hk⟩
    exact List.ne_nil_of_mem hm he
  · intro h
    cases hq : (childrenOf t p).filter (fun c => match kindOf t c with
        | some k => k.isText | none => false) with
    | nil => exact absurd hq h
    | cons x xs =>
      have hx : x ∈ (childrenOf t p).filter (fun c => match kindOf t c with
          | some k => k.isText | none => false) := by rw [hq]; simp
      obtain ⟨hm, hk⟩ := List.mem_filter.mp hx
      cases hd : t.get? x with
      | none => rw [kindOf_eq, hd] at hk; simp at hk
      | some d => exact ⟨x, hm, d, hd, by rw [kindOf_of_get? hd] at hk; exact hk⟩

theorem doctypeFollowing_iff {t : Tree} {parent c : NodeId} :
    DoctypeFollowing t parent c ↔ doctypeFollows t parent c = true := by
  unfold DoctypeFollowing doctypeFollows
  constructor
  · rintro ⟨A, B, hL, hnot, d, hd, hk⟩
    rw [hL, ListUtil.splitAt?_append_cons_self hnot]
    exact List.any_eq_true.mpr ⟨d, hd, by simp [kindIs_iff.mp hk]⟩
  · intro h
    cases hq : ListUtil.splitAt? (childrenOf t parent) c with
    | none => rw [hq] at h; simp at h
    | some q =>
      rw [hq] at h
      obtain ⟨d, hd, hk⟩ := List.any_eq_true.mp h
      refine ⟨q.1, q.2, ListUtil.splitAt?_eq_some hq, ?_, d, hd, kindIs_iff.mpr (by simpa using hk)⟩
      exact ListUtil.splitAt?_not_mem_left hq

theorem elementPreceding_iff {t : Tree} {parent c : NodeId} :
    ElementPreceding t parent c ↔ elementPrecedes t parent c = true := by
  unfold ElementPreceding elementPrecedes
  constructor
  · rintro ⟨A, B, hL, hnot, d, hd, hk⟩
    rw [hL, ListUtil.splitAt?_append_cons_self hnot]
    exact List.any_eq_true.mpr ⟨d, hd, by simp [kindIs_iff.mp hk]⟩
  · intro h
    cases hq : ListUtil.splitAt? (childrenOf t parent) c with
    | none => rw [hq] at h; simp at h
    | some q =>
      rw [hq] at h
      obtain ⟨d, hd, hk⟩ := List.any_eq_true.mp h
      refine ⟨q.1, q.2, ListUtil.splitAt?_eq_some hq, ?_, d, hd, kindIs_iff.mpr (by simpa using hk)⟩
      exact ListUtil.splitAt?_not_mem_left hq

/-- `elementChildren` は kind `element` の子の filter そのものである。 -/
theorem hasElementChild_iff {t : Tree} {p : NodeId} :
    HasChildOfKind t p .element ↔ elementChildren t p ≠ [] := hasChildOfKind_iff

theorem hasElementChildOutside_iff {t : Tree} {p : NodeId} {excl : List NodeId} :
    HasChildOfKindOutside t p .element excl ↔
      (elementChildren t p).any (fun c => !excl.contains c) = true := hasChildOfKindOutside_iff

theorem hasDoctypeChildOutside_iff {t : Tree} {p : NodeId} {excl : List NodeId} :
    HasChildOfKindOutside t p .documentType excl ↔
      (doctypeChildren t p).any (fun c => !excl.contains c) = true := hasChildOfKindOutside_iff

theorem hasTwoElementChildren_iff {t : Tree} {p : NodeId}
    (hnd : (childrenOf t p).Nodup) :
    HasTwoElementChildren t p ↔ 1 < (elementChildren t p).length := by
  unfold HasTwoElementChildren
  constructor
  · rintro ⟨a, ha, b, hb, hab, hka, hkb⟩
    have hma : a ∈ elementChildren t p :=
      List.mem_filter.mpr ⟨ha, by simp [kindIs_iff.mp hka]⟩
    have hmb : b ∈ elementChildren t p :=
      List.mem_filter.mpr ⟨hb, by simp [kindIs_iff.mp hkb]⟩
    rcases Nat.lt_or_ge 1 (elementChildren t p).length with hlt | hle
    · exact hlt
    · exfalso
      cases hq : elementChildren t p with
      | nil => rw [hq] at hma; simp at hma
      | cons x xs =>
        cases hr : xs with
        | nil =>
          rw [hq, hr] at hma hmb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hma hmb
          exact hab (by rw [hma, hmb])
        | cons y ys => rw [hq, hr] at hle; simp at hle
  · intro h
    cases hq : elementChildren t p with
    | nil => rw [hq] at h; simp at h
    | cons x xs =>
      cases hr : xs with
      | nil => rw [hq, hr] at h; simp at h
      | cons y ys =>
        have hnd' : (elementChildren t p).Nodup := hnd.filter _
        rw [hq, hr] at hnd'
        have hxy : x ≠ y := by
          intro he
          exact (List.nodup_cons.mp hnd').1 (by rw [he]; simp)
        have hmx : x ∈ elementChildren t p := by rw [hq]; simp
        have hmy : y ∈ elementChildren t p := by rw [hq, hr]; simp
        obtain ⟨hcx, hkx⟩ := List.mem_filter.mp hmx
        obtain ⟨hcy, hky⟩ := List.mem_filter.mp hmy
        exact ⟨x, hcx, y, hcy, hxy, kindIs_iff.mpr (by simpa using hkx),
          kindIs_iff.mpr (by simpa using hky)⟩

theorem elementInsertionBlocked_iff {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} :
    ElementInsertionBlocked t parent child excl ↔
      checkElementInsertion t parent child excl ≠ .ok () := by
  unfold ElementInsertionBlocked checkElementInsertion
  by_cases hel : (elementChildren t parent).any (fun c => !excl.contains c) = true
  · rw [if_pos hel]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    exact Or.inl (hasElementChildOutside_iff.mpr hel)
  · rw [if_neg hel]
    cases child with
    | none =>
      simp only [ne_eq, not_true_eq_false, iff_false, not_or]
      refine ⟨fun hq => hel (hasElementChildOutside_iff.mp hq), ?_, ?_⟩
      · rintro ⟨c', hc', -⟩
        simp at hc'
      · rintro ⟨c', hc', -, -⟩
        simp at hc'
    | some c =>
      simp only []
      by_cases hdf : doctypeFollows t parent c = true
      · rw [if_pos hdf]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
        exact Or.inr (Or.inl ⟨c, rfl, doctypeFollowing_iff.mpr hdf⟩)
      · rw [if_neg hdf]
        by_cases hdt : (kindOf t c == some .documentType && !excl.contains c) = true
        · rw [if_pos hdt]
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', ne_eq, reduceCtorEq,
            not_false_eq_true, iff_true] at hdt ⊢
          exact Or.inr (Or.inr ⟨c, rfl, kindIs_iff.mpr hdt.1, by simpa using hdt.2⟩)
        · rw [if_neg hdt]
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', not_and] at hdt
          simp only [ne_eq, not_true_eq_false, iff_false, not_or]
          refine ⟨fun hq => hel (hasElementChildOutside_iff.mp hq), ?_, ?_⟩
          · rintro ⟨c', hc', hq⟩
            cases hc'
            exact hdf (doctypeFollowing_iff.mp hq)
          · rintro ⟨c', hc', hk, hex⟩
            cases hc'
            exact absurd (hdt (kindIs_iff.mp hk)) (by simpa using hex)

theorem doctypeInsertionBlocked_iff {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} :
    DoctypeInsertionBlocked t parent child excl ↔
      checkDoctypeInsertion t parent child excl ≠ .ok () := by
  unfold DoctypeInsertionBlocked checkDoctypeInsertion
  by_cases hdt : (doctypeChildren t parent).any (fun c => !excl.contains c) = true
  · rw [if_pos hdt]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    exact Or.inl (hasDoctypeChildOutside_iff.mpr hdt)
  · rw [if_neg hdt]
    cases child with
    | some c =>
      simp only []
      by_cases hep : elementPrecedes t parent c = true
      · rw [if_pos hep]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
        exact Or.inr (Or.inl ⟨c, rfl, elementPreceding_iff.mpr hep⟩)
      · rw [if_neg hep]
        simp only [ne_eq, not_true_eq_false, iff_false, not_or]
        refine ⟨fun hq => hdt (hasDoctypeChildOutside_iff.mp hq), ?_, ?_⟩
        · rintro ⟨c', hc', hq⟩
          cases hc'
          exact hep (elementPreceding_iff.mp hq)
        · rintro ⟨hc', -⟩
          simp at hc'
    | none =>
      simp only []
      by_cases hel : (elementChildren t parent).any (fun c => !excl.contains c) = true
      · rw [if_pos hel]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
        exact Or.inr (Or.inr ⟨trivial, hasElementChildOutside_iff.mpr hel⟩)
      · rw [if_neg hel]
        simp only [ne_eq, not_true_eq_false, iff_false, not_or]
        refine ⟨fun hq => hdt (hasDoctypeChildOutside_iff.mp hq), ?_, ?_⟩
        · rintro ⟨c', hc', -⟩
          simp at hc'
        · rintro ⟨-, hq⟩
          exact hel (hasElementChildOutside_iff.mp hq)

/--
**関係は結果を一つに決める。**

combinator ごとの補題を組むだけである。`Step` / `Return` / `Branch` のどれも
条件が `Prop` なので、両側が同じ枝を取る。
-/
theorem preInsertValidity_deterministic (t : Tree) (node parent : NodeId)
    (child : Option NodeId) (excl : List NodeId) :
    Deterministic (PreInsertValidity t node parent child excl) :=
  Step_deterministic <| Step_deterministic <| Step_deterministic <| Step_deterministic <|
  Step_deterministic <| Step_deterministic <|
  Branch_deterministic (Step_deterministic Done_deterministic) <|
  Step_deterministic <| Return_deterministic <|
  Branch_deterministic
    (Step_deterministic (Return_deterministic (Step_deterministic Done_deterministic)))
    (Branch_deterministic (Step_deterministic Done_deterministic)
      (Step_deterministic Done_deterministic))

/-! ## soundness -/

/--
**`ensurePreInsertionValidity` の結果は、成否によらず関係を満たす。**

仮定を置かないので、「どの入力でどの例外を返すか」まで関係が決めることになる。
`WellFormed` が要るのは step 2（`isInclusiveAncestorOf` と `InclusiveAncestor` の対応）と
step 8.1（children に重複が無いこと）である。
-/
theorem ensurePreInsertionValidity_spec {t : Tree} (hwf : WellFormed t)
    (node parent : NodeId) (child : Option NodeId) (excl : List NodeId) :
    PreInsertValidity t node parent child excl
      (ensurePreInsertionValidity t node parent child excl) := by
  unfold PreInsertValidity ensurePreInsertionValidity Step Branch Return Done
  cases hpd : t.get? parent with
  | none => exact Or.inl ⟨by rw [inTree_iff, hpd]; simp, rfl⟩
  | some pd =>
  simp only []
  refine Or.inr ⟨by rw [inTree_iff, hpd]; simp, ?_⟩
  cases hnd : t.get? node with
  | none => exact Or.inl ⟨by rw [inTree_iff, hnd]; simp, rfl⟩
  | some nd =>
  simp only []
  refine Or.inr ⟨by rw [inTree_iff, hnd]; simp, ?_⟩
  -- step 1
  by_cases h1 : (pd.kind = .document ∨ pd.kind = .documentFragment ∨ pd.kind = .element)
  · have hb1 : (pd.kind == .document || pd.kind == .documentFragment ||
        pd.kind == .element) = true := by rcases h1 with h | h | h <;> simp [h]
    rw [if_neg (by simp [hb1])]
    refine Or.inr ⟨by rw [parentIsContainer_iff hpd]; exact fun hq => hq h1, ?_⟩
    -- step 2
    by_cases h2 : isInclusiveAncestorOf t node parent = true
    · rw [if_pos h2]
      exact Or.inl ⟨(isInclusiveAncestorOf_iff hwf node parent).mp h2, rfl⟩
    · rw [if_neg h2]
      refine Or.inr ⟨fun hq => h2 ((isInclusiveAncestorOf_iff hwf node parent).mpr hq), ?_⟩
      -- step 3
      by_cases h3 : childHasParent t child parent = true
      · rw [if_neg (by simp [h3])]
        refine Or.inr ⟨not_not_intro (childIsChildOf_iff.mpr h3), ?_⟩
        -- step 4
        by_cases h4 : (nd.kind = .documentFragment ∨ nd.kind = .documentType ∨
            nd.kind = .element ∨ nd.kind.isCharacterData = true)
        · have hb4 : (nd.kind == .documentFragment || nd.kind == .documentType ||
              nd.kind == .element || nd.kind.isCharacterData) = true := by
            rcases h4 with h | h | h | h <;> simp [h]
          rw [if_neg (by simp [hb4])]
          refine Or.inr ⟨by rw [nodeIsInsertable_iff hnd]; exact fun hq => hq h4, ?_⟩
          -- step 5
          by_cases h5 : pd.kind = .document
          · rw [if_neg (by simp [h5])]
            refine Or.inr ⟨by rw [kindIs_iff, kindOf_of_get? hpd]; simpa using h5, ?_⟩
            -- step 6
            by_cases h6 : nd.kind.isText = true
            · rw [if_pos h6]
              exact Or.inl ⟨(isText_iff hnd).mpr h6, rfl⟩
            · rw [if_neg h6]
              refine Or.inr ⟨fun hq => h6 ((isText_iff hnd).mp hq), ?_⟩
              -- step 7
              by_cases h7 : nd.kind.isCharacterData = true
              · rw [if_pos h7]
                exact Or.inl ⟨(isCharacterData_iff hnd).mpr h7, rfl⟩
              · rw [if_neg h7]
                refine Or.inr ⟨fun hq => h7 ((isCharacterData_iff hnd).mp hq), ?_⟩
                -- step 8
                by_cases h8 : nd.kind = .documentFragment
                · rw [if_pos (by simp [h8])]
                  refine Or.inl ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using h8, ?_⟩
                  by_cases h81a : 1 < (elementChildren t node).length
                  · rw [if_pos (by simp [h81a])]
                    exact Or.inl ⟨Or.inl
                      ((hasTwoElementChildren_iff (childrenOf_nodup hwf node)).mpr h81a), rfl⟩
                  by_cases h81b : textChildren t node = []
                  · rw [if_neg (by simp [h81a, h81b])]
                    refine Or.inr ⟨?_, ?_⟩
                    · rintro (h | h)
                      · exact h81a ((hasTwoElementChildren_iff (childrenOf_nodup hwf node)).mp h)
                      · exact hasTextChild_iff.mp h h81b
                    · by_cases h82 : elementChildren t node = []
                      · rw [if_pos (by simp [h82])]
                        exact Or.inl ⟨fun hq => hasElementChild_iff.mp hq h82, rfl⟩
                      · rw [if_neg (by simp [h82])]
                        refine Or.inr ⟨fun hq => hq (hasElementChild_iff.mpr h82), ?_⟩
                        by_cases h9 : checkElementInsertion t parent child excl = .ok ()
                        · rw [h9]
                          exact Or.inr ⟨fun hq => (elementInsertionBlocked_iff.mp hq) h9, rfl⟩
                        · refine Or.inl ⟨elementInsertionBlocked_iff.mpr h9, ?_⟩
                          cases hq : checkElementInsertion t parent child excl with
                          | ok u => exact absurd (by cases u; exact hq) h9
                          | error e =>
                            have : e = .hierarchyRequestError := by
                              unfold checkElementInsertion at hq
                              split at hq
                              · exact (Except.error.inj hq).symm
                              · split at hq
                                · simp at hq
                                · split at hq
                                  · exact (Except.error.inj hq).symm
                                  · split at hq
                                    · exact (Except.error.inj hq).symm
                                    · simp at hq
                            rw [this]
                  · rw [if_pos (by simp [h81b])]
                    exact Or.inl ⟨Or.inr (hasTextChild_iff.mpr h81b), rfl⟩
                · rw [if_neg (by simp [h8])]
                  refine Or.inr ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using h8, ?_⟩
                  -- step 9
                  by_cases h9 : nd.kind = .element
                  · rw [if_pos (by simp [h9])]
                    refine Or.inl ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using h9, ?_⟩
                    by_cases hc : checkElementInsertion t parent child excl = .ok ()
                    · rw [hc]
                      exact Or.inr ⟨fun hq => (elementInsertionBlocked_iff.mp hq) hc, rfl⟩
                    · refine Or.inl ⟨elementInsertionBlocked_iff.mpr hc, ?_⟩
                      cases hq : checkElementInsertion t parent child excl with
                      | ok u => exact absurd (by cases u; exact hq) hc
                      | error e =>
                        have : e = .hierarchyRequestError := by
                          unfold checkElementInsertion at hq
                          split at hq
                          · exact (Except.error.inj hq).symm
                          · split at hq
                            · simp at hq
                            · split at hq
                              · exact (Except.error.inj hq).symm
                              · split at hq
                                · exact (Except.error.inj hq).symm
                                · simp at hq
                        rw [this]
                  · rw [if_neg (by simp [h9])]
                    refine Or.inr ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using h9, ?_⟩
                    -- step 10-11
                    by_cases hc : checkDoctypeInsertion t parent child excl = .ok ()
                    · rw [hc]
                      exact Or.inr ⟨fun hq => (doctypeInsertionBlocked_iff.mp hq) hc, rfl⟩
                    · refine Or.inl ⟨doctypeInsertionBlocked_iff.mpr hc, ?_⟩
                      cases hq : checkDoctypeInsertion t parent child excl with
                      | ok u => exact absurd (by cases u; exact hq) hc
                      | error e =>
                        have : e = .hierarchyRequestError := by
                          unfold checkDoctypeInsertion at hq
                          split at hq
                          · exact (Except.error.inj hq).symm
                          · split at hq
                            · split at hq
                              · exact (Except.error.inj hq).symm
                              · simp at hq
                            · split at hq
                              · exact (Except.error.inj hq).symm
                              · simp at hq
                        rw [this]
          · rw [if_pos (by simp [h5])]
            by_cases hdt : nd.kind = .documentType
            · rw [if_pos (by simp [hdt])]
              refine Or.inl ⟨by rw [kindIs_iff, kindOf_of_get? hpd]; simpa using h5, ?_⟩
              exact Or.inl ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using hdt, rfl⟩
            · rw [if_neg (by simp [hdt])]
              refine Or.inl ⟨by rw [kindIs_iff, kindOf_of_get? hpd]; simpa using h5, ?_⟩
              exact Or.inr ⟨by rw [kindIs_iff, kindOf_of_get? hnd]; simpa using hdt, rfl⟩
        · rw [if_pos (by
            simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
            simp only [not_or] at h4
            exact ⟨⟨⟨h4.1, h4.2.1⟩, h4.2.2.1⟩, by simpa using h4.2.2.2⟩)]
          exact Or.inl ⟨by rw [nodeIsInsertable_iff hnd]; exact h4, rfl⟩
      · rw [if_pos (by simp [h3])]
        exact Or.inl ⟨fun hq => h3 (childIsChildOf_iff.mp hq), rfl⟩
  · rw [if_pos (by
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      simp only [not_or] at h1
      exact ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩)]
    exact Or.inl ⟨by rw [parentIsContainer_iff hpd]; exact h1, rfl⟩

/--
**関係を満たす結果は、実行関数の結果そのものである。**

soundness（仮定なし）と一意性を繋いだもの。
「例外の種類まで含めて関係が決める」という主張はこれである。
-/
theorem ensurePreInsertionValidity_eq_of_spec {t : Tree} (hwf : WellFormed t)
    {node parent : NodeId} {child : Option NodeId} {excl : List NodeId}
    {r : Except DOMException Unit} (h : PreInsertValidity t node parent child excl r) :
    r = ensurePreInsertionValidity t node parent child excl :=
  preInsertValidity_deterministic t node parent child excl _ _ h
    (ensurePreInsertionValidity_spec hwf node parent child excl)

/-- **関係と実行関数は同じ結果を指す。** 上の二つを繋いだ形。 -/
theorem preInsertValidity_iff {t : Tree} (hwf : WellFormed t)
    {node parent : NodeId} {child : Option NodeId} {excl : List NodeId}
    {r : Except DOMException Unit} :
    PreInsertValidity t node parent child excl r ↔
      ensurePreInsertionValidity t node parent child excl = r := by
  constructor
  · intro h; exact (ensurePreInsertionValidity_eq_of_spec hwf h).symm
  · intro h; rw [← h]; exact ensurePreInsertionValidity_spec hwf node parent child excl

end Dom.Spec
