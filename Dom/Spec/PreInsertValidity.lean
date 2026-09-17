import Dom.Basic.State
import Dom.Basic.Order

/-!
# `ensure pre-insert validity` の関係意味論（§4.2.3 step 1-11）

実行関数 `ensurePreInsertionValidity` をそのまま関係にすると、仕様の step 1-11 を
読み違えて実装しても関係がその実装に合わせて成り立つ。だからここでは step 1-11 を
**実行側の関数を呼ばずに**書く。

条件は `Dom/Basic/` の語彙（`childrenOf` / `parentOf` / `kindOf` / `InclusiveAncestor`）
と list の所属だけで書き、`elementChildren` や `doctypeFollows` のような実行側の helper は
使わない。この file は `Dom.Basic.*` しか import しないので、import graph がそのまま
「実行側を呼びようがない」ことの保証になっている。

制御の流れ（どの step が先か、どこで return するか）は仕様の `<ol>` の形をそのまま写し、
`Step` / `Return` / `Branch` / `Done` の四つの combinator で組む。この形だと関係が
**構造的に結果を一つに決める**（`preInsertValidity_deterministic`）ので、実行側に触れずに
一意性が言える。実行関数がこの関係を満たすこと（soundness）と、逆にこの関係を満たす結果が
実行関数の結果そのものであることは `Dom/Properties/PreInsertValidityBridge.lean` で示す。

`PreInsertValid` / `PreInsertError` は、この結果の関係を使いやすい pre/post 条件の形に
開いた略記である（それぞれ `.ok ()` と `.error e` の場合）。

## 「following」「preceding」の読み

step 9 の「a doctype is following child」と step 11 の「an element is preceding child」の
`following` / `preceding` は、仕様では**木の順序**である。ここでは
**`parent` の children の中での前後**として書いた。

**両者が一致することは証明してある**（`Dom/Spec/PreInsertValidityOrder.lean` の
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
木順との一致は `doctypeFollowing_iff_precedes`（`Dom/Spec/PreInsertValidityOrder.lean`）にある。

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

/--
**関係は結果を一つに決める。**

combinator ごとの補題を組むだけである。`Step` / `Return` / `Branch` のどれも
条件が `Prop` なので、両側が同じ枝を取る。実行関数には触れない。
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

/-! ## pre-insert step 2-3：reference child -/

/-- §4.2.3 pre-insert step 2-3。`child` が `node` 自身ならその次の兄弟に取り直す。 -/
def PreInsertRefChild (t : Tree) (node : NodeId) (child : Option NodeId) : Option NodeId :=
  if child = some node then nextSibling t node else child

/-! ## pre/post 条件の形 -/

/--
step 1-11 を通ること。`PreInsertValidity` の `.ok ()` を開いた略記である。
-/
def PreInsertValid (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  PreInsertValidity t node parent child excl (.ok ())

/--
どの例外で落ちるか。`PreInsertValidity` の `.error e` を開いた略記である。
優先順位は `PreInsertValidity` の制御の流れが表す。
-/
def PreInsertError (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) (e : DOMException) : Prop :=
  PreInsertValidity t node parent child excl (.error e)

end Dom.Spec
