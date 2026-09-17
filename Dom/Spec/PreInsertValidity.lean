import Dom.Basic.State
import Dom.Basic.Order

/-!
# pre-insertion validity の関係意味論（§4.2.3 step 1-11）

`Dom.Spec.Result` の `PreInsertResult` が「どの入力でどの例外を返すか」まで
述べるには、validity の成否と例外が要る。実行関数 `ensurePreInsertionValidity`
をそのまま使うと関係が実装の言い換えになるので、仕様本文から独立に書き写す。

この module は `Dom.Basic.*` しか import しない。したがって実行側の
algorithm（`ensurePreInsertionValidity` とその補助検査）を呼びようがない。
実行関数との一致は `Dom/Properties/PreInsertValidityBridge.lean` で別に証明する。

## 構成

| 定義 | 仕様の step |
| --- | --- |
| `PreInsertValid` | 1-11 を全部通る |
| `PreInsertError` | どの step でどの例外になるか（先に落ちる step が優先） |

`PreInsertError` は優先順位を「先の step を通ること」で表す。たとえば step 4 の
枝は step 1-3 を通ることを連言に含むので、step 1-3 で落ちる入力とは排他になる。
-/

namespace Dom.Spec

open Dom

/-! ## step 2-3：reference child -/

/-- §4.2.3 pre-insert step 2-3。`child` が `node` 自身ならその次の兄弟に取り直す。 -/
def PreInsertRefChild (t : Tree) (node : NodeId) (child : Option NodeId) : Option NodeId :=
  if child = some node then nextSibling t node else child

/-! ## children の分類と tree order -/

/-- `p` の children のうち kind が `k` であるもの。 -/
def childrenOfKind (t : Tree) (p : NodeId) (k : NodeKind) : List NodeId :=
  (childrenOf t p).filter fun c => kindOf t c == some k

/-- `p` の children のうち Text であるもの（CDATASection を含む）。 -/
def textChildrenOf (t : Tree) (p : NodeId) : List NodeId :=
  (childrenOf t p).filter fun c =>
    match kindOf t c with
    | some k => k.isText
    | none => false

/-- `c` の後ろ（children の並び）に kind `k` の child がある。 -/
def HasKindAfter (t : Tree) (parent c : NodeId) (k : NodeKind) : Prop :=
  match Dom.ListUtil.splitAt? (childrenOf t parent) c with
  | none => False
  | some (_, tail) => ∃ d, d ∈ tail ∧ kindOf t d = some k

/-- `c` の前（children の並び）に kind `k` の child がある。 -/
def HasKindBefore (t : Tree) (parent c : NodeId) (k : NodeKind) : Prop :=
  match Dom.ListUtil.splitAt? (childrenOf t parent) c with
  | none => False
  | some (head, _) => ∃ d, d ∈ head ∧ kindOf t d = some k

/-! ## step 8.2 / 9・10-11 の部分検査 -/

/--
step 8.2 / step 9。element（または element child を持つ fragment）を入れる条件。

parent の element child が `excl` の外に無く、`child` の位置の後ろに
excluded でない doctype が来ないこと。
-/
def ElementInsertionOk (t : Tree) (parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  (∀ e, e ∈ childrenOfKind t parent .element → e ∈ excl) ∧
  match child with
  | none => True
  | some c =>
    ¬ HasKindAfter t parent c .documentType ∧
      (kindOf t c = some .documentType → c ∈ excl)

/--
step 10-11。doctype を入れる条件。

parent の doctype child が `excl` の外に無く、`child` の位置より前に element が
無く、`child` が null なら parent に element child が無いこと。
-/
def DoctypeInsertionOk (t : Tree) (parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  (∀ d, d ∈ childrenOfKind t parent .documentType → d ∈ excl) ∧
  match child with
  | none => ∀ e, e ∈ childrenOfKind t parent .element → e ∈ excl
  | some c => ¬ HasKindBefore t parent c .element

/-! ## step 1-11 を通ること -/

/-- step 4 が許す node の kind。 -/
def PreNodeKindOk (nd : NodeData) : Prop :=
  nd.kind = .documentFragment ∨ nd.kind = .documentType ∨ nd.kind = .element ∨
    nd.kind.isCharacterData = true

/-- step 5 が許す parent と node の組。 -/
def PreDoctypeParentOk (pd nd : NodeData) : Prop :=
  nd.kind = .documentType → pd.kind = .document

/-- step 6 が禁じるもの。 -/
def PreNoTextInDocument (pd nd : NodeData) : Prop :=
  pd.kind = .document → nd.kind.isText = false

/-- step 6-11 のうち、parent が Document のときにだけ効く条件。 -/
def PreInsertDocumentOk (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) (_pd nd : NodeData) : Prop :=
  (nd.kind = .documentFragment →
    (childrenOfKind t node .element).length ≤ 1 ∧ textChildrenOf t node = []) ∧
  ((nd.kind = .element ∨
      (nd.kind = .documentFragment ∧ childrenOfKind t node .element ≠ [])) →
    ElementInsertionOk t parent child excl) ∧
  (nd.kind = .documentType → DoctypeInsertionOk t parent child excl)

/-- step 1-11 を通ることを、parent と node の data を固定して書いたもの。 -/
def PreInsertValidCore (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) (pd nd : NodeData) : Prop :=
  t.get? parent = some pd ∧ t.get? node = some nd ∧
    pd.kind.canHaveChildren = true ∧
    ¬ InclusiveAncestor t node parent ∧
    (∀ c, child = some c → parentOf t c = some parent) ∧
    PreNodeKindOk nd ∧
    PreDoctypeParentOk pd nd ∧
    PreNoTextInDocument pd nd ∧
    (pd.kind = .document → PreInsertDocumentOk t node parent child excl pd nd)

/--
**§4.2.3 pre-insertion validity を全部通る。**

順序を持たない連言である。どの例外になるかは `PreInsertError` が持つ。

step 5 は「parent が Document でなければ、doctype のときだけ落ちて、あとは return」
なので、step 6-11 は parent が Document のときにだけ効く。
-/
def PreInsertValid (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Prop :=
  ∃ pd nd, PreInsertValidCore t node parent child excl pd nd

/-! ## どの step で落ちるか -/

/-- step 1-2 のうち、parent と node が在り parent が children を持てること（step 1 まで通る）。 -/
def PreBase (t : Tree) (node parent : NodeId) (pd nd : NodeData) : Prop :=
  t.get? parent = some pd ∧ t.get? node = some nd ∧ pd.kind.canHaveChildren = true

/-- step 1-3 を通る。 -/
def PreP123 (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (pd nd : NodeData) : Prop :=
  PreBase t node parent pd nd ∧ ¬ InclusiveAncestor t node parent ∧
    (∀ c, child = some c → parentOf t c = some parent)

/-- step 1-4 を通る。 -/
def PreP1234 (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (pd nd : NodeData) : Prop :=
  PreP123 t node parent child pd nd ∧ PreNodeKindOk nd

/-- step 1-5 を通る。 -/
def PreP12345 (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (pd nd : NodeData) : Prop :=
  PreP1234 t node parent child pd nd ∧ PreDoctypeParentOk pd nd

/-- step 1-6 を通る。 -/
def PreP123456 (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (pd nd : NodeData) : Prop :=
  PreP12345 t node parent child pd nd ∧ PreNoTextInDocument pd nd

/--
**§4.2.3 pre-insertion validity がどの例外で落ちるか。**

枝は優先順位を表す。先に落ちる step の枝は、後ろの step の枝の前提（先の step を
通ること）を満たさない。同じ step に属する二つの枝（8.1 と 8.2/9）は同じ例外を
持つので、どの入力でも成り立つ `e` は高々一つに定まる。
-/
def PreInsertError (t : Tree) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) (e : DOMException) : Prop :=
  -- parent が無い
  (t.get? parent = none ∧ e = .notFoundError) ∨
  -- node が無い
  (∃ pd, t.get? parent = some pd ∧ t.get? node = none ∧ e = .notFoundError) ∨
  -- step 1：parent が children を持てない
  (∃ pd nd, t.get? parent = some pd ∧ t.get? node = some nd ∧
    pd.kind.canHaveChildren = false ∧ e = .hierarchyRequestError) ∨
  -- step 2：循環する
  (∃ pd nd, PreBase t node parent pd nd ∧ InclusiveAncestor t node parent ∧
    e = .hierarchyRequestError) ∨
  -- step 3：child の parent が違う
  (∃ pd nd, PreBase t node parent pd nd ∧ ¬ InclusiveAncestor t node parent ∧
    (∃ c, child = some c ∧ parentOf t c ≠ some parent) ∧ e = .notFoundError) ∨
  -- step 4：node の kind が許されない
  (∃ pd nd, PreP123 t node parent child pd nd ∧ ¬ PreNodeKindOk nd ∧
    e = .hierarchyRequestError) ∨
  -- step 5：doctype の parent が Document でない
  (∃ pd nd, PreP1234 t node parent child pd nd ∧ ¬ PreDoctypeParentOk pd nd ∧
    e = .hierarchyRequestError) ∨
  -- step 6：Document に Text
  (∃ pd nd, PreP12345 t node parent child pd nd ∧ ¬ PreNoTextInDocument pd nd ∧
    e = .hierarchyRequestError) ∨
  -- step 8.1：fragment が element を二つ持つか Text を持つ
  (∃ pd nd, PreP123456 t node parent child pd nd ∧ pd.kind = .document ∧
    nd.kind = .documentFragment ∧
    (1 < (childrenOfKind t node .element).length ∨ textChildrenOf t node ≠ []) ∧
    e = .hierarchyRequestError) ∨
  -- step 8.2 / 9：element の挿入条件
  (∃ pd nd, PreP123456 t node parent child pd nd ∧ pd.kind = .document ∧
    (nd.kind = .element ∨ (nd.kind = .documentFragment ∧ childrenOfKind t node .element ≠ [])) ∧
    ¬ ElementInsertionOk t parent child excl ∧ e = .hierarchyRequestError) ∨
  -- step 10-11：doctype の挿入条件
  (∃ pd nd, PreP123456 t node parent child pd nd ∧ pd.kind = .document ∧
    nd.kind = .documentType ∧
    ¬ DoctypeInsertionOk t parent child excl ∧ e = .hierarchyRequestError)

end Dom.Spec
