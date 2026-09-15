import Dom.Spec.Insert

/-!
# `replace` の関係意味論（§4.2.3）

`remove` / `adopt` / `insert` と同じ方針。仕様本文から独立に書き写した関係を置き、
実行関数がそれを満たすことは別に証明する。

`replace` は step 6 で `adopt` を、step 7 で `remove` を、step 9 で `insert` を呼ぶので、
関係もそれぞれ `AdoptSpec` / `RemoveSpec` / `InsertSpec` を composition する。
仕様本文がそう書いているとおりの構成であり、実行関数の再利用ではない。

step 1（ensure pre-insertion validity）は別の algorithm なので、ここには含めない。
`InsertSpec` が pre-insert を含まないのと同じ扱いである。
例外の順序は `Dom/Properties/Contract.lean` にある。

## 位置は木を変える前に決まる

step 2-3 の reference child と step 4 の previous sibling は、
**adopt も removal も走る前**の木で決まる。record に載るのはその値である。
step 8 の `nodes` だけは removal の後に読むが、
`child` は `node` の子ではありえない（step 1 の validity が
「`node` は `parent` の inclusive ancestor でない」を保証し、
`child` の parent は `parent` である）ので、どこで読んでも同じ列になる。
その一致は soundness の側で示す。
-/

namespace Dom.Spec

open Dom

/-! ## step 2-3：reference child -/

/--
仕様の step 2-3。

`child` の次の兄弟。ただしそれが `node` 自身なら、`node` の次の兄弟。
`node` は step 9 で動くので、その分ずらしておく。
-/
def ReferenceChild (t : Tree) (child node : NodeId) (ref : Option NodeId) : Prop :=
  (nextSibling t child = some node ∧ ref = nextSibling t node) ∨
  (nextSibling t child ≠ some node ∧ ref = nextSibling t child)

/-! ## step 7：`child` を外す -/

/--
仕様の step 7。

`child` に parent があれば（observer を抑えて）外し、removedNodes を « child » にする。
adopt の後で見るので、`node` を adopt した拍子に `child` が外れていれば何もしない
（`replace(child, child, parent)` がその場合である）。
-/
def ChildRemoved (s s' : DOMState) (child : NodeId) (removed : List NodeId) : Prop :=
  (parentOf s.tree child = none ∧ removed = [] ∧ s' = s) ∨
  ((∃ p, parentOf s.tree child = some p) ∧ removed = [child] ∧ RemoveSpec s child true s')

/-! ## 仕様の assertion が要る前提 -/

/--
DocumentFragment は誰の子にもならない。

仕様の `insert` は step 1 で fragment を children に展開するので、
fragment が誰かの子になっている状態は algorithm からは作れない。
ところが `StructurallyValid`（`Dom/Validity/Structural.lean`）はこれを言っていない。
`documentHasNoParent` の fragment 版が無い、ということである。

`replace` の step 10 の assertion（addedNodes と removedNodes のどちらかは空でない）は
これに依存する。`node` が `child` と同じ空の DocumentFragment だと、
adopt が `child` を親から外してしまい、どちらの列も空になるからである。
その状態は本物の DOM には無いので、必要なところで仮定する。
-/
def FragmentsAreRoots (t : Tree) : Prop :=
  ∀ n d, t.get? n = some d → d.kind = .documentFragment → d.parent = none

/-! ## 全体 -/

/--
**`replace` の関係意味論。**

`ReplaceSpec s child node parent s'` は
「状態 `s` で `parent` の子 `child` を `node` に置き換えると `s'` になる」と読む。
step 1 の validity を通った後の話である。

step 10 の record は一つだけ積まれる。step 7 と step 9 は
suppress observers を立てて呼ぶので、そちらは record を積まない。
-/
def ReplaceSpec (s : DOMState) (child node parent : NodeId) (s' : DOMState) : Prop :=
  ∃ (ref prev : Option NodeId) (nodes removed : List NodeId) (pd : NodeData)
    (s₁ s₂ s₃ : DOMState),
    -- step 2-3
    ReferenceChild s.tree child node ref ∧
    -- step 4
    prev = previousSibling s.tree child ∧
    s.tree.get? parent = some pd ∧
    -- step 6
    AdoptSpec s node pd.ownerDocument s₁ ∧
    -- step 7
    ChildRemoved s₁ s₂ child removed ∧
    -- step 8
    NodesToInsert s₂.tree node nodes ∧
    -- step 9
    InsertSpec s₂ node parent ref true s₃ ∧
    -- step 10。"queue a tree mutation record" の step 1 は、どちらかが空でないこと。
    (nodes ≠ [] ∨ removed ≠ []) ∧
    TreeRecordQueued s₃ s' parent nodes removed prev ref false ∧
    ObserverOnly s₃ s'

end Dom.Spec
