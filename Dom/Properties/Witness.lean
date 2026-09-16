import Dom.Properties.CloneOk
import Dom.Selector.Api

/-!
# 定理が空虚でないことの証人

定理は仮定を満たす状態が一つも無ければ何も言っていない。`AdmissibleDOMState` は
七つの条件の連言なので、**それを満たす状態が本当にあるか**は自明ではない。

ここでは具体的な状態を一つ組み立て、決定手続き `checkAdmissibleDOMState` が
`true` を返すことを `rfl` で確かめ、`checkAdmissibleDOMState_iff` を通して
`AdmissibleDOMState` を得る。そのうえで主定理をその状態に当てて、
結論が実際に成り立つことを見る。

**仮定が飾りでないこと**も同じ file で見る。`adoptNode` に Document を渡すと
本当に失敗するので、`adoptNode_isOk` の `d.kind ≠ document` は外せない。

固定 scenario 154 本は `lake exe dom-model --check` が毎 step の admissibility を
実行時に検査しているので、経験的な証人はそちらにもある。この file は
**証明の側にも証人を置く**ためのものである。
-/

namespace Dom.Witness

/-- document > html > text の小さな木。 -/
def tree : Tree :=
  { nodes := NodeStore.empty
      |>.insert ⟨0⟩ { kind := .document, children := [⟨1⟩], ownerDocument := ⟨0⟩ }
      |>.insert ⟨1⟩ { kind := .element, parent := some ⟨0⟩, children := [⟨2⟩],
                      ownerDocument := ⟨0⟩, localName := "html" }
      |>.insert ⟨2⟩ { kind := .text, parent := some ⟨1⟩, ownerDocument := ⟨0⟩, data := "x" } }

def state : DOMState := { tree := tree }

/-- **妥当な状態は実在する。** 決定手続きが `true` を返すので `AdmissibleDOMState` が従う。 -/
theorem state_admissible : AdmissibleDOMState state :=
  (checkAdmissibleDOMState_iff state).mp (by rfl)

theorem get?_document : state.tree.get? ⟨0⟩ =
    some { kind := .document, children := [⟨1⟩], ownerDocument := ⟨0⟩ } := rfl

theorem get?_html : state.tree.get? ⟨1⟩ =
    some { kind := .element, parent := some ⟨0⟩, children := [⟨2⟩],
           ownerDocument := ⟨0⟩, localName := "html" } := rfl

/-! ## 主定理をこの状態に当てる -/

/-- `cloneNode` は失敗しない（§15）。 -/
example : ∃ c s', cloneNode state ⟨1⟩ true = .ok (c, s') :=
  cloneNode_isOk state_admissible get?_html

/-- `adoptNode` は失敗しない。 -/
example : ∃ s', adoptNode state ⟨0⟩ ⟨1⟩ = .ok (⟨1⟩, s') :=
  adoptNode_isOk state_admissible get?_document rfl get?_html (by simp)

/-- `remove` は parent がある node に対して成功する（契約）。 -/
example : ∃ s', remove state ⟨1⟩ = .ok s' :=
  (remove_succeeds_iff state_admissible.wellFormed).mpr rfl

/-! ## 仮定は飾りではない

外すと結論が成り立たなくなることを、同じ状態の上で見る。
-/

/-- `adoptNode_isOk` の「node が Document でない」を外すと失敗する。 -/
example : adoptNode state ⟨0⟩ ⟨0⟩ = .error .notSupportedError := rfl

/-- `remove_succeeds_iff` の「parent がある」を外すと失敗する。 -/
example : remove state ⟨0⟩ = .error .notFoundError := rfl

/-- `querySelector` の受け手が `ParentNode` でなければ `TypeError` になる。 -/
example : querySelector state.tree "p" ⟨2⟩ = .error .typeError := rfl

/-! ## selector の側

`parseSelector` と照合は整礎再帰なので、`rfl` では簡約できない（kernel は
well-founded recursion を展開しない）。selector の実際の結果は
`lake exe dom-model --check test/scenarios` と差分テストが実行時に見ている。
ここで見られるのは、本体に入る前の検査だけである。
-/

/-- 受け手が `ParentNode` でなければ、selector を読む前に `TypeError` になる。 -/
example : querySelector state.tree "p" ⟨2⟩ = .error .typeError := rfl

/-- `matches()` の受け手が Element でなければ同じく `TypeError`。 -/
example : matchesSelector state.tree "p" ⟨0⟩ = .error .typeError := rfl

end Dom.Witness
