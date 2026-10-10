import Dom.Spec.SelectorMatch
import Dom.Spec.RangeDeleteSound
import Dom.Spec.RangeDeleteCongr
import Dom.Selector.Api

/-!
# "scope-match a selectors string" の関係意味論（DOM §1.3、Selectors §17）

DOM の "scope-match a selectors string" は、selector を parse し、Selectors Level 4 の
"match a selector against a tree" を node の root と scoping root node で呼ぶ。
Selectors §17 はその結果を次の手順で定める（版は `docs/selectors-spec-version.md`）。

1. candidate elements を、root element とその descendant element を tree order に並べたものとする。
2. scoping root があれば、その descendant でないものを candidate elements から除く。
3-4. selector に当たる element を、candidate elements の順に集める。

実行関数 `matchTree`（`Dom/Selector/Api.lean`）は root からではなく node の部分木を列挙し、
node 自身を除く。scoping root の descendant は node の部分木の node 自身以外にちょうど一致するので、
結果は同じになる。ここではそれを、列の要素と並びの両方について示す。

DOM の呼び出しでは root が Document や DocumentFragment でありうるが、step 1 は element だけを
候補にするので、root の種類は結果に効かない。
-/

namespace Dom.Spec

open Dom
open Dom.ListUtil (eq_of_pairwise_of_mem_iff)

/--
**Selectors §17 "match a selector against a tree"（scoping root が一つの場合）。**

`l` は、`rootNode` の inclusive descendant である element のうち、`scope` の descendant で、
selector に当たるものを、tree order に並べた列である。
-/
def MatchAgainstTree (t : Tree) (sel : Selectors.SelectorList) (rootNode scope : NodeId)
    (l : List NodeId) : Prop :=
  (∀ e, e ∈ l ↔
    -- step 1
    InclusiveDescendant t e rootNode ∧ isElementNode t e = true ∧
    -- step 2
    Descendant t e scope ∧
    -- step 3-4
    SelectorListMatches { tree := t, scope := some scope } sel e) ∧
  -- step 1 の並び
  l.Pairwise (PrecedesStruct t)

/--
**DOM §1.3 "scope-match a selectors string" の、結果まで含めた関係。**

1. selector を parse する。failure なら SyntaxError。
2. node の root について、scoping root を node として "match a selector against a tree" の結果を返す。
-/
def ScopeMatchResult (t : Tree) (selectors : String) (node : NodeId) :
    Except DOMException (List NodeId) → Prop
  | .error e => Selectors.parseSelector selectors = none ∧ e = .syntaxError
  | .ok l => ∃ sel, Selectors.parseSelector selectors = some sel ∧
      MatchAgainstTree t sel (root t node) node l

/-- node の descendant は、node の root の inclusive descendant である。 -/
private theorem inclusiveDescendant_root_of_descendant {t : Tree} (hwf : WellFormed t) {e node : NodeId}
    (h : Descendant t e node) : InclusiveDescendant t e (root t node) := by
  have hr : root t e = root t node := root_eq_of_ancestor hwf h
  rw [← hr]
  exact root_inclusive_ancestor t e

/-- **`matchTree` は "match a selector against a tree" を満たす。** -/
theorem matchTree_spec {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d) (sel : Selectors.SelectorList) :
    MatchAgainstTree t sel (root t node) node (matchTree t sel node) := by
  refine ⟨fun e => ?_, ?_⟩
  · rw [mem_matchTree_iff_spec hwf hav hn sel e]
    constructor
    · rintro ⟨hd, hel, hm⟩
      exact ⟨inclusiveDescendant_root_of_descendant hwf hd, hel, hd, hm⟩
    · rintro ⟨-, hel, hd, hm⟩
      exact ⟨hd, hel, hm⟩
  · unfold matchTree
    refine List.Pairwise.filter _ (List.Pairwise.filter _ ?_)
    have hnd := preorder_nodup hwf node
    refine ((pairwise_precedesIn hnd).and hnd).imp_of_mem ?_
    intro x y hx hy ⟨hxy, hne⟩
    exact (precedesIn_preorder_iff_struct hwf hn ((mem_preorder_iff hwf hn x).mp hx)
      ((mem_preorder_iff hwf hn y).mp hy) hne).mp hxy

/-- **"match a selector against a tree" の結果は一つに決まる。** -/
theorem matchAgainstTree_unique {t : Tree} (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) {sel : Selectors.SelectorList} {l₁ l₂ : List NodeId}
    (h₁ : MatchAgainstTree t sel (root t node) node l₁)
    (h₂ : MatchAgainstTree t sel (root t node) node l₂) : l₁ = l₂ := by
  obtain ⟨rd, hrd⟩ := exists_data_root hwf hn
  have hdesc : ∀ x ∈ l₁, InclusiveDescendant t x (root t node) :=
    fun x hx => ((h₁.1 x).mp hx).1
  have hmem : ∀ x ∈ l₁, x ∈ preorder t (root t node) :=
    fun x hx => (mem_preorder_iff hwf hrd x).mpr (hdesc x hx)
  have hnd := preorder_nodup hwf (root t node)
  have hirr : ∀ x ∈ l₁, ¬ PrecedesStruct t x x := by
    intro x hx hp
    have := precedesIn_preorder_of_struct hwf hrd (hdesc x hx) (hdesc x hx) hp
    rw [precedesIn_self_of_nodup hnd] at this
    cases this
  refine eq_of_pairwise_of_mem_iff hirr ?_ h₁.2 h₂.2 (fun x => (h₁.1 x).trans (h₂.1 x).symm)
  intro x hx y hy hxy hyx
  have hne : x ≠ y := fun he => hirr x hx (he ▸ hxy)
  have e₁ := precedesIn_preorder_of_struct hwf hrd (hdesc x hx) (hdesc y hy) hxy
  have e₂ := precedesIn_preorder_of_struct hwf hrd (hdesc y hy) (hdesc x hx) hyx
  rw [precedesIn_asymm hne (hmem x hx) (hmem y hy) e₁] at e₂
  cases e₂

/-- **`scopeMatch` の結果は関係を満たす。** -/
theorem scopeMatch_result_sound {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d) (selectors : String) :
    ScopeMatchResult t selectors node (scopeMatch t selectors node) := by
  unfold scopeMatch
  cases hp : Selectors.parseSelector selectors with
  | none => exact ⟨hp, rfl⟩
  | some sel => exact ⟨sel, hp, matchTree_spec hwf hav hn sel⟩

/-- **関係を満たす結果は、`scopeMatch` の結果と等しい。** -/
theorem scopeMatch_result_complete {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d) {selectors : String}
    {r : Except DOMException (List NodeId)} (h : ScopeMatchResult t selectors node r) :
    r = scopeMatch t selectors node := by
  unfold scopeMatch
  rcases r with e | l
  · obtain ⟨hp, rfl⟩ := h
    rw [hp]
  · obtain ⟨sel, hp, hm⟩ := h
    rw [hp, matchAgainstTree_unique hwf hn hm (matchTree_spec hwf hav hn sel)]

end Dom.Spec
