import Dom.Spec.Result
import Dom.Spec.ChildNode
import Dom.Spec.ReplaceAllSound
import Dom.Spec.AdoptSound
import Dom.Spec.CharacterDataResult
import Dom.Spec.ScopeMatch
import Dom.Spec.Create
import Dom.Mutation.SetText
import Dom.Mutation.InsertAdjacent
import Dom.Mutation.Import
import Dom.Properties.Variadic
import Dom.Properties.Selector
import Dom.Spec.AttributeNodeSound
import Dom.Spec.Namespace
import Dom.Spec.TreeOrder

/-!
# 既存の関係を呼ぶだけの method（§4.2.3、§4.2.6、§4.4、§4.5、§4.8、§4.9）

本文の method の多くは、別の algorithm を呼んでその結果を返すだけである。ここでは、その algorithm の関係
（`PreInsertResult`・`ReplaceResult`・`RemoveResult`・`ReplaceAllSpec`・`ReplaceDataResult`・`AdoptSpec`・
`ScopeMatchResult`・`SelectorListMatches`）を使って method の結果を述べ、実行関数がそれを満たすことを示す。
-/

namespace Dom.Spec

open Dom Selectors

/-! ## §4.2.3・§4.4 の木の method -/

/-- §4.2.3 "pre-remove"：child の parent が parent でなければ NotFoundError、そうでなければ remove。 -/
def PreRemoveResult (s : DOMState) (child parent : NodeId) (r : Except DOMException DOMState) : Prop :=
  (parentOf s.tree child ≠ some parent ∧ r = .error .notFoundError) ∨
    (parentOf s.tree child = some parent ∧ RemoveResult s child false r)

theorem preRemove_result_sound {s : DOMState} (hwf : WellFormed s.tree) (child parent : NodeId) :
    PreRemoveResult s child parent (preRemove s child parent) := by
  by_cases hp : parentOf s.tree child = some parent
  · exact Or.inr ⟨hp, by rw [preRemove_of_parent hp]; exact remove_result_sound hwf child false⟩
  · refine Or.inl ⟨hp, ?_⟩
    unfold preRemove; rw [if_pos hp]

/-- §4.4 `removeChild(child)` は pre-remove。 -/
theorem removeChild_result_sound {s : DOMState} (hwf : WellFormed s.tree) (parent child : NodeId) :
    PreRemoveResult s child parent (removeChild s parent child) :=
  preRemove_result_sound hwf child parent

/-- §4.4 `insertBefore(node, child)` は pre-insert。 -/
theorem insertBefore_result_sound {s : DOMState} (hwf : WellFormed s.tree)
    (parent node : NodeId) (child : Option NodeId) :
    PreInsertResult s node parent child (insertBefore s parent node child) :=
  preInsert_result_sound hwf node parent child

/-- §4.2.3 "append" は child が null の pre-insert。 -/
theorem append_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node parent : NodeId) :
    PreInsertResult s node parent none (append s node parent) :=
  preInsert_result_sound hwf node parent none

/-- §4.4 `appendChild(node)` は append。 -/
theorem appendChild_result_sound {s : DOMState} (hwf : WellFormed s.tree) (parent node : NodeId) :
    PreInsertResult s node parent none (appendChild s parent node) :=
  append_result_sound hwf node parent

/-- §4.4 `replaceChild(node, child)` は replace。 -/
theorem replaceChild_result_sound {s : DOMState} (hsv : StructurallyValid s.tree)
    (parent node child : NodeId) :
    ReplaceResult s child node parent (replaceChild s parent node child) :=
  replace_result_sound hsv child node parent

/-! ## §4.2.6 `prepend()`・`append()`（node 一つ） -/

theorem prependNodes_single {s : DOMState} {this : NodeId} {td : NodeData}
    (ht : s.tree.get? this = some td) (n : NodeId) :
    prependNodes s this [.node n] =
      withState s (preInsert s n this (childrenOf s.tree this).head?) := by
  unfold prependNodes
  simp only [ht, Option.isNone_some, Bool.false_eq_true, if_false, convertNodesIntoNode_single,
    afterConvert_nil]

/-- `prepend(node)`：this の first child を reference にして pre-insert する。 -/
theorem prepend_single_result_sound {s : DOMState} (hwf : WellFormed s.tree) {this : NodeId}
    {td : NodeData} (ht : s.tree.get? this = some td) (n : NodeId) :
    ∃ r, prependNodes s this [.node n] = withState s r ∧
      PreInsertResult s n this (childrenOf s.tree this).head? r :=
  ⟨_, prependNodes_single ht n, preInsert_result_sound hwf n this _⟩

/-- `append(node)`：this に append する。 -/
theorem append_single_result_sound {s : DOMState} (hwf : WellFormed s.tree) {this : NodeId}
    {td : NodeData} (ht : s.tree.get? this = some td) (n : NodeId) :
    ∃ r, appendNodes s this [.node n] = withState s r ∧ PreInsertResult s n this none r :=
  ⟨_, appendNodes_single ht n, append_result_sound hwf n this⟩

/-! ## §4.4 `textContent`・`nodeValue` の setter -/

/--
§4.4 "string replace all"：文字列が空なら null で replace all、そうでなければ parent の node document の
Text を作って replace all する。
-/
def StringReplaceAllResult (s : DOMState) (string : String) (parent : NodeId)
    (r : Except DOMException DOMState) : Prop :=
  ∃ pd, s.tree.get? parent = some pd ∧ ∃ s', r = .ok s' ∧
    ((string = "" ∧ ReplaceAllSpec s none parent s') ∨
     (string ≠ "" ∧ ∃ n s₁,
        CreatesNode s n s₁ { kind := .text, ownerDocument := pd.ownerDocument, data := string } ∧
        ReplaceAllSpec s₁ (some n) parent s'))

/-- 木にある node に対する string replace all は例外を返さない。 -/
theorem stringReplaceAllResult_not_error {s : DOMState} {str : String} {parent : NodeId}
    {e : DOMException} : ¬ StringReplaceAllResult s str parent (.error e) := by
  rintro ⟨_, _, _, he, _⟩
  cases he

theorem stringReplaceAll_result_sound {s : DOMState} (hv : AdmissibleDOMState s) {parent : NodeId}
    {pd : NodeData} (hp : s.tree.get? parent = some pd) (string : String) :
    StringReplaceAllResult s string parent (stringReplaceAll s string parent) := by
  unfold stringReplaceAll
  rw [hp]
  simp only
  by_cases he : string.isEmpty = true
  · rw [if_pos he]
    obtain ⟨out, hout⟩ := replaceAll_isOk (node := none) (parent := parent) hv.wellFormed
      (fun n hn => by cases hn)
    exact ⟨pd, hp, out, hout, Or.inl ⟨by simpa using he, replaceAll_sound hv.wellFormed hout⟩⟩
  · rw [if_neg he]
    obtain ⟨dd, hdd, hk⟩ := hv.wellFormed.ownerDocument_is_document parent pd hp
    have hc : createTextNode s pd.ownerDocument string =
        .ok (withFresh s { kind := .text, ownerDocument := pd.ownerDocument, data := string }) := by
      simp [createTextNode, requireDocument, hdd, hk]
    obtain ⟨n, s₁, hcreate⟩ : ∃ n s₁, createTextNode s pd.ownerDocument string = .ok (n, s₁) :=
      ⟨_, _, hc⟩
    rw [hcreate]
    have hcn := createTextNode_creates hcreate
    have hv₁ := admissible_createTextNode hv hcreate
    have hp₁ : s₁.tree.get? parent = some pd := by
      rw [hcn.1.others parent (hcn.1.ne_of_mem hp)]; exact hp
    have hna : ¬ InclusiveAncestor s₁.tree n parent := by
      intro ha
      rcases ha with heq | ha
      · exact hcn.1.ne_of_mem hp heq.symm
      · obtain ⟨nd, hnd⟩ := exists_data_of_inclusiveAncestor hv.wellFormed
          (Or.inr (hcn.1.ancestor_of hcn.2.1.parent ha)) hp
        rw [hcn.1.fresh] at hnd
        cases hnd
    obtain ⟨out, hout⟩ := replaceAll_isOk (node := some n) (parent := parent) hv₁.wellFormed
      (fun n' hn' => by cases hn'; exact ⟨⟨pd, hp₁⟩, ⟨_, hcn.1.created⟩, hna⟩)
    exact ⟨pd, hp, out, hout, Or.inr ⟨by simpa using he,
      n, s₁, hcn, replaceAll_sound hv₁.wellFormed hout⟩⟩

/-- §4.4 "set text content"（`Attr` 以外）。 -/
def SetTextContentResult (s : DOMState) (n : NodeId) (value : String)
    (r : Except DOMException DOMState) : Prop :=
  ∃ d, s.tree.get? n = some d ∧
    (((d.kind = .element ∨ d.kind = .documentFragment) ∧ StringReplaceAllResult s value n r) ∨
     (d.kind.isCharacterData = true ∧ ReplaceDataResult s n 0 d.length value r) ∨
     ((d.kind = .document ∨ d.kind = .documentType) ∧ r = .ok s))

theorem setTextContent_result_sound {s : DOMState} (hv : AdmissibleDOMState s) {n : NodeId}
    {d : NodeData} (hn : s.tree.get? n = some d) (value : String) :
    SetTextContentResult s n value (setTextContent s n value) := by
  refine ⟨d, hn, ?_⟩
  unfold setTextContent
  rw [hn]
  simp only
  by_cases hef : (d.kind == .documentFragment || d.kind == .element) = true
  · rw [if_pos hef]
    have : d.kind = .element ∨ d.kind = .documentFragment := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hef; exact hef.symm
    exact Or.inl ⟨this, stringReplaceAll_result_sound hv hn value⟩
  · rw [if_neg hef]
    by_cases hc : d.kind.isCharacterData = true
    · rw [if_pos hc]
      exact Or.inr (Or.inl ⟨hc, replaceData_result_sound hv.wellFormed n 0 d.length value⟩)
    · rw [if_neg hc]
      refine Or.inr (Or.inr ⟨?_, rfl⟩)
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hef
      cases hk : d.kind <;> simp_all [NodeKind.isCharacterData]

/-- §4.4 `nodeValue` の setter（`Attr` 以外）。 -/
def SetNodeValueResult (s : DOMState) (n : NodeId) (value : String)
    (r : Except DOMException DOMState) : Prop :=
  ∃ d, s.tree.get? n = some d ∧
    ((d.kind.isCharacterData = true ∧ ReplaceDataResult s n 0 d.length value r) ∨
     (d.kind.isCharacterData = false ∧ r = .ok s))

theorem setNodeValue_result_sound {s : DOMState} (hwf : WellFormed s.tree) {n : NodeId}
    {d : NodeData} (hn : s.tree.get? n = some d) (value : String) :
    SetNodeValueResult s n value (setNodeValue s n value) := by
  refine ⟨d, hn, ?_⟩
  unfold setNodeValue
  rw [hn]
  simp only
  by_cases hc : d.kind.isCharacterData = true
  · rw [if_pos hc]; exact Or.inl ⟨hc, replaceData_result_sound hwf n 0 d.length value⟩
  · rw [if_neg hc]; exact Or.inr ⟨by simpa using hc, rfl⟩

/-! ## §4.5 `adoptNode()`・`importNode()` -/

/-- §4.5 `adoptNode(node)` は node を adopt して node を返す。 -/
theorem adoptNode_sound {s s' : DOMState} (hwf : WellFormed s.tree) {doc n m : NodeId}
    (h : adoptNode s doc n = .ok (m, s')) : m = n ∧ AdoptSpec s n doc s' := by
  unfold adoptNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next s₁ ha =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, adopt_sound hwf ha⟩

/-- §4.5 `importNode(node, options)` は、Document でない node を doc に clone する。 -/
theorem importNode_eq_clone {s : DOMState} {doc n : NodeId} {dd d : NodeData}
    (hdd : s.tree.get? doc = some dd) (hk : dd.kind = .document) (hn : s.tree.get? n = some d)
    (hnk : d.kind ≠ .document) (subtree : Bool) :
    importNode s doc n subtree = cloneNodeIn s n doc subtree := by
  unfold importNode
  simp [requireDocument, hdd, hk, hn, hnk]

/-! ## §4.2.6・§4.8 の selector の method -/

/-- §4.2.6 `querySelectorAll(selectors)` は scope-match の結果。 -/
theorem querySelectorAll_result_sound {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document ∨ d.kind = .documentFragment ∨ d.kind = .element) (selectors : String) :
    ScopeMatchResult t selectors node (querySelectorAll t selectors node) := by
  have hreq : requireParentNode t node = .ok () := by
    unfold requireParentNode
    rcases hk with hk | hk | hk <;> simp [hn, hk, NodeKind.canHaveChildren]
  unfold querySelectorAll
  rw [hreq]
  exact scopeMatch_result_sound hwf hav hn selectors

/-- §4.2.6 `querySelector(selectors)` は scope-match の結果の最初の element（tree order）。 -/
theorem querySelector_result_sound {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {node : NodeId} {d : NodeData} (hn : t.get? node = some d)
    (hk : d.kind = .document ∨ d.kind = .documentFragment ∨ d.kind = .element) (selectors : String) :
    (∃ e, querySelector t selectors node = .error e ∧ ScopeMatchResult t selectors node (.error e)) ∨
    (∃ l, querySelector t selectors node = .ok l.head? ∧ ScopeMatchResult t selectors node (.ok l)) := by
  have hreq : requireParentNode t node = .ok () := by
    unfold requireParentNode
    rcases hk with hk | hk | hk <;> simp [hn, hk, NodeKind.canHaveChildren]
  have hs := scopeMatch_result_sound hwf hav hn selectors
  unfold querySelector
  rw [hreq]
  simp only
  cases h : scopeMatch t selectors node with
  | error e => rw [h] at hs; exact Or.inl ⟨e, rfl, hs⟩
  | ok l => rw [h] at hs; exact Or.inr ⟨l, rfl, hs⟩

/-- §4.8 `matches(selectors)`：parse に失敗すれば SyntaxError、そうでなければ element が selector に当たるか。 -/
theorem matches_result_sound {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {e : NodeId} {d : NodeData} (he : t.get? e = some d) (hk : d.kind = .element)
    (selectors : String) :
    (parseSelector selectors = none ∧ matchesSelector t selectors e = .error .syntaxError) ∨
    ∃ sel b, parseSelector selectors = some sel ∧ matchesSelector t selectors e = .ok b ∧
      (b = true ↔ SelectorListMatches { tree := t, scope := some e } sel e) := by
  have hreq : requireElementNode t e = .ok () := by
    unfold requireElementNode; simp [he, hk]
  unfold matchesSelector
  rw [hreq]
  simp only
  cases hp : parseSelector selectors with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some sel =>
    exact Or.inr ⟨sel, _, rfl, rfl, matchSelList_iff_spec hwf hav rfl sel e⟩

/--
§4.8 `closest(selectors)`：parse に失敗すれば SyntaxError。そうでなければ、element から root へ向かって
最初に selector に当たる inclusive ancestor の element、無ければ null。
-/
def ClosestResult (t : Tree) (selectors : String) (e : NodeId)
    (r : Except DOMException (Option NodeId)) : Prop :=
  (parseSelector selectors = none ∧ r = .error .syntaxError) ∨
  ∃ sel, parseSelector selectors = some sel ∧
    let M := fun f => SelectorListMatches { tree := t, scope := some e } sel f
    ((r = .ok none ∧ ∀ f, InclusiveAncestor t f e → kindOf t f = some .element → ¬ M f) ∨
     (∃ a, r = .ok (some a) ∧ InclusiveAncestor t a e ∧ kindOf t a = some .element ∧ M a ∧
        ∀ f, InclusiveAncestor t f e → kindOf t f = some .element → M f → InclusiveAncestor t f a))

/-- `n` から root へ向かう inclusive ancestor の列では、後ろのものほど上にある。 -/
theorem ancestorChain_pairwise_anc {t : Tree} :
    ∀ (f : Nat) (n : NodeId), (ancestorChain t f n).Pairwise (fun a b => Ancestor t b a)
  | 0, _ => by simp [ancestorChain]
  | f + 1, n => by
    unfold ancestorChain
    split
    · exact List.Pairwise.nil
    · next p _ =>
      exact List.Pairwise.cons (fun x hx => mem_ancestorChain_ancestor f p x hx)
        (ancestorChain_pairwise_anc f p)

theorem isElementNode_iff (t : Tree) (n : NodeId) :
    isElementNode t n = true ↔ kindOf t n = some .element := by
  unfold isElementNode; simp

theorem closest_result_sound {t : Tree} (hwf : WellFormed t) (hav : AttributesValid t)
    {e : NodeId} {d : NodeData} (he : t.get? e = some d) (hk : d.kind = .element)
    (selectors : String) : ClosestResult t selectors e (closest t selectors e) := by
  have hreq : requireElementNode t e = .ok () := by
    unfold requireElementNode; simp [he, hk]
  cases hp : parseSelector selectors with
  | none =>
    refine Or.inl ⟨hp, ?_⟩
    unfold closest; rw [hreq, hp]
  | some sel =>
    refine Or.inr ⟨sel, hp, ?_⟩
    have hM : ∀ f, matchSelList { tree := t, scope := some e } sel f = true ↔
        SelectorListMatches { tree := t, scope := some e } sel f :=
      fun f => matchSelList_iff_spec hwf hav rfl sel f
    cases hc : closest t selectors e with
    | error x => rw [closest_eq hp hreq] at hc; cases hc
    | ok o =>
      cases o with
      | none =>
        refine Or.inl ⟨rfl, fun f hf hel hm => ?_⟩
        have := (closest_eq_none_iff hwf hp hreq).mp hc f hf ((isElementNode_iff t f).mpr hel)
        rw [(hM f).mpr hm] at this; cases this
      | some a =>
        obtain ⟨ha, hael, ham⟩ := closest_spec hwf hp hreq hc
        obtain ⟨nearer, farther, hsplit, hno⟩ := closest_first hp hreq hc
        refine Or.inr ⟨a, rfl, ha, (isElementNode_iff t a).mp hael, (hM a).mp ham,
          fun f hf hel hm => ?_⟩
        have hfm : f ∈ inclusiveAncestorElements t e :=
          (mem_inclusiveAncestorElements_iff hwf e f).mpr ⟨hf, (isElementNode_iff t f).mpr hel⟩
        have hsorted : (inclusiveAncestorElements t e).Pairwise (fun x y => Ancestor t y x) := by
          unfold inclusiveAncestorElements
          refine List.Pairwise.filter _ (List.Pairwise.cons ?_ (ancestorChain_pairwise_anc _ _))
          intro x hx
          exact (mem_ancestors_iff hwf e x).mp hx
        rw [hsplit] at hfm hsorted
        rcases List.mem_append.mp hfm with hn | hfa
        · have := hno f hn
          rw [(hM f).mpr hm] at this; cases this
        · rcases List.mem_cons.mp hfa with rfl | hfar
          · exact Or.inl rfl
          · exact Or.inr ((pairwise_split hsorted).2 f hfar)

/-! ## §4.9 `insertAdjacentElement()`・`insertAdjacentText()` -/

/-- pre-insert の結果を、入れた node を添えた結果として読む。 -/
def InsertedAs (node : NodeId) (R : Except DOMException DOMState → Prop)
    (r : Except DOMException (Option NodeId × DOMState)) : Prop :=
  (∀ e, r = .error e → R (.error e)) ∧ (∀ x s', r = .ok (x, s') → x = some node ∧ R (.ok s'))

/-- §4.9 "insert adjacent"。where は ASCII case-insensitive に読む。 -/
def InsertAdjacentResult (s : DOMState) (element : NodeId) (where_ : String) (node : NodeId)
    (r : Except DOMException (Option NodeId × DOMState)) : Prop :=
  let w := Infra.asciiLowercase where_
  (w ∉ ["beforebegin", "afterbegin", "beforeend", "afterend"] ∧ r = .error .syntaxError) ∨
  ((w = "beforebegin" ∨ w = "afterend") ∧ parentOf s.tree element = none ∧ r = .ok (none, s)) ∨
  (w = "beforebegin" ∧ ∃ p, parentOf s.tree element = some p ∧
    InsertedAs node (PreInsertResult s node p (some element)) r) ∨
  (w = "afterbegin" ∧ InsertedAs node (PreInsertResult s node element (childrenOf s.tree element).head?) r) ∨
  (w = "beforeend" ∧ InsertedAs node (PreInsertResult s node element none) r) ∨
  (w = "afterend" ∧ ∃ p, parentOf s.tree element = some p ∧
    InsertedAs node (PreInsertResult s node p (nextSibling s.tree element)) r)

theorem insertedAs_of {node : NodeId} {R : Except DOMException DOMState → Prop}
    {x : Except DOMException DOMState} (h : R x) : InsertedAs node R (insertAdjacent.inserted node x) := by
  cases x with
  | error e =>
    refine ⟨fun e' he => ?_, fun _ _ he => ?_⟩
    · simp [insertAdjacent.inserted] at he; subst he; exact h
    · simp [insertAdjacent.inserted] at he
  | ok s' =>
    refine ⟨fun _ he => ?_, fun x s'' he => ?_⟩
    · simp [insertAdjacent.inserted] at he
    · simp [insertAdjacent.inserted] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, h⟩

theorem adjacentPosition?_cases (w : String) :
    (adjacentPosition? w = some .beforebegin ∧ Infra.asciiLowercase w = "beforebegin") ∨
    (adjacentPosition? w = some .afterbegin ∧ Infra.asciiLowercase w = "afterbegin") ∨
    (adjacentPosition? w = some .beforeend ∧ Infra.asciiLowercase w = "beforeend") ∨
    (adjacentPosition? w = some .afterend ∧ Infra.asciiLowercase w = "afterend") ∨
    (adjacentPosition? w = none ∧
      Infra.asciiLowercase w ∉ ["beforebegin", "afterbegin", "beforeend", "afterend"]) := by
  unfold adjacentPosition?
  generalize Infra.asciiLowercase w = x
  split <;> simp_all

theorem insertAdjacent_result_sound {s : DOMState} (hwf : WellFormed s.tree)
    (element : NodeId) (where_ : String) (node : NodeId) :
    InsertAdjacentResult s element where_ node (insertAdjacent s element where_ node) := by
  unfold insertAdjacent InsertAdjacentResult
  rcases adjacentPosition?_cases where_ with ⟨h, hw⟩ | ⟨h, hw⟩ | ⟨h, hw⟩ | ⟨h, hw⟩ | ⟨h, hw⟩ <;>
    rw [h] <;> (try rw [hw])
  · cases hp : parentOf s.tree element with
    | none => exact Or.inr (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)
    | some p => exact Or.inr (Or.inr (Or.inl ⟨rfl, p, rfl,
        insertedAs_of (preInsert_result_sound hwf node p _)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, insertedAs_of (preInsert_result_sound hwf node element _)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, insertedAs_of (preInsert_result_sound hwf node element _)⟩))))
  · cases hp : parentOf s.tree element with
    | none => exact Or.inr (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)
    | some p => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, p, rfl,
        insertedAs_of (preInsert_result_sound hwf node p _)⟩))))
  · exact Or.inl ⟨hw, rfl⟩

/-! ## §4.9 attribute の lookup -/

/-- `getAttribute(qualifiedName)`：get an attribute by name の value。 -/
theorem getAttribute_spec (t : Tree) {e : NodeId} {d : NodeData} (he : t.get? e = some d)
    (qn : String) : ∃ a, AttrByName t d qn a ∧ getAttribute t e qn = a.map (·.value) :=
  ⟨_, getAttributeByName_spec t d qn, by unfold getAttribute; rw [he]⟩

/-- `getAttributeNS(namespace, localName)`：get an attribute by namespace and local name の value。 -/
theorem getAttributeNS_spec (t : Tree) {e : NodeId} {d : NodeData} (he : t.get? e = some d)
    (ns : Option String) (ln : String) :
    ∃ a, AttrByKey d ns ln a ∧ getAttributeNS t e ns ln = a.map (·.value) :=
  ⟨_, getAttributeByKey_spec d ns ln, by unfold getAttributeNS; rw [he]⟩

/-- `getAttributeNode(qualifiedName)`・`getNamedItem(qualifiedName)`。 -/
theorem getAttributeNode_spec (t : Tree) {e : NodeId} {d : NodeData} (he : t.get? e = some d)
    (hk : d.kind = .element) (qn : String) :
    ∃ a, AttrByName t d qn a ∧ getAttributeNode t e qn = .ok (a.map (·.id)) :=
  ⟨_, getAttributeByName_spec t d qn, by unfold getAttributeNode requireElement; simp [he, hk]⟩

/-- `getAttributeNodeNS(namespace, localName)`・`getNamedItemNS(namespace, localName)`。 -/
theorem getAttributeNodeNS_spec (t : Tree) {e : NodeId} {d : NodeData} (he : t.get? e = some d)
    (hk : d.kind = .element) (ns : Option String) (ln : String) :
    ∃ a, AttrByKey d ns ln a ∧ getAttributeNodeNS t e ns ln = .ok (a.map (·.id)) :=
  ⟨_, getAttributeByKey_spec d ns ln, by unfold getAttributeNodeNS requireElement; simp [he, hk]⟩

/-- §4.9 `removeNamedItemNS(namespace, localName)`。 -/
def RemoveNamedItemNSResult (s : DOMState) (element : NodeId) (ns : Option String) (ln : String) :
    Except DOMException (AttrId × DOMState) → Prop
  | .error e => ReceiverError s element e ∨ ∃ d, IsElementData s element d ∧
      AttrByKey d ns ln none ∧ e = .notFoundError
  | .ok (r, s') => ∃ d, IsElementData s element d ∧ ∃ a, AttrByKey d ns ln (some a) ∧
      r = a.id ∧ AttributeDetached s element d a s'

theorem removeNamedItemNS_result_sound {s : DOMState} (hwf : WellFormed s.tree)
    (hu : AttrIdsUnique s) (element : NodeId) (ns : Option String) (ln : String) :
    RemoveNamedItemNSResult s element ns ln (removeNamedItemNS s element ns ln) := by
  unfold removeNamedItemNS
  cases hreq : requireElement s.tree element with
  | error e => exact Or.inl (receiverError_of_requireElement hreq)
  | ok d =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    have hnd := hu.within element
    rw [attrIdsAt_of_get? hd] at hnd
    have hspec := getAttributeByKey_spec d ns ln
    cases hg : getAttributeByKey d ns ln with
    | none => rw [hg] at hspec; dsimp only; rw [hg]; exact Or.inr ⟨d, ⟨hd, hk⟩, hspec, rfl⟩
    | some a =>
      rw [hg] at hspec
      have hmem := mem_of_firstAttr hspec
      have hfind : d.attributes.find? (fun b => b.id == a.id) = some a := by
        cases hf : d.attributes.find? (fun b => b.id == a.id) with
        | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf a hmem)
        | some b =>
          have hid : b.id = a.id := by simpa using List.find?_some hf
          rw [eq_of_key_eq hnd (List.mem_of_find?_eq_some hf) hmem hid]
      dsimp only
      rw [hg]
      dsimp only
      unfold removeAttributeNode
      rw [hreq]
      dsimp only
      rw [hfind]
      exact ⟨d, ⟨hd, hk⟩, a, hspec, rfl, detachAttribute_spec hwf hd hmem hnd⟩

end Dom.Spec
