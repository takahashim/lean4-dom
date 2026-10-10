import Dom.Validity.Discard
import Dom.Validity.Admissible
import Dom.Validity.AttrIdsAttr

/-!
# 可変長の引数を取る method は、成功しても失敗しても状態を妥当に保つ

`prepend`・`append`・`replaceChildren`・`before`・`after`・`replaceWith`（`Dom/Mutation/Variadic.lean`）は、
失敗してもそれまでの変更を残しうるので、失敗にも状態を持たせてある。その状態も含めて、
admissibility と attribute の id の一意性が保たれることを示す。

部品はどれも既存の結果である。Text node と DocumentFragment を作ること（`admissible_createTextNode` ほか）、
pre-insert・replace・replace all（`admissible_preInsert` ほか）、参照されなくなった node を消すこと
（`admissible_discard`）。証明は、この部品で閉じている性質 `P` について一度だけ書き（`VariadicClosed`）、
admissibility と、それに id の一意性を加えたもの（`Good`）に当てる。
-/

namespace Dom

/-- `doc` が木にある Document であること。 -/
def IsDocumentIn (s : DOMState) (doc : NodeId) : Prop :=
  ∃ dd, s.tree.get? doc = some dd ∧ dd.kind = .document

/-- 可変長の method の部品で閉じている性質。 -/
structure VariadicClosed (P : DOMState → Prop) : Prop where
  text : ∀ {s : DOMState} {doc : NodeId} (data : String), P s → IsDocumentIn s doc →
    P (withFresh s { kind := .text, ownerDocument := doc, data := data }).2
  fragment : ∀ {s : DOMState} {doc : NodeId}, P s → IsDocumentIn s doc →
    P (withFresh s { kind := .documentFragment, ownerDocument := doc }).2
  preInsert : ∀ {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}, P s →
    preInsert s node parent child = .ok s' → P s'
  replace : ∀ {s s' : DOMState} {child node parent : NodeId}, P s →
    replace s child node parent = .ok s' → P s'
  replaceChildren : ∀ {s s' : DOMState} {parent : NodeId} {node : Option NodeId}, P s →
    replaceChildren s parent node = .ok s' → P s'
  discard : ∀ {s : DOMState} (n : NodeId), P s → P (discard s n)
  nodeDocument : ∀ {s : DOMState} {this : NodeId} {td : NodeData}, P s →
    s.tree.get? this = some td → IsDocumentIn s (nodeDocumentOf s this)

/-- 結果が成功でも失敗でも、その状態が `P` を満たすこと。 -/
def ResultHolds {α : Type} (P : DOMState → Prop) (good : α → Prop)
    (r : Except (DOMException × DOMState) α) : Prop :=
  (∀ a, r = .ok a → good a) ∧ (∀ e s', r = .error (e, s') → P s')

theorem withFresh_get?_of_some {s : DOMState} {m : NodeId} {md : NodeData} (h : s.tree.get? m = some md)
    (x : NodeData) : (withFresh s x).2.tree.get? m = some md := by
  have hne : m ≠ freshId s.tree := by
    intro he; rw [he, freshId_get?_eq_none] at h; cases h
  show (s.tree.insertNode (freshId s.tree) x).get? m = some md
  rw [get?_insertNode_ne _ hne]
  exact h

theorem isDocumentIn_withFresh {s : DOMState} {doc : NodeId} (h : IsDocumentIn s doc) (x : NodeData) :
    IsDocumentIn (withFresh s x).2 doc := by
  obtain ⟨dd, hdd, hk⟩ := h
  exact ⟨dd, withFresh_get?_of_some hdd x, hk⟩

theorem createTextNode_of_isDocumentIn {s : DOMState} {doc : NodeId} (h : IsDocumentIn s doc)
    (data : String) : createTextNode s doc data =
      .ok (withFresh s { kind := .text, ownerDocument := doc, data := data }) := by
  obtain ⟨dd, hdd, hk⟩ := h
  unfold createTextNode requireDocument
  simp [hdd, hk]

theorem createDocumentFragment_of_isDocumentIn {s : DOMState} {doc : NodeId} (h : IsDocumentIn s doc) :
    createDocumentFragment s doc =
      .ok (withFresh s { kind := .documentFragment, ownerDocument := doc }) := by
  obtain ⟨dd, hdd, hk⟩ := h
  unfold createDocumentFragment requireDocument
  simp [hdd, hk]

/-- 木にある node の node document は、木にある Document である。 -/
theorem isDocumentIn_nodeDocumentOf {s : DOMState} (hwf : WellFormed s.tree) {this : NodeId}
    {td : NodeData} (ht : s.tree.get? this = some td) : IsDocumentIn s (nodeDocumentOf s this) := by
  obtain ⟨dd, hdd, hk⟩ := hwf.ownerDocument_is_document this td ht
  refine ⟨dd, ?_, hk⟩
  simp only [nodeDocumentOf, ownerDocumentOf, ht, Option.map_some, Option.getD_some]
  exact hdd

section Generic

variable {P : DOMState → Prop} (hc : VariadicClosed P)
include hc

theorem closed_discardAll {s : DOMState} (h : P s) : ∀ ns, P (discardAll s ns) := by
  intro ns
  induction ns generalizing s with
  | nil => exact h
  | cons n rest ih => exact ih (hc.discard n h)

/-- step 1：Text node を作っても `P` で、`doc` は Document のままである。 -/
theorem closed_textsFor {doc : NodeId} :
    ∀ (items : List NodeOrString) {s : DOMState}, P s → IsDocumentIn s doc →
      P (textsFor s doc items).2.2 ∧ IsDocumentIn (textsFor s doc items).2.2 doc
  | [], _, h, hdoc => ⟨h, hdoc⟩
  | .node _ :: rest, s, h, hdoc => by
    simp only [textsFor]
    exact closed_textsFor rest h hdoc
  | .string d :: rest, s, h, hdoc => by
    simp only [textsFor]
    exact closed_textsFor rest (hc.text d h hdoc) (isDocumentIn_withFresh hdoc _)

/-- step 4：append を重ねても、成功でも失敗でも `P` である。 -/
theorem closed_appendAll {frag : NodeId} :
    ∀ (ns : List NodeId) {s : DOMState}, P s → ResultHolds P P (appendAll s frag ns)
  | [], s, h => ⟨fun a ha => (by cases ha; exact h), fun e s' ha => (by cases ha)⟩
  | n :: rest, s, h => by
    unfold appendAll
    split
    · exact ⟨fun a ha => (by cases ha), fun e' s' ha => (by cases ha; exact h)⟩
    · rename_i s₁ hs₁
      exact closed_appendAll rest (hc.preInsert h hs₁)

/-- **convert nodes into a node は、成功でも失敗でも `P` を保つ。** -/
theorem closed_convert {s : DOMState} {doc : NodeId} (h : P s) (hdoc : IsDocumentIn s doc)
    (items : List NodeOrString) :
    ResultHolds P (fun (r : NodeId × List NodeId × DOMState) => P r.2.2)
      (convertNodesIntoNode s items doc) := by
  obtain ⟨h₁, hdoc₁⟩ := closed_textsFor hc items h hdoc
  unfold convertNodesIntoNode
  generalize textsFor s doc items = r at h₁ hdoc₁
  obtain ⟨ns, created, s₁⟩ := r
  simp only at h₁ hdoc₁ ⊢
  split
  · exact ⟨fun a ha => (by cases ha; exact h₁), fun e s' ha => (by cases ha)⟩
  · have h₂ := hc.fragment h₁ hdoc₁
    have ha := closed_appendAll hc
      (frag := (withFresh s₁ { kind := .documentFragment, ownerDocument := doc }).1) ns h₂
    generalize appendAll _ _ ns = r at ha
    rcases r with ⟨e, s₃⟩ | s₃
    · exact ⟨fun a hq => (by cases hq),
        fun e' s' hq => (by cases hq; exact closed_discardAll hc (ha.2 e s₃ rfl) _)⟩
    · exact ⟨fun a hq => (by cases hq; exact ha.1 s₃ rfl), fun e' s' hq => (by cases hq)⟩

/-- 変換の後の手順が `P` を保てば、回収を含めて成功でも失敗でも `P` である。 -/
theorem closed_afterConvert {created : List NodeId} {s₁ : DOMState}
    {k : DOMState → Except DOMException DOMState} (h₁ : P s₁)
    (hk : ∀ s₂, k s₁ = .ok s₂ → P s₂) : ResultHolds P P (afterConvert created s₁ k) := by
  unfold afterConvert
  split
  · exact ⟨fun a ha => (by cases ha), fun e s' ha => (by cases ha; exact closed_discardAll hc h₁ _)⟩
  · rename_i s₂ hs₂
    exact ⟨fun a ha => (by cases ha; exact closed_discardAll hc (hk s₂ hs₂) _),
      fun e s' ha => (by cases ha)⟩

/-- 変換から後半の手順までの組み立て。 -/
theorem closed_convert_then {s : DOMState} (h : P s) {this : NodeId} {td : NodeData}
    (ht : s.tree.get? this = some td) (items : List NodeOrString)
    {k : NodeId → DOMState → Except DOMException DOMState}
    (hk : ∀ node s₁ s₂, P s₁ → k node s₁ = .ok s₂ → P s₂) :
    ResultHolds P P (match convertNodesIntoNode s items (nodeDocumentOf s this) with
      | .error p => .error p
      | .ok (node, created, s₁) => afterConvert created s₁ (k node)) := by
  have hcv := closed_convert hc h (hc.nodeDocument h ht) items
  generalize convertNodesIntoNode s items (nodeDocumentOf s this) = r at hcv
  rcases r with ⟨e, s'⟩ | ⟨node, created, s₁⟩
  · exact ⟨fun a ha => (by cases ha), fun e' s'' ha => (by cases ha; exact hcv.2 e s' rfl)⟩
  · exact closed_afterConvert hc (hcv.1 _ rfl) (fun s₂ hs₂ => hk node s₁ s₂ (hcv.1 _ rfl) hs₂)

omit hc in
/-- this が木にあること（ParentNode の method の guard を通った後）。 -/
private theorem exists_of_isNone_false {s : DOMState} {this : NodeId}
    (h : ¬ (s.tree.get? this).isNone = true) : ∃ td, s.tree.get? this = some td := by
  cases hq : s.tree.get? this with
  | none => rw [hq] at h; exact absurd rfl h
  | some td => exact ⟨td, rfl⟩

omit hc in
/-- parent があれば this は木にある。 -/
private theorem exists_of_parentOf {s : DOMState} {this p : NodeId} (hp : parentOf s.tree this = some p) :
    ∃ td, s.tree.get? this = some td := by
  obtain ⟨td, htd, -⟩ := parentOf_eq_some hp
  exact ⟨td, htd⟩

theorem closed_prependNodes {s : DOMState} (h : P s) (this : NodeId) (items : List NodeOrString) :
    ResultHolds P P (prependNodes s this items) := by
  unfold prependNodes
  split
  · exact ⟨fun a ha => (by cases ha), fun e s' ha => (by cases ha; exact h)⟩
  · rename_i hnone
    obtain ⟨td, ht⟩ := exists_of_isNone_false hnone
    exact closed_convert_then hc h ht items (fun _ _ _ h₁ hp => hc.preInsert h₁ hp)

theorem closed_appendNodes {s : DOMState} (h : P s) (this : NodeId) (items : List NodeOrString) :
    ResultHolds P P (appendNodes s this items) := by
  unfold appendNodes
  split
  · exact ⟨fun a ha => (by cases ha), fun e s' ha => (by cases ha; exact h)⟩
  · rename_i hnone
    obtain ⟨td, ht⟩ := exists_of_isNone_false hnone
    exact closed_convert_then hc h ht items (fun _ _ _ h₁ hp => hc.preInsert h₁ hp)

theorem closed_replaceChildrenNodes {s : DOMState} (h : P s) (this : NodeId)
    (items : List NodeOrString) : ResultHolds P P (replaceChildrenNodes s this items) := by
  unfold replaceChildrenNodes
  split
  · exact ⟨fun a ha => (by cases ha), fun e s' ha => (by cases ha; exact h)⟩
  · rename_i hnone
    obtain ⟨td, ht⟩ := exists_of_isNone_false hnone
    exact closed_convert_then hc h ht items (fun _ _ _ h₁ hp => hc.replaceChildren h₁ hp)

theorem closed_beforeNodes {s : DOMState} (h : P s) (this : NodeId) (items : List NodeOrString) :
    ResultHolds P P (beforeNodes s this items) := by
  unfold beforeNodes
  split
  · exact ⟨fun a ha => (by cases ha; exact h), fun e s' ha => (by cases ha)⟩
  · rename_i parent hp
    obtain ⟨td, ht⟩ := exists_of_parentOf hp
    exact closed_convert_then hc h ht items (fun _ _ _ h₁ hq => hc.preInsert h₁ hq)

theorem closed_afterNodes {s : DOMState} (h : P s) (this : NodeId) (items : List NodeOrString) :
    ResultHolds P P (afterNodes s this items) := by
  unfold afterNodes
  split
  · exact ⟨fun a ha => (by cases ha; exact h), fun e s' ha => (by cases ha)⟩
  · rename_i parent hp
    obtain ⟨td, ht⟩ := exists_of_parentOf hp
    exact closed_convert_then hc h ht items (fun _ _ _ h₁ hq => hc.preInsert h₁ hq)

theorem closed_replaceWithNodes {s : DOMState} (h : P s) (this : NodeId) (items : List NodeOrString) :
    ResultHolds P P (replaceWithNodes s this items) := by
  unfold replaceWithNodes
  split
  · exact ⟨fun a ha => (by cases ha; exact h), fun e s' ha => (by cases ha)⟩
  · rename_i parent hp
    obtain ⟨td, ht⟩ := exists_of_parentOf hp
    refine closed_convert_then hc h ht items (fun node s₁ s₂ h₁ hq => ?_)
    split at hq
    · exact hc.replace h₁ hq
    · exact hc.preInsert h₁ hq

end Generic

/-! ## admissibility と、attribute の id の一意性 -/

/-- **admissibility は、可変長の method の部品で閉じている。** -/
theorem admissible_variadicClosed : VariadicClosed AdmissibleDOMState where
  text data h hdoc := admissible_createTextNode h (createTextNode_of_isDocumentIn hdoc data)
  fragment h hdoc := admissible_createDocumentFragment h (createDocumentFragment_of_isDocumentIn hdoc)
  preInsert h hp := admissible_preInsert h hp
  replace h hp := admissible_replace h hp
  replaceChildren h hp := admissible_replaceChildren h hp
  discard n h := admissible_discard h n
  nodeDocument h ht := isDocumentIn_nodeDocumentOf h.wellFormed ht

/-- admissible で、attribute の id も一意な状態。 -/
def Good (s : DOMState) : Prop := AdmissibleDOMState s ∧ AttrIdsUnique s

/-- **admissibility と attribute の id の一意性の組も、可変長の method の部品で閉じている。** -/
theorem good_variadicClosed : VariadicClosed Good where
  text data h hdoc := ⟨admissible_createTextNode h.1 (createTextNode_of_isDocumentIn hdoc data),
    unique_createTextNode h.2 (createTextNode_of_isDocumentIn hdoc data)⟩
  fragment h hdoc :=
    ⟨admissible_createDocumentFragment h.1 (createDocumentFragment_of_isDocumentIn hdoc),
      unique_createDocumentFragment h.2 (createDocumentFragment_of_isDocumentIn hdoc)⟩
  preInsert h hp := ⟨admissible_preInsert h.1 hp, (attrFrame_insertBefore hp).unique h.2⟩
  replace h hp := ⟨admissible_replace h.1 hp, (attrFrame_replaceChild hp).unique h.2⟩
  replaceChildren h hp := ⟨admissible_replaceChildren h.1 hp, (attrFrame_replaceChildren hp).unique h.2⟩
  discard n h := ⟨admissible_discard h.1 n, (attrFrame_discard _ n).unique h.2⟩
  nodeDocument h ht := isDocumentIn_nodeDocumentOf h.1.wellFormed ht

end Dom
