import Dom.Properties.Create
import Dom.Properties.Algorithms
import Dom.Validity.State

/-!
# node を作っても妥当性は保たれる

作る algorithm はどれも「detach された node を一つ足す」だけなので、
`AdmissibleDOMState` の七成分はどれも壊れない。要る条件は `FreshNodeData` にまとめてある。
-/

namespace Dom

/--
新しく作る node の data が満たすこと。

parent も children も持たず、attribute も持たず、Document ではなく、
node document は Document である。§4.5 の factory はどれもこの形の node を作る。
-/
structure FreshNodeData (t : Tree) (d : NodeData) : Prop where
  parent : d.parent = none
  children : d.children = []
  attributes : d.attributes = []
  notDocument : d.kind ≠ .document
  ownerIsDocument : IsDocument t d.ownerDocument

/-- list の `any` は、要素ごとに述語が一致すれば同じ値である。 -/
theorem any_congr {α : Type _} : ∀ (l : List α) {p q : α → Bool},
    (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _, _, _ => rfl
  | x :: rest, p, q, h => by
    simp only [List.any_cons, h x (List.mem_cons_self ..)]
    rw [any_congr rest fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Document の children とその kind が同じなら、`DocumentChildrenOk` も同じである。 -/
theorem documentChildrenOk_congr_of_children {t t' : Tree} {doc : NodeId}
    (hch : childrenOf t' doc = childrenOf t doc)
    (hkind : ∀ c ∈ childrenOf t doc, kindOf t' c = kindOf t c)
    (h : DocumentChildrenOk t doc) : DocumentChildrenOk t' doc := by
  have hfil : ∀ p q : NodeId → Bool, (∀ c ∈ childrenOf t doc, p c = q c) →
      (childrenOf t' doc).filter p = (childrenOf t doc).filter q := by
    intro p q hpq; rw [hch]; exact List.filter_congr hpq
  have he : elementChildren t' doc = elementChildren t doc :=
    hfil _ _ fun c hc => by simp [hkind c hc]
  have hdt : doctypeChildren t' doc = doctypeChildren t doc :=
    hfil _ _ fun c hc => by simp [hkind c hc]
  have htx : textChildren t' doc = textChildren t doc :=
    hfil _ _ fun c hc => by simp [hkind c hc]
  have hdf : ∀ e, doctypeFollows t' doc e = doctypeFollows t doc e := by
    intro e
    unfold doctypeFollows
    rw [hch]
    cases hs : ListUtil.splitAt? (childrenOf t doc) e with
    | none => rfl
    | some pr =>
      obtain ⟨u, v⟩ := pr
      refine any_congr v fun x hx => ?_
      have hmem : x ∈ childrenOf t doc := by
        rw [ListUtil.splitAt?_eq_some hs]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
      simp [hkind x hmem]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [he]; exact h1, by rw [hdt]; exact h2, by rw [htx]; exact h3,
    by rw [he]; intro x hx; rw [hdf]; exact h4 x hx⟩

namespace AddsNode

variable {s s' : DOMState} {n : NodeId} {d : NodeData}

/-- 木にあった node を、作った後の木でも引ける。 -/
theorem get?_of (h : AddsNode s.tree s'.tree n d) {m : NodeId} {md : NodeData}
    (hm : s.tree.get? m = some md) : s'.tree.get? m = some md := by
  rw [h.others m (h.ne_of_mem hm)]; exact hm

/-- 作った後の木で引けたなら、作った node か、もともと居た node である。 -/
theorem get?_cases (h : AddsNode s.tree s'.tree n d) {m : NodeId} {md : NodeData}
    (hm : s'.tree.get? m = some md) : (m = n ∧ md = d) ∨ s.tree.get? m = some md := by
  by_cases hmn : m = n
  · subst hmn
    rw [h.created] at hm
    exact Or.inl ⟨rfl, (Option.some.inj hm).symm⟩
  · rw [h.others m hmn] at hm
    exact Or.inr hm

theorem structurallyValid (h : AddsNode s.tree s'.tree n d) (hd : FreshNodeData s.tree d)
    (hv : StructurallyValid s.tree) : StructurallyValid s'.tree := by
  have hwf := hv.wellFormed
  have hpn : ∀ p pd, s'.tree.get? p = some pd → p ≠ n → s.tree.get? p = some pd := by
    intro p pd hpd hp; rw [← h.others p hp]; exact hpd
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- parent_child
    intro p pd hpd c hc
    have hcm : c ∈ childrenOf s'.tree p := by rw [childrenOf_eq hpd]; exact hc
    have hne : p ≠ n := by
      intro he; rw [he, h.childrenOf_self hd.children] at hcm; simp at hcm
    rw [h.childrenOf_other hne] at hcm
    obtain ⟨cd, hcd, hcdp⟩ := hwf.parent_child p pd (hpn p pd hpd hne) c
      (by rw [← childrenOf_eq (hpn p pd hpd hne)]; exact hcm)
    exact ⟨cd, h.get?_of hcd, hcdp⟩
  · -- child_parent
    intro c cd p hcd hcdp
    rcases h.get?_cases hcd with ⟨rfl, rfl⟩ | hcd'
    · rw [hd.parent] at hcdp; simp at hcdp
    · obtain ⟨pd, hpd, hmem⟩ := hwf.child_parent c cd p hcd' hcdp
      exact ⟨pd, h.get?_of hpd, hmem⟩
  · -- children_nodup
    intro m md hmd
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · rw [hd.children]; simp
    · exact hwf.children_nodup m md hmd'
  · -- acyclic
    exact fun m hm => hwf.acyclic m (h.ancestor_of hwf hd.children hd.parent hm)
  · -- ownerDocument_is_document
    intro m md hmd
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · obtain ⟨dd, hdd, hk⟩ := hd.ownerIsDocument
      exact ⟨dd, h.get?_of hdd, hk⟩
    · obtain ⟨dd, hdd, hk⟩ := hwf.ownerDocument_is_document m md hmd'
      exact ⟨dd, h.get?_of hdd, hk⟩
  · -- documentHasNoParent
    intro m md hmd hk
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · exact absurd hk hd.notDocument
    · exact hv.documentHasNoParent m md hmd' hk
  · -- fragmentHasNoParent
    intro m md hmd hk
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · exact hd.parent
    · exact hv.fragmentHasNoParent m md hmd' hk
  · -- childrenOnlyUnderContainers
    intro m md hmd hc
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · exact absurd hd.children hc
    · exact hv.childrenOnlyUnderContainers m md hmd' hc
  · -- doctypeParentIsDocument
    intro m md hmd hk p hp pd hpd
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · rw [hd.parent] at hp; simp at hp
    · rcases h.get?_cases hpd with ⟨rfl, rfl⟩ | hpd'
      · exfalso
        obtain ⟨pd₀, hpd₀, -⟩ := hwf.child_parent m md _ hmd' hp
        rw [h.fresh] at hpd₀; simp at hpd₀
      · exact hv.doctypeParentIsDocument m md hmd' hk p hp pd hpd'

theorem nodeDocumentsValid (h : AddsNode s.tree s'.tree n d) (hd : FreshNodeData s.tree d)
    (hwf : WellFormed s.tree) (hv : NodeDocumentsValid s.tree) :
    NodeDocumentsValid s'.tree := by
  refine ⟨?_, ?_⟩
  · intro m md hmd hk
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · exact absurd hk hd.notDocument
    · exact hv.documentIsOwnNodeDocument m md hmd' hk
  · intro c p hp
    have hcn : c ≠ n := by
      intro he; rw [he, h.parentOf_self hd.parent] at hp; simp at hp
    rw [h.parentOf_other hcn] at hp
    obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
    obtain ⟨pd, hpd, -⟩ := hwf.child_parent c cd p hcd hcdp
    rw [h.ownerDocumentOf_other hcn, h.ownerDocumentOf_other (h.ne_of_mem hpd)]
    exact hv.treeEdgePreservesNodeDocument c p hp

theorem documentTreesValid (h : AddsNode s.tree s'.tree n d) (hd : FreshNodeData s.tree d)
    (hwf : WellFormed s.tree) (hv : DocumentTreesValid s.tree) :
    DocumentTreesValid s'.tree := by
  refine ⟨?_⟩
  intro doc dd hdd hk
  rcases h.get?_cases hdd with ⟨rfl, rfl⟩ | hdd'
  · exact absurd hk hd.notDocument
  · -- Document の children も、その kind も変わらない。
    have hne : doc ≠ n := h.ne_of_mem hdd'
    have hch : childrenOf s'.tree doc = childrenOf s.tree doc := h.childrenOf_other hne
    have hkind : ∀ c ∈ childrenOf s.tree doc, kindOf s'.tree c = kindOf s.tree c := by
      intro c hc
      obtain ⟨cd, hcd, -⟩ := parentOf_eq_some (parentOf_of_mem_childrenOf hwf hc)
      simp [kindOf, h.others c (h.ne_of_mem hcd)]
    exact documentChildrenOk_congr_of_children hch hkind (hv.documentChildren doc dd hdd' hk)

theorem rangeEndpointsValid (h : AddsNode s.tree s'.tree n d) (hr : s'.ranges = s.ranges)
    (hv : RangeEndpointsValid s) : RangeEndpointsValid s' := by
  intro r hrmem
  rw [hr] at hrmem
  obtain ⟨⟨sd, hsd, hso⟩, ⟨ed, hed, heo⟩⟩ := hv r hrmem
  exact ⟨⟨sd, h.get?_of hsd, hso⟩, ⟨ed, h.get?_of hed, heo⟩⟩

theorem iteratorsValid (h : AddsNode s.tree s'.tree n d) (hit : s'.iterators = s.iterators)
    (hv : IteratorsValid s) : IteratorsValid s' := by
  intro it hmem
  rw [hit] at hmem
  obtain ⟨⟨rd, hrd⟩, hdesc⟩ := hv it hmem
  refine ⟨⟨rd, h.get?_of hrd⟩, ?_⟩
  rcases hdesc with he | ha
  · exact Or.inl he
  · exact Or.inr (h.ancestor_to ha)

theorem observerRegistrationsValid (h : AddsNode s.tree s'.tree n d)
    (hreg : s'.registrations = s.registrations) (hobs : s'.observers = s.observers)
    (hv : ObserverRegistrationsValid s) : ObserverRegistrationsValid s' := by
  intro r hmem
  rw [hreg] at hmem
  obtain ⟨hlt, hnode⟩ := hv r hmem
  refine ⟨by rw [hobs]; exact hlt, ?_⟩
  obtain ⟨nd, hnd⟩ := Option.isSome_iff_exists.mp hnode
  rw [h.get?_of hnd]
  rfl

theorem attributesValid (h : AddsNode s.tree s'.tree n d) (hd : FreshNodeData s.tree d)
    (hv : AttributesValid s.tree) : AttributesValid s'.tree := by
  refine ⟨?_, ?_, ?_⟩
  · intro m md hmd hk
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · exact hd.attributes
    · exact hv.onlyElements m md hmd' hk
  · intro m md hmd
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · rw [hd.attributes]; simp
    · exact hv.keysNodup m md hmd'
  · intro m md hmd a ha
    rcases h.get?_cases hmd with ⟨rfl, rfl⟩ | hmd'
    · rw [hd.attributes] at ha; simp at ha
    · exact hv.prefixHasNamespace m md hmd' a ha

/-- **node を一つ足しても妥当性は保たれる。** -/
theorem admissible (h : AddsNode s.tree s'.tree n d) (hd : FreshNodeData s.tree d)
    (hr : s'.ranges = s.ranges) (hit : s'.iterators = s.iterators)
    (hreg : s'.registrations = s.registrations) (hobs : s'.observers = s.observers)
    (hv : AdmissibleDOMState s) : AdmissibleDOMState s' where
  structural := h.structurallyValid hd hv.structural
  nodeDocuments := h.nodeDocumentsValid hd hv.wellFormed hv.nodeDocuments
  documentTrees := h.documentTreesValid hd hv.wellFormed hv.documentTrees
  rangeEndpoints := h.rangeEndpointsValid hr hv.rangeEndpoints
  iterators := h.iteratorsValid hit hv.iterators
  observerRegistrations := h.observerRegistrationsValid hreg hobs hv.observerRegistrations
  attributes := h.attributesValid hd hv.attributes


end AddsNode

/-! ## 各 method -/

theorem requireDocument_ok {t : Tree} {doc : NodeId} {dd : NodeData}
    (h : requireDocument t doc = .ok dd) : t.get? doc = some dd ∧ dd.kind = .document := by
  unfold requireDocument at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · next hk =>
      cases h
      exact ⟨hd, by simpa using hk⟩
    · simp at h

/--
作った node が満たすこと。

`withFresh` が返す組はこの形になる。ここから妥当性の保存が出る。
-/
def CreatesNode (s : DOMState) (n : NodeId) (s' : DOMState) (d : NodeData) : Prop :=
  AddsNode s.tree s'.tree n d ∧ FreshNodeData s.tree d ∧
    s'.ranges = s.ranges ∧ s'.iterators = s.iterators ∧
    s'.registrations = s.registrations ∧ s'.observers = s.observers

theorem createsNode_withFresh {s : DOMState} {d : NodeData} (hd : FreshNodeData s.tree d) :
    CreatesNode s (withFresh s d).1 (withFresh s d).2 d :=
  ⟨withFresh_addsNode s d, hd, rfl, rfl, rfl, rfl⟩

/-- **作っても妥当性は保たれる。** -/
theorem admissible_createsNode {s s' : DOMState} {n : NodeId} {d : NodeData}
    (hv : AdmissibleDOMState s) (h : CreatesNode s n s' d) : AdmissibleDOMState s' :=
  h.1.admissible h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hv

/-- `withFresh` が返した組を、名前で受けた `n` と `s'` へ移す。 -/
theorem creates_of_withFresh {s s' : DOMState} {n : NodeId} {d : NodeData}
    (hd : FreshNodeData s.tree d) (h : withFresh s d = (n, s')) : CreatesNode s n s' d := by
  have h1 : (withFresh s d).1 = n := by rw [h]
  have h2 : (withFresh s d).2 = s' := by rw [h]
  rw [← h1, ← h2]
  exact createsNode_withFresh hd

theorem createTextNode_creates {s s' : DOMState} {doc n : NodeId} {data : String}
    (h : createTextNode s doc data = .ok (n, s')) :
    CreatesNode s n s' { kind := .text, ownerDocument := doc, data := data } := by
  unfold createTextNode at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    exact creates_of_withFresh ⟨rfl, rfl, rfl, by simp, ⟨dd, hdd, hk⟩⟩ (Except.ok.inj h)

theorem createComment_creates {s s' : DOMState} {doc n : NodeId} {data : String}
    (h : createComment s doc data = .ok (n, s')) :
    CreatesNode s n s' { kind := .comment, ownerDocument := doc, data := data } := by
  unfold createComment at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    exact creates_of_withFresh ⟨rfl, rfl, rfl, by simp, ⟨dd, hdd, hk⟩⟩ (Except.ok.inj h)

theorem createDocumentFragment_creates {s s' : DOMState} {doc n : NodeId}
    (h : createDocumentFragment s doc = .ok (n, s')) :
    CreatesNode s n s' { kind := .documentFragment, ownerDocument := doc } := by
  unfold createDocumentFragment at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    exact creates_of_withFresh ⟨rfl, rfl, rfl, by simp, ⟨dd, hdd, hk⟩⟩ (Except.ok.inj h)

theorem createElement_creates {s s' : DOMState} {doc n : NodeId} {localName : String}
    (h : createElement s doc localName = .ok (n, s')) :
    ∃ dd, s.tree.get? doc = some dd ∧ dd.kind = .document ∧
      CreatesNode s n s'
        { kind := .element, ownerDocument := doc,
          «namespace» := if dd.isHTMLDocument then some htmlNamespace else none,
          localName := if dd.isHTMLDocument then asciiLowercase localName else localName } := by
  unfold createElement at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    split at h
    · simp at h
    · exact ⟨dd, hdd, hk,
        creates_of_withFresh ⟨rfl, rfl, rfl, by simp, ⟨dd, hdd, hk⟩⟩ (Except.ok.inj h)⟩

theorem createElementNS_creates {s s' : DOMState} {doc n : NodeId}
    {«namespace» : Option String} {qualifiedName : String}
    (h : createElementNS s doc «namespace» qualifiedName = .ok (n, s')) :
    ∃ (ns₀ pfx₀ : Option String) (ln : String),
      validateAndExtractElement «namespace» qualifiedName = .ok (ns₀, pfx₀, ln) ∧
      CreatesNode s n s'
        { kind := .element, ownerDocument := doc, «namespace» := ns₀, «prefix» := pfx₀,
          localName := ln } := by
  unfold createElementNS at h
  split at h
  · simp at h
  · next dd hreq =>
    obtain ⟨hdd, hk⟩ := requireDocument_ok hreq
    cases hval : validateAndExtractElement «namespace» qualifiedName with
    | error e => rw [hval] at h; simp at h
    | ok r =>
      obtain ⟨ns₀, pfx₀, ln⟩ := r
      rw [hval] at h
      exact ⟨ns₀, pfx₀, ln, rfl,
        creates_of_withFresh ⟨rfl, rfl, rfl, by simp, ⟨dd, hdd, hk⟩⟩ (Except.ok.inj h)⟩

end Dom
