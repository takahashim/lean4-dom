import Dom.Attribute.Node
import Dom.Validity.Admissible

/-!
# `Attr` を node として渡す API も妥当性を保つ

`Dom/Validity/Attributes.lean` の `AttrOpResult` にそのまま乗る。
`detachedAttrs` は `AdmissibleDOMState` の成分ではないので、そこを触っても何も要らない。

新しいのは "replace an attribute" だけである。押し出す側と**同じ鍵**でしか置き換えないので、
attribute list の鍵は変わらず、`keysNodup` はそのまま残る。
-/

namespace Dom

open Dom.ListUtil

theorem AttributesOnly.trans {t t' t'' : Tree} (h₁ : AttributesOnly t t')
    (h₂ : AttributesOnly t' t'') : AttributesOnly t t'' := fun m => (h₂ m).trans (h₁ m)

theorem AttrOpResult.trans {s s' s'' : DOMState} (h₁ : AttrOpResult s s')
    (h₂ : AttrOpResult s' s'') : AttrOpResult s s'' where
  tree := h₁.tree.trans h₂.tree
  ranges := by rw [h₂.ranges, h₁.ranges]
  iterators := by rw [h₂.iterators, h₁.iterators]
  registrations := by rw [h₂.registrations, h₁.registrations]
  observersLength := by rw [h₂.observersLength, h₁.observersLength]
  attributes := fun h => h₂.attributes (h₁.attributes h)

/-- detach された list を触っても木も live object も変わらない。 -/
theorem attrOpResult_removeDetached (s : DOMState) (aid : AttrId) :
    AttrOpResult s (removeDetached s aid) :=
  ⟨AttributesOnly.refl _, rfl, rfl, rfl, rfl, id⟩

/-- `createAttribute` は detach された list に足すだけである。 -/
theorem attrOpResult_createAttributeIn (s : DOMState) (ns pfx : Option String) (ln : String) :
    AttrOpResult s (createAttributeIn s ns pfx ln).2 :=
  ⟨AttributesOnly.refl _, rfl, rfl, rfl, rfl, id⟩

/-! ## "replace an attribute" -/

@[simp] theorem replaceAttributeWith_tree (s : DOMState) (element : NodeId) (d : NodeData)
    (old new : Attr) : (replaceAttributeWith s element d old new).tree =
      setAttributes s.tree element d
        (updateFirst (fun b => b.key == old.key) (fun _ => new) d.attributes) := by
  unfold replaceAttributeWith; simp

@[simp] theorem replaceAttributeWith_ranges (s : DOMState) (element : NodeId) (d : NodeData)
    (old new : Attr) : (replaceAttributeWith s element d old new).ranges = s.ranges := by
  unfold replaceAttributeWith; simp

@[simp] theorem replaceAttributeWith_iterators (s : DOMState) (element : NodeId) (d : NodeData)
    (old new : Attr) : (replaceAttributeWith s element d old new).iterators = s.iterators := by
  unfold replaceAttributeWith; simp

@[simp] theorem replaceAttributeWith_registrations (s : DOMState) (element : NodeId)
    (d : NodeData) (old new : Attr) :
    (replaceAttributeWith s element d old new).registrations = s.registrations := by
  unfold replaceAttributeWith; simp

@[simp] theorem replaceAttributeWith_observers_length (s : DOMState) (element : NodeId)
    (d : NodeData) (old new : Attr) :
    (replaceAttributeWith s element d old new).observers.length = s.observers.length := by
  unfold replaceAttributeWith; simp

/-- 同じ鍵で置き換えるなら、attribute list の妥当性は保たれる。 -/
theorem attributesValid_replace {t : Tree} {n : NodeId} {d : NodeData} {old new : Attr}
    (hd : t.get? n = some d) (h : AttributesValid t) (hk : d.kind = .element)
    (hkey : new.key = old.key) (hpfx : new.prefix.isSome → new.namespace.isSome) :
    AttributesValid (setAttributes t n d
      (updateFirst (fun b => b.key == old.key) (fun _ => new) d.attributes)) := by
  refine attributesValid_setAttributes hd h hk ?_ ?_
  · rw [map_updateFirst_of_pred (p := fun b => b.key == old.key) (f := fun _ => new)
      (g := Attr.key) (fun b hb => by
        have : b.key = old.key := by simpa using hb
        rw [this, hkey])]
    exact h.keysNodup n d hd
  · intro b hb
    rcases mem_updateFirst hb with hb' | ⟨b₀, hb₀, rfl⟩
    · exact h.prefixHasNamespace n d hd b hb'
    · exact hpfx

theorem attrOpResult_replace {s : DOMState} {element : NodeId} {d : NodeData} {old new : Attr}
    (hd : s.tree.get? element = some d) (hk : d.kind = .element)
    (hkey : new.key = old.key) (hpfx : new.prefix.isSome → new.namespace.isSome) :
    AttrOpResult s (replaceAttributeWith s element d old new) :=
  ⟨by rw [replaceAttributeWith_tree]; exact attributesOnly_setAttributes hd _,
    replaceAttributeWith_ranges .., replaceAttributeWith_iterators ..,
    replaceAttributeWith_registrations .., replaceAttributeWith_observers_length ..,
    fun h => by rw [replaceAttributeWith_tree]; exact attributesValid_replace hd h hk hkey hpfx⟩

/-- 鍵で引いた attribute の鍵は、引いた鍵そのものである。 -/
theorem getAttributeByKey_key {d : NodeData} {ns : Option String} {ln : String} {old : Attr}
    (h : getAttributeByKey d ns ln = some old) : old.key = (normalizeNamespace ns, ln) := by
  unfold getAttributeByKey at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  simp [Attr.key, hp.1, hp.2]

/-! ## "remove an attribute"（返す側） -/

@[simp] theorem detachAttribute_tree (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) :
    (detachAttribute s element d a).tree =
      setAttributes s.tree element d (eraseFirst (fun b => b.id == a.id) d.attributes) := by
  unfold detachAttribute; simp

@[simp] theorem detachAttribute_ranges (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (detachAttribute s element d a).ranges = s.ranges := by
  unfold detachAttribute; simp

@[simp] theorem detachAttribute_iterators (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (detachAttribute s element d a).iterators = s.iterators := by
  unfold detachAttribute; simp

@[simp] theorem detachAttribute_registrations (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (detachAttribute s element d a).registrations = s.registrations := by
  unfold detachAttribute; simp

@[simp] theorem detachAttribute_observers_length (s : DOMState) (element : NodeId)
    (d : NodeData) (a : Attr) :
    (detachAttribute s element d a).observers.length = s.observers.length := by
  unfold detachAttribute; simp

theorem attrOpResult_detach {s : DOMState} {element : NodeId} {d : NodeData} {a : Attr}
    (hd : s.tree.get? element = some d) (hk : d.kind = .element) :
    AttrOpResult s (detachAttribute s element d a) :=
  ⟨by rw [detachAttribute_tree]; exact attributesOnly_setAttributes hd _,
    detachAttribute_ranges .., detachAttribute_iterators ..,
    detachAttribute_registrations .., detachAttribute_observers_length ..,
    fun h => by rw [detachAttribute_tree]; exact attributesValid_erase hd h hk⟩

/-! ## 各 API -/

theorem requireElement_ok {t : Tree} {element : NodeId} {d : NodeData}
    (h : requireElement t element = .ok d) : t.get? element = some d ∧ d.kind = .element := by
  unfold requireElement at h
  split at h
  · simp at h
  · next d' hd' =>
    split at h
    · simp at h
    · next hk =>
      cases h
      exact ⟨hd', by simpa using hk⟩

theorem attrOpResult_createAttribute {s s' : DOMState} {doc : NodeId} {ln : String}
    {aid : AttrId} (hr : createAttribute s doc ln = .ok (aid, s')) : AttrOpResult s s' := by
  unfold createAttribute at hr
  split at hr
  · simp at hr
  · next dd hreq =>
    split at hr
    · simp at hr
    · have he : (createAttributeIn s none none _).2 = s' := congrArg Prod.snd (Except.ok.inj hr)
      rw [← he]
      exact attrOpResult_createAttributeIn ..

theorem attrOpResult_createAttributeNS {s s' : DOMState} {doc : NodeId} {ns : Option String}
    {qn : String} {aid : AttrId} (hr : createAttributeNS s doc ns qn = .ok (aid, s')) :
    AttrOpResult s s' := by
  unfold createAttributeNS at hr
  split at hr
  · simp at hr
  · next dd hreq =>
    cases hval : validateAndExtractAttribute ns qn with
    | error e => rw [hval] at hr; simp at hr
    | ok r =>
      rw [hval] at hr
      have he : (createAttributeIn s r.1 r.2.1 r.2.2).2 = s' :=
        congrArg Prod.snd (Except.ok.inj hr)
      rw [← he]
      exact attrOpResult_createAttributeIn ..

theorem attrOpResult_setAttributeNode {s s' : DOMState} {element : NodeId} {aid : AttrId}
    {ret : Option AttrId} (h : AttributesValid s.tree)
    (hr : setAttributeNode s element aid = .ok (ret, s')) : AttrOpResult s s' := by
  unfold setAttributeNode at hr
  split at hr
  · simp at hr
  · next d hreq =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    split at hr
    · simp at hr
    · next a₀ owner hfind =>
      split at hr
      · simp at hr
      · split at hr
        · next old hold =>
          split at hr
          · have he : s = s' := congrArg Prod.snd (Except.ok.inj hr)
            rw [← he]
            exact AttrOpResult.refl s
          · have he : replaceAttributeWith (removeDetached s aid) element d old
                a₀.normalized = s' := congrArg Prod.snd (Except.ok.inj hr)
            rw [← he]
            refine (attrOpResult_removeDetached s aid).trans
              (attrOpResult_replace (by simpa using hd) hk ?_ (Attr.normalized_prefixHasNamespace _))
            -- 同じ鍵である。`old` は `a` の鍵で引いたものである。
            rw [Attr.normalized_key, getAttributeByKey_key hold]
            simp
        · next hnone =>
          have he : appendAttribute (removeDetached s aid) element d a₀.normalized = s' :=
            congrArg Prod.snd (Except.ok.inj hr)
          rw [← he]
          refine (attrOpResult_removeDetached s aid).trans
            (attrOpResult_append (by simpa using hd) hk ?_
              (Attr.normalized_prefixHasNamespace _))
          intro _
          have := key_not_mem_of_getAttributeByKey_none hnone
          simpa using this

theorem attrOpResult_removeAttributeNode {s s' : DOMState} {element : NodeId} {aid ret : AttrId}
    (hr : removeAttributeNode s element aid = .ok (ret, s')) : AttrOpResult s s' := by
  unfold removeAttributeNode at hr
  split at hr
  · simp at hr
  · next d hreq =>
    obtain ⟨hd, hk⟩ := requireElement_ok hreq
    split at hr
    · simp at hr
    · next a ha =>
      have he : detachAttribute s element d a = s' := congrArg Prod.snd (Except.ok.inj hr)
      rw [← he]
      exact attrOpResult_detach hd hk

theorem attrOpResult_removeNamedItem {s s' : DOMState} {element : NodeId} {qn : String}
    {ret : AttrId} (hr : removeNamedItem s element qn = .ok (ret, s')) : AttrOpResult s s' := by
  unfold removeNamedItem at hr
  split at hr
  · simp at hr
  · next d hreq =>
    split at hr
    · simp at hr
    · next a ha => exact attrOpResult_removeAttributeNode hr

/-! ## admissibility -/

theorem admissible_createAttribute {s s' : DOMState} {doc : NodeId} {ln : String} {aid : AttrId}
    (h : AdmissibleDOMState s) (hr : createAttribute s doc ln = .ok (aid, s')) :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_createAttribute hr)

theorem admissible_createAttributeNS {s s' : DOMState} {doc : NodeId} {ns : Option String}
    {qn : String} {aid : AttrId} (h : AdmissibleDOMState s)
    (hr : createAttributeNS s doc ns qn = .ok (aid, s')) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_createAttributeNS hr)

theorem admissible_setAttributeNode {s s' : DOMState} {element : NodeId} {aid : AttrId}
    {ret : Option AttrId} (h : AdmissibleDOMState s)
    (hr : setAttributeNode s element aid = .ok (ret, s')) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setAttributeNode h.attributes hr)

theorem admissible_removeAttributeNode {s s' : DOMState} {element : NodeId} {aid ret : AttrId}
    (h : AdmissibleDOMState s) (hr : removeAttributeNode s element aid = .ok (ret, s')) :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_removeAttributeNode hr)

theorem admissible_removeNamedItem {s s' : DOMState} {element : NodeId} {qn : String}
    {ret : AttrId} (h : AdmissibleDOMState s) (hr : removeNamedItem s element qn = .ok (ret, s')) :
    AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_removeNamedItem hr)

end Dom
