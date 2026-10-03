import Dom.Validity.AttrIds
import Dom.Validity.Attributes
import Dom.Attribute.Node
import Dom.Attribute.AsNode
import Dom.Spec.AttributeSound
import Dom.Attribute.Reflect
import Dom.Mutation.Clone
import Dom.Mutation.Import

/-!
# attribute を作る・動かす操作は id の一意性を保つ

新しい attribute の id は `freshStateAttrId`（状態にある id の最大 + 1）で、木にも
detach された list にも無い。既存の `Attr` を動かす操作は、元の場所から外してから付ける。
どちらも「一つの element の attribute list と detach された list だけが変わる」形なので、
その形の一般補題（`AttrIdsUnique.of_change`）に帰着させる。
-/

namespace Dom

open Dom.ListUtil

/-! ## 一般補題 -/

theorem attrIdsAt_eq (t : Tree) (m : NodeId) : attrIdsAt t m = (attrSigAt t m).map Prod.fst := rfl

/--
**一つの element の attribute list と detach された list だけが変わるとき。**

新しい element の id の列（`L` の第一成分）と detach された id の列 `D` が、それぞれ重複せず、
互いに重ならず、他の element の id とも重ならず、新しい namespace が正規化されていれば、
一意性は保たれる。
-/
theorem AttrIdsUnique.of_change {s s' : DOMState} (hu : AttrIdsUnique s) (n : NodeId)
    (L : List (AttrId × Option String)) (D : List AttrId)
    (hids : ∀ m, attrSigAt s'.tree m = if m = n then L else attrSigAt s.tree m)
    (hD : s'.detachedAttrs.map (·.id) = D)
    (hL : (L.map Prod.fst).Nodup) (hDn : D.Nodup) (hLD : ∀ i ∈ L.map Prod.fst, i ∉ D)
    (hLo : ∀ m, m ≠ n → ∀ i ∈ L.map Prod.fst, i ∉ attrIdsAt s.tree m)
    (hDo : ∀ m, m ≠ n → ∀ i ∈ attrIdsAt s.tree m, i ∉ D)
    (hLn : ∀ p ∈ L, normalizeNamespace p.2 = p.2)
    (hDN : ∀ p ∈ s'.detachedAttrs.map detachedSig, AttrNormalForm p.2) : AttrIdsUnique s' := by
  have hids' : ∀ m, attrIdsAt s'.tree m =
      if m = n then L.map Prod.fst else attrIdsAt s.tree m := by
    intro m; rw [attrIdsAt_eq, hids]; split <;> rfl
  refine ⟨fun m => ?_, fun m m' hne i hi => ?_, by rw [hD]; exact hDn, fun m i hi => ?_,
    fun m p hp => ?_, hDN⟩
  · rw [hids']; split
    · exact hL
    · exact hu.within m
  · rw [hids'] at hi ⊢
    by_cases hm : m = n
    · rw [if_pos hm] at hi
      rw [if_neg (fun h => hne (hm.trans h.symm))]
      exact hLo m' (fun h => hne (hm.trans h.symm)) i hi
    · rw [if_neg hm] at hi
      split
      · intro hiL; exact hLo m hm i hiL hi
      · exact hu.across m m' hne i hi
  · rw [hids'] at hi
    rw [hD]
    split at hi
    · exact hLD i hi
    · next hm => exact hDo m hm i hi
  · rw [hids] at hp
    split at hp
    · exact hLn p hp
    · exact hu.normalized m p hp

/-- 木を変えず、detach された list だけを変えるとき。 -/
theorem AttrIdsUnique.of_detached {s s' : DOMState} (hu : AttrIdsUnique s) (D : List AttrId)
    (ht : s'.tree = s.tree) (hD : s'.detachedAttrs.map (·.id) = D) (hDn : D.Nodup)
    (hDo : ∀ m, ∀ i ∈ attrIdsAt s.tree m, i ∉ D)
    (hDN : ∀ p ∈ s'.detachedAttrs.map detachedSig, AttrNormalForm p.2) : AttrIdsUnique s' :=
  ⟨fun m => by rw [ht]; exact hu.within m,
    fun m m' hne i hi => by rw [ht] at hi ⊢; exact hu.across m m' hne i hi,
    by rw [hD]; exact hDn,
    fun m i hi => by rw [ht] at hi; rw [hD]; exact hDo m i hi,
    fun m p hp => by rw [ht] at hp; exact hu.normalized m p hp, hDN⟩

/-! ## 正規形 -/

/-- 正規形の `Attr` は正規化しても変わらない。 -/
theorem normalized_eq_of_normalForm {a : Attr} (h : AttrNormalForm (a.namespace, a.prefix)) :
    a.normalized = a := by
  obtain ⟨hn, hp⟩ := h
  unfold Attr.normalized
  simp only [hn]
  cases a with
  | mk id ns pfx ln v doc =>
    simp only at hn hp ⊢
    cases hns : ns with
    | some x => simp
    | none =>
      cases hpf : pfx with
      | none => simp
      | some y => rw [hns, hpf] at hp; simp at hp

theorem normalForm_normalized (a : Attr) :
    AttrNormalForm (a.normalized.namespace, a.normalized.prefix) :=
  ⟨by simp [normalizeNamespace_idem], a.normalized_prefixHasNamespace⟩

/-- detach された list の `Attr` は正規形にある。 -/
theorem AttrIdsUnique.normalForm_detached {s : DOMState} (hu : AttrIdsUnique s) {a : Attr}
    (ha : a ∈ s.detachedAttrs) : AttrNormalForm (a.namespace, a.prefix) :=
  hu.detachedNormal (detachedSig a) (List.mem_map_of_mem ha)

/-- 各要素が正規形なら、sig の列も正規形である。 -/
theorem detNormal_of_forall {l : List Attr} (h : ∀ a ∈ l, AttrNormalForm (a.namespace, a.prefix)) :
    ∀ p ∈ l.map detachedSig, AttrNormalForm p.2 := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  exact h a ha

theorem attrSigAt_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) (m : NodeId) :
    attrSigAt (setAttributes t n d as) m =
      if m = n then as.map (fun a => (a.id, a.namespace)) else attrSigAt t m := by
  by_cases hm : m = n
  · subst hm; rw [if_pos rfl]; unfold attrSigAt; rw [get?_setAttributes hd, if_pos rfl]
  · rw [if_neg hm]; unfold attrSigAt; rw [get?_setAttributes hd, if_neg hm]

theorem attrSigAt_of_get? {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d) :
    attrSigAt t n = d.attributes.map (fun a => (a.id, a.namespace)) := by
  unfold attrSigAt; rw [hd]

theorem attrIdsAt_of_get? {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d) :
    attrIdsAt t n = d.attributes.map (·.id) := by
  rw [attrIdsAt_eq, attrSigAt_of_get? hd, List.map_map]; rfl

/-- `L` の第一成分。 -/
theorem map_fst_sig (as : List Attr) :
    (as.map (fun a => (a.id, a.namespace))).map Prod.fst = as.map (·.id) := by
  rw [List.map_map]; rfl

/-- `freshStateAttrId` は状態のどこにも無い。 -/
theorem fresh_not_mem_attrIdsAt (s : DOMState) (m : NodeId) :
    freshStateAttrId s ∉ attrIdsAt s.tree m := by
  rw [attrIdsAt_eq]
  unfold attrSigAt
  cases hd : s.tree.get? m with
  | none => simp
  | some d =>
    intro h
    rw [map_fst_sig] at h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    exact ne_freshStateAttrId_tree hd ha he

theorem fresh_not_mem_detached (s : DOMState) :
    freshStateAttrId s ∉ s.detachedAttrs.map (·.id) := by
  intro h
  obtain ⟨a, ha, he⟩ := List.mem_map.mp h
  exact ne_freshStateAttrId_detached ha he

/-- 付いている attribute は正規化されている。 -/
theorem AttrIdsUnique.normalized_of_mem {s : DOMState} (hu : AttrIdsUnique s) {n : NodeId}
    {d : NodeData} (hd : s.tree.get? n = some d) {a : Attr} (ha : a ∈ d.attributes) :
    normalizeNamespace a.namespace = a.namespace :=
  hu.normalized n (a.id, a.namespace) (by rw [attrSigAt_of_get? hd]; exact List.mem_map_of_mem ha)

/-- 付いている attribute は正規形にある。 -/
theorem AttrIdsUnique.normalForm_of_mem {s : DOMState} (hu : AttrIdsUnique s)
    (hav : AttributesValid s.tree) {n : NodeId} {d : NodeData} (hd : s.tree.get? n = some d)
    {a : Attr} (ha : a ∈ d.attributes) : AttrNormalForm (a.namespace, a.prefix) :=
  ⟨hu.normalized_of_mem hd ha, hav.prefixHasNamespace n d hd a ha⟩

/-! ## record を積む段は id の配置を変えない -/

theorem attrFrame_handleAttributeChanges (s : DOMState) (element : NodeId) (a : Attr)
    (ov : Option String) : AttrFrame s (handleAttributeChanges s element a ov) :=
  AttrFrame.of_eq (by simp) (by unfold handleAttributeChanges; simp)

/-! ## change / append / remove -/

theorem attrFrame_changeAttribute {s : DOMState} {element : NodeId} {d : NodeData}
    (hd : s.tree.get? element = some d) (a : Attr) (value : String) :
    AttrFrame s (changeAttribute s element d a value) := by
  unfold changeAttribute
  let T := setAttributes s.tree element d
    (updateFirst (fun b => b.key == a.key) (fun b => { b with value := value }) d.attributes)
  refine AttrFrame.trans (s₁ := { s with tree := T }) ⟨fun m => ?_, rfl⟩
    (attrFrame_handleAttributeChanges ..)
  show attrSigAt (setAttributes s.tree element d _) m = _
  rw [attrSigAt_setAttributes hd]
  split
  · next hm =>
    subst hm; rw [attrSigAt_of_get? hd]
    exact map_updateFirst (g := fun x : Attr => (x.id, x.namespace))
      (f := fun b : Attr => { b with value := value }) (fun _ => rfl) _
  · rfl

/-- 新しい attribute（id が fresh で namespace が正規化済み）を足す。 -/
theorem unique_appendAttribute {s : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) (a₀ : Attr)
    (hfresh : a₀.id = freshStateAttrId s) (hns : normalizeNamespace a₀.namespace = a₀.namespace) :
    AttrIdsUnique (appendAttribute s element d a₀) := by
  unfold appendAttribute
  refine (attrFrame_handleAttributeChanges ..).unique ?_
  have hold := hu.within element
  rw [attrIdsAt_of_get? hd] at hold
  refine hu.of_change element
    (d.attributes.map (fun a => (a.id, a.namespace)) ++ [(a₀.id, a₀.namespace)])
    (s.detachedAttrs.map (·.id)) (fun m => ?_) rfl ?_ hu.detached ?_ ?_ ?_ ?_ hu.detachedNormal
  · show attrSigAt (setAttributes s.tree element d _) m = _
    rw [attrSigAt_setAttributes hd]
    simp
  · rw [List.map_append, map_fst_sig]
    refine List.nodup_append.mpr ⟨hold, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hy
    rw [hy, hfresh] at hxy
    exact fresh_not_mem_attrIdsAt s element (by rw [attrIdsAt_of_get? hd, ← hxy]; exact hx)
  · intro i hi
    rw [List.map_append, map_fst_sig] at hi
    rcases List.mem_append.mp hi with h | h
    · exact hu.attachedDetached element i (by rw [attrIdsAt_of_get? hd]; exact h)
    · simp at h; rw [h, hfresh]; exact fresh_not_mem_detached s
  · intro m hm i hi
    rw [List.map_append, map_fst_sig] at hi
    rcases List.mem_append.mp hi with h | h
    · exact hu.across element m (Ne.symm hm) i (by rw [attrIdsAt_of_get? hd]; exact h)
    · simp at h; rw [h, hfresh]; exact fresh_not_mem_attrIdsAt s m
  · intro m _ i hi; exact hu.attachedDetached m i hi
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact hu.normalized_of_mem hd ha
    · simp at h; rw [h]; exact hns

/-- 部分列に縮める変更は一意性を保つ。 -/
theorem unique_shrink {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId} {d : NodeData}
    (hd : s.tree.get? element = some d) (as : List Attr)
    (hids : ∀ m, attrSigAt s'.tree m =
      if m = element then as.map (fun a => (a.id, a.namespace)) else attrSigAt s.tree m)
    (hD : s'.detachedAttrs = s.detachedAttrs)
    (hsub : as.Sublist d.attributes) : AttrIdsUnique s' := by
  have hold := hu.within element
  rw [attrIdsAt_of_get? hd] at hold
  have hsub' := hsub.map (·.id)
  refine hu.of_change element _ _ hids (by rw [hD]) (by rw [map_fst_sig]; exact hold.sublist hsub')
    hu.detached ?_ ?_ ?_ ?_ (by rw [hD]; exact hu.detachedNormal)
  · intro i hi
    rw [map_fst_sig] at hi
    exact hu.attachedDetached element i (by rw [attrIdsAt_of_get? hd]; exact hsub'.subset hi)
  · intro m hm i hi
    rw [map_fst_sig] at hi
    exact hu.across element m (Ne.symm hm) i (by rw [attrIdsAt_of_get? hd]; exact hsub'.subset hi)
  · intro m _ i hi; exact hu.attachedDetached m i hi
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hu.normalized_of_mem hd (hsub.subset ha)

theorem unique_removeAttributeFrom {s : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) (a : Attr) :
    AttrIdsUnique (removeAttributeFrom s element d a) := by
  unfold removeAttributeFrom
  refine (attrFrame_handleAttributeChanges ..).unique ?_
  let T := setAttributes s.tree element d (eraseFirst (fun b => b.key == a.key) d.attributes)
  refine unique_shrink (s' := { s with tree := T }) hu hd
    (eraseFirst (fun b => b.key == a.key) d.attributes) (fun m => ?_) rfl (eraseFirst_sublist _)
  show attrSigAt (setAttributes s.tree element d _) m = _
  rw [attrSigAt_setAttributes hd]

/-! ## 既存の `Attr` を動かす -/

/-- id に重複の無い list の中の `a` は、その id の最初の位置で切れる。 -/
theorem split_of_mem_id {as : List Attr} {a : Attr} (hmem : a ∈ as) (hnd : (as.map (·.id)).Nodup) :
    ∃ pre post, as = pre ++ a :: post ∧ ∀ x ∈ pre, x.id ≠ a.id := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  refine ⟨pre, post, rfl, fun x hx he => ?_⟩
  rw [List.map_append, List.map_cons] at hnd
  exact (List.nodup_append.mp hnd).2.2 x.id (List.mem_map_of_mem hx) a.id (by simp) he

/-- `findAttr` が detach された `Attr` を返したなら、それは detach された list にある。 -/
theorem findAttr_detached {s : DOMState} {aid : AttrId} {a : Attr}
    (h : findAttr s aid = some (a, none)) : a ∈ s.detachedAttrs ∧ a.id = aid := by
  unfold findAttr at h
  split at h
  · split at h
    · cases h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, h⟩ := h
      cases h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨b, hb, rfl, -⟩ := h
    obtain ⟨hpa, -, -, -⟩ := List.find?_eq_some_iff_append.mp hb
    exact ⟨List.mem_of_find?_eq_some hb, by simpa using hpa⟩

/-- `findAttr` が element に付いた `Attr` を返したなら、それはその element の list にある。 -/
theorem findAttr_attached {s : DOMState} {aid : AttrId} {a : Attr} {n : NodeId}
    (h : findAttr s aid = some (a, some n)) :
    ∃ d, s.tree.get? n = some d ∧ a ∈ d.attributes ∧ a.id = aid := by
  unfold findAttr at h
  split at h
  · split at h
    · cases h
    · next d hd =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨b, hb, rfl, hn⟩ := h
      cases hn
      obtain ⟨hpa, -, -, -⟩ := List.find?_eq_some_iff_append.mp hb
      exact ⟨d, hd, List.mem_of_find?_eq_some hb, by simpa using hpa⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, h⟩ := h
    cases h

theorem unique_detachAttribute {s : DOMState} (hu : AttrIdsUnique s) (hav : AttributesValid s.tree)
    {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {a : Attr} (ha : a ∈ d.attributes) :
    AttrIdsUnique (detachAttribute s element d a) := by
  unfold detachAttribute
  refine (attrFrame_handleAttributeChanges ..).unique ?_
  have hold := hu.within element
  rw [attrIdsAt_of_get? hd] at hold
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem_id ha hold
  have hlist : eraseFirst (fun b => b.id == a.id) d.attributes = pre ++ post := by
    rw [hsplit]
    exact Dom.Spec.eraseFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  have hnd : ((pre ++ a :: post).map (·.id)).Nodup := by rw [← hsplit]; exact hold
  have hnot : a.id ∉ (pre ++ post).map (·.id) := by
    intro hm
    rw [List.map_append] at hm hnd
    rw [List.map_cons] at hnd
    rcases List.mem_append.mp hm with h | h
    · exact (List.nodup_append.mp hnd).2.2 _ h a.id (by simp) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h
  have hsubids : ((pre ++ post).map (·.id)).Sublist (d.attributes.map (·.id)) := by
    rw [hsplit]; simp
  let T := setAttributes s.tree element d (eraseFirst (fun b => b.id == a.id) d.attributes)
  refine hu.of_change (s' := { s with tree := T, detachedAttrs := s.detachedAttrs ++ [a] }) element
    ((pre ++ post).map (fun b => (b.id, b.namespace)))
    (s.detachedAttrs.map (·.id) ++ [a.id]) (fun m => ?_) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show attrSigAt (setAttributes s.tree element d _) m = _
    rw [attrSigAt_setAttributes hd, hlist]
  · rw [map_fst_sig]; exact hold.sublist hsubids
  · refine List.nodup_append.mpr ⟨hu.detached, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hy; rw [hy] at hxy
    exact hu.attachedDetached element a.id
      (by rw [attrIdsAt_of_get? hd]; exact List.mem_map_of_mem ha) (hxy ▸ hx)
  · intro i hi hD
    rw [map_fst_sig] at hi
    rcases List.mem_append.mp hD with h | h
    · exact hu.attachedDetached element i (by rw [attrIdsAt_of_get? hd]; exact hsubids.subset hi) h
    · simp at h; rw [h] at hi; exact hnot hi
  · intro m hm i hi
    rw [map_fst_sig] at hi
    exact hu.across element m (Ne.symm hm) i (by rw [attrIdsAt_of_get? hd]; exact hsubids.subset hi)
  · intro m hm i hi hD
    rcases List.mem_append.mp hD with h | h
    · exact hu.attachedDetached m i hi h
    · simp at h; rw [h] at hi
      exact hu.across element m (Ne.symm hm) a.id
        (by rw [attrIdsAt_of_get? hd]; exact List.mem_map_of_mem ha) hi
  · intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    refine hu.normalized_of_mem hd ?_
    rw [hsplit]
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · refine detNormal_of_forall fun b hb => ?_
    rcases List.mem_append.mp hb with h | h
    · exact hu.normalForm_detached h
    · simp at h; rw [h]; exact hu.normalForm_of_mem hav hd ha

/-- 鍵に重複の無い list で、同じ鍵の要素は同じである。 -/
theorem eq_of_key_eq {β : Type _} {f : Attr → β} : ∀ {l : List Attr}, (l.map f).Nodup →
    ∀ {x y : Attr}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, he => by
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (he ▸ List.mem_map_of_mem hy') hnd'.1
    · exact absurd (he.symm ▸ List.mem_map_of_mem hx') hnd'.1
    · exact eq_of_key_eq hnd'.2 hx' hy' he

theorem requireElement_ok {t : Tree} {element : NodeId} {d : NodeData}
    (h : requireElement t element = .ok d) : t.get? element = some d ∧ d.kind = .element := by
  unfold requireElement at h
  split at h
  · cases h
  · next d' hd =>
    split at h
    · cases h
    · next hk => cases h; exact ⟨hd, by simpa using hk⟩

/-- 付いている（正規化済みの）`Attr` を、正規化した鍵で引くと自分自身に当たる。 -/
theorem getAttributeByKey_self {d : NodeData} (hav : (d.attributes.map Attr.key).Nodup) {a : Attr}
    (ha : a ∈ d.attributes) (hn : normalizeNamespace a.namespace = a.namespace) :
    getAttributeByKey d a.normalized.namespace a.normalized.localName = some a := by
  unfold getAttributeByKey
  simp only [Attr.normalized_namespace, Attr.normalized_localName, hn]
  cases hf : d.attributes.find? (fun b => b.namespace == a.namespace && b.localName == a.localName)
    with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf a ha)
  | some b =>
    obtain ⟨hpb, -, -, -⟩ := List.find?_eq_some_iff_append.mp hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hpb
    rw [eq_of_key_eq hav (List.mem_of_find?_eq_some hf) ha
      (show b.key = a.key by simp [Attr.key, hpb.1, hpb.2])]

theorem removeDetached_split {s : DOMState} {a : Attr} (hu : AttrIdsUnique s)
    (ha : a ∈ s.detachedAttrs) :
    ∃ pre post, s.detachedAttrs = pre ++ a :: post ∧
      (removeDetached s a.id).detachedAttrs = pre ++ post := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_of_mem_id ha hu.detached
  refine ⟨pre, post, hsplit, ?_⟩
  show eraseFirst (fun b => b.id == a.id) s.detachedAttrs = _
  rw [hsplit]
  exact Dom.Spec.eraseFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)

/-- detach された `a₀` を、`element` に足す（`setAttributeNode` の step 8）。 -/
theorem unique_appendDetached {s : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) {a₀ : Attr} (ha : a₀ ∈ s.detachedAttrs) :
    AttrIdsUnique (appendAttribute (removeDetached s a₀.id) element d a₀.normalized) := by
  obtain ⟨Dpre, Dpost, hDs, hDr⟩ := removeDetached_split hu ha
  unfold appendAttribute
  refine (attrFrame_handleAttributeChanges ..).unique ?_
  have hold := hu.within element
  rw [attrIdsAt_of_get? hd] at hold
  have hdet := hu.detached
  rw [hDs] at hdet
  -- a₀ の id はどこの element にも無い
  have hfree : ∀ m, a₀.id ∉ attrIdsAt s.tree m := fun m hm =>
    hu.attachedDetached m a₀.id hm (List.mem_map_of_mem ha)
  have hDsub : ∀ i ∈ (Dpre ++ Dpost).map (·.id), i ∈ s.detachedAttrs.map (·.id) := by
    intro i hi; rw [hDs]; simp at hi ⊢
    rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hnotD : a₀.id ∉ (Dpre ++ Dpost).map (·.id) := by
    intro hm
    rw [List.map_append, List.map_cons] at hdet
    rw [List.map_append] at hm
    rcases List.mem_append.mp hm with h | h
    · exact (List.nodup_append.mp hdet).2.2 _ h a₀.id (by simp) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp hdet).2.1).1 h
  let T := setAttributes s.tree element d (d.attributes ++ [{ a₀.normalized with ownerDocument := d.ownerDocument }])
  refine hu.of_change (s' := { removeDetached s a₀.id with tree := T }) element
    (d.attributes.map (fun a => (a.id, a.namespace)) ++ [(a₀.id, normalizeNamespace a₀.namespace)])
    ((Dpre ++ Dpost).map (·.id)) (fun m => ?_) (by show List.map _ (removeDetached s a₀.id).detachedAttrs = _; rw [hDr])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show attrSigAt (setAttributes s.tree element d _) m = _
    rw [attrSigAt_setAttributes hd]
    simp
  · rw [List.map_append, map_fst_sig]
    refine List.nodup_append.mpr ⟨hold, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hy; rw [hy] at hxy
    exact hfree element (by rw [attrIdsAt_of_get? hd, ← hxy]; exact hx)
  · rw [List.map_append] at hdet ⊢
    rw [List.map_cons] at hdet
    exact List.nodup_append.mpr ⟨(List.nodup_append.mp hdet).1,
      (List.nodup_cons.mp (List.nodup_append.mp hdet).2.1).2,
      fun x hx y hy => (List.nodup_append.mp hdet).2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
  · intro i hi hD
    rw [List.map_append, map_fst_sig] at hi
    rcases List.mem_append.mp hi with h | h
    · exact hu.attachedDetached element i (by rw [attrIdsAt_of_get? hd]; exact h) (hDsub i hD)
    · simp at h; rw [h] at hD; exact hnotD hD
  · intro m hm i hi
    rw [List.map_append, map_fst_sig] at hi
    rcases List.mem_append.mp hi with h | h
    · exact hu.across element m (Ne.symm hm) i (by rw [attrIdsAt_of_get? hd]; exact h)
    · simp at h; rw [h]; exact hfree m
  · intro m _ i hi hD; exact hu.attachedDetached m i hi (hDsub i hD)
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨a, ha', rfl⟩ := List.mem_map.mp h
      exact hu.normalized_of_mem hd ha'
    · simp at h; rw [h]; simp
  · show ∀ p ∈ (removeDetached s a₀.id).detachedAttrs.map detachedSig, _
    rw [hDr]
    refine detNormal_of_forall fun b hb => hu.normalForm_detached ?_
    rw [hDs]; simp at hb ⊢
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- detach された `a₀` で、付いている `old` を置き換える（`setAttributeNode` の step 7）。 -/
theorem unique_replaceDetached {s : DOMState} (hu : AttrIdsUnique s) (hav : AttributesValid s.tree)
    {element : NodeId}
    {d : NodeData} (hd : s.tree.get? element = some d) (hkeys : (d.attributes.map Attr.key).Nodup)
    {a₀ old : Attr} (ha : a₀ ∈ s.detachedAttrs) (hold : old ∈ d.attributes) :
    AttrIdsUnique (replaceAttributeWith (removeDetached s a₀.id) element d old a₀.normalized) := by
  obtain ⟨Dpre, Dpost, hDs, hDr⟩ := removeDetached_split hu ha
  obtain ⟨pre, post, hsplit, hpre⟩ := Dom.Spec.split_of_mem hold hkeys
  have hlist : updateFirst (fun b => b.key == old.key)
      (fun _ => { a₀.normalized with ownerDocument := d.ownerDocument }) d.attributes =
      pre ++ { a₀.normalized with ownerDocument := d.ownerDocument } :: post := by
    rw [hsplit]
    exact Dom.Spec.updateFirst_split pre post (fun x hx => by simpa using hpre x hx) (by simp)
  unfold replaceAttributeWith
  refine (attrFrame_handleAttributeChanges ..).unique ?_
  have hids := hu.within element
  rw [attrIdsAt_of_get? hd, hsplit] at hids
  have hdet := hu.detached
  rw [hDs] at hdet
  simp only [List.map_append, List.map_cons] at hids hdet
  have hfree : ∀ m, a₀.id ∉ attrIdsAt s.tree m := fun m hm =>
    hu.attachedDetached m a₀.id hm (List.mem_map_of_mem ha)
  have holdD : old.id ∉ s.detachedAttrs.map (·.id) :=
    hu.attachedDetached element old.id (by rw [attrIdsAt_of_get? hd]; exact List.mem_map_of_mem hold)
  have hmemOld : ∀ i, i ∈ pre.map (·.id) ∨ i ∈ post.map (·.id) → i ∈ attrIdsAt s.tree element := by
    intro i hi; rw [attrIdsAt_of_get? hd, hsplit]; simp at hi ⊢
    rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hmemD : ∀ i, i ∈ Dpre.map (·.id) ∨ i ∈ Dpost.map (·.id) → i ∈ s.detachedAttrs.map (·.id) := by
    intro i hi; rw [hDs]; simp at hi ⊢
    rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have holdPP : old.id ∉ pre.map (·.id) ∧ old.id ∉ post.map (·.id) := by
    constructor
    · intro h; exact (List.nodup_append.mp hids).2.2 _ h old.id (by simp) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp hids).2.1).1
  have ha₀D : a₀.id ∉ Dpre.map (·.id) ∧ a₀.id ∉ Dpost.map (·.id) := by
    constructor
    · intro h; exact (List.nodup_append.mp hdet).2.2 _ h a₀.id (by simp) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp hdet).2.1).1
  have hne : a₀.id ≠ old.id := fun he =>
    hfree element (by rw [attrIdsAt_of_get? hd, he]; exact List.mem_map_of_mem hold)
  let T := setAttributes s.tree element d (updateFirst (fun b => b.key == old.key)
    (fun _ => { a₀.normalized with ownerDocument := d.ownerDocument }) d.attributes)
  let D' := (removeDetached s a₀.id).detachedAttrs ++ [old]
  refine hu.of_change (s' := { removeDetached s a₀.id with tree := T, detachedAttrs := D' }) element
    ((pre ++ { a₀.normalized with ownerDocument := d.ownerDocument } :: post).map
      (fun a => (a.id, a.namespace)))
    ((Dpre ++ Dpost).map (·.id) ++ [old.id]) (fun m => ?_)
    (by show List.map _ ((removeDetached s a₀.id).detachedAttrs ++ [old]) = _; simp [hDr])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show attrSigAt (setAttributes s.tree element d _) m = _
    rw [attrSigAt_setAttributes hd, hlist]
  · rw [map_fst_sig]
    simp only [List.map_append, List.map_cons]
    refine List.nodup_append.mpr ⟨(List.nodup_append.mp hids).1, List.nodup_cons.mpr
      ⟨fun h => hfree element (hmemOld _ (Or.inr h)),
        (List.nodup_cons.mp (List.nodup_append.mp hids).2.1).2⟩, ?_⟩
    intro x hx y hy hxy
    rcases List.mem_cons.mp hy with h | h
    · rw [h] at hxy; exact hfree element (hxy ▸ hmemOld _ (Or.inl hx))
    · exact (List.nodup_append.mp hids).2.2 x hx y (List.mem_cons_of_mem _ h) hxy
  · simp only [List.map_append]
    refine List.nodup_append.mpr ⟨?_, by simp, ?_⟩
    · exact List.nodup_append.mpr ⟨(List.nodup_append.mp hdet).1,
        (List.nodup_cons.mp (List.nodup_append.mp hdet).2.1).2,
        fun x hx y hy => (List.nodup_append.mp hdet).2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
    · intro x hx y hy hxy
      simp at hy; rw [hy] at hxy
      rw [← hxy] at holdD
      exact holdD (hmemD x (List.mem_append.mp hx))
  · intro i hi hD
    rw [map_fst_sig] at hi
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hi hD
    rcases hD with hD | hD
    · rcases hi with h | h | h
      · exact hu.attachedDetached element i (hmemOld i (Or.inl h)) (hmemD i hD)
      · simp at h; rw [h] at hD; rcases hD with hD | hD
        · exact ha₀D.1 hD
        · exact ha₀D.2 hD
      · exact hu.attachedDetached element i (hmemOld i (Or.inr h)) (hmemD i hD)
    · simp at hD; rw [hD] at hi
      rcases hi with h | h | h
      · exact holdPP.1 h
      · simp at h; exact hne h.symm
      · exact holdPP.2 h
  · intro m hm i hi
    rw [map_fst_sig] at hi
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hi
    rcases hi with h | h | h
    · exact hu.across element m (Ne.symm hm) i (hmemOld i (Or.inl h))
    · simp at h; rw [h]; exact hfree m
    · exact hu.across element m (Ne.symm hm) i (hmemOld i (Or.inr h))
  · intro m hm i hi hD
    simp only [List.map_append, List.mem_append] at hD
    rcases hD with hD | hD
    · exact hu.attachedDetached m i hi (hmemD i hD)
    · simp at hD; rw [hD] at hi
      exact hu.across element m (Ne.symm hm) old.id
        (by rw [attrIdsAt_of_get? hd]; exact List.mem_map_of_mem hold) hi
  · intro p hp
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp ha' with h | h
    · exact hu.normalized_of_mem hd (by rw [hsplit]; exact List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with h | h
      · rw [h]; simp
      · exact hu.normalized_of_mem hd
          (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
  · show ∀ p ∈ ((removeDetached s a₀.id).detachedAttrs ++ [old]).map detachedSig, _
    rw [hDr]
    refine detNormal_of_forall fun b hb => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (h | h) | h
    · exact hu.normalForm_detached (by rw [hDs]; exact List.mem_append_left _ h)
    · exact hu.normalForm_detached
        (by rw [hDs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    · rw [h]; exact hu.normalForm_of_mem hav hd hold

theorem unique_setAttributeNode {s s' : DOMState} (hu : AttrIdsUnique s) (hav : AttributesValid s.tree)
    {element : NodeId} {aid : AttrId} {r : Option AttrId}
    (h : setAttributeNode s element aid = .ok (r, s')) : AttrIdsUnique s' := by
  unfold setAttributeNode at h
  split at h
  · cases h
  · next d hreq =>
    obtain ⟨hd, -⟩ := requireElement_ok hreq
    have hkeys := hav.keysNodup element d hd
    split at h
    · cases h
    · next a₀ owner hfind =>
      split at h
      · cases h
      · next hown =>
        have howner : owner = none ∨ owner = some element := by
          cases owner with
          | none => exact Or.inl rfl
          | some n =>
            right
            by_cases hne : n = element
            · rw [hne]
            · exact absurd (by simp [hne]) hown
        -- 付いている側なら、引き直した結果は自分自身である
        have hself : owner = some element →
            getAttributeByKey d a₀.normalized.namespace a₀.normalized.localName = some a₀ ∧
              a₀.id = aid := by
          intro ho
          rw [ho] at hfind
          obtain ⟨d', hd', ha₀, hid⟩ := findAttr_attached hfind
          rw [hd] at hd'; cases hd'
          exact ⟨getAttributeByKey_self hkeys ha₀ (hu.normalized_of_mem hd ha₀), hid⟩
        split at h
        · next old hgk =>
          split at h
          · cases h; exact hu
          · next hne =>
            cases h
            rcases howner with ho | ho
            · rw [ho] at hfind
              obtain ⟨ha₀, hid⟩ := findAttr_detached hfind
              subst hid
              have hold : old ∈ d.attributes := by
                unfold getAttributeByKey at hgk
                exact List.mem_of_find?_eq_some hgk
              exact unique_replaceDetached hu hav hd hkeys ha₀ hold
            · obtain ⟨hg, hid⟩ := hself ho
              rw [hg] at hgk; cases hgk
              exact absurd (by simp [hid]) hne
        · next hgk =>
          cases h
          rcases howner with ho | ho
          · rw [ho] at hfind
            obtain ⟨ha₀, hid⟩ := findAttr_detached hfind
            subst hid
            exact unique_appendDetached hu hd ha₀
          · obtain ⟨hg, -⟩ := hself ho
            rw [hg] at hgk; cases hgk

theorem unique_removeAttributeNode {s s' : DOMState} (hu : AttrIdsUnique s)
    (hav : AttributesValid s.tree) {element : NodeId}
    {aid r : AttrId} (h : removeAttributeNode s element aid = .ok (r, s')) : AttrIdsUnique s' := by
  unfold removeAttributeNode at h
  split at h
  · cases h
  · next d hreq =>
    obtain ⟨hd, -⟩ := requireElement_ok hreq
    split at h
    · cases h
    · next a hf =>
      cases h
      exact unique_detachAttribute hu hav hd (List.mem_of_find?_eq_some hf)

theorem unique_removeNamedItem {s s' : DOMState} (hu : AttrIdsUnique s)
    (hav : AttributesValid s.tree) {element : NodeId}
    {qn : String} {r : AttrId} (h : removeNamedItem s element qn = .ok (r, s')) :
    AttrIdsUnique s' := by
  unfold removeNamedItem at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact unique_removeAttributeNode hu hav h

/-! ## 新しい `Attr` を detach された list に足す -/

theorem unique_addDetachedFresh {s : DOMState} (hu : AttrIdsUnique s) (a : Attr)
    (hfresh : a.id = freshStateAttrId s) (hn : AttrNormalForm (a.namespace, a.prefix)) :
    AttrIdsUnique { s with detachedAttrs := s.detachedAttrs ++ [a] } := by
  refine hu.of_detached (s.detachedAttrs.map (·.id) ++ [a.id]) rfl (by simp) ?_ ?_ ?_
  · refine List.nodup_append.mpr ⟨hu.detached, by simp, ?_⟩
    intro x hx y hy hxy
    simp at hy; rw [hy, hfresh] at hxy
    exact fresh_not_mem_detached s (hxy ▸ hx)
  · intro m i hi hD
    rcases List.mem_append.mp hD with h | h
    · exact hu.attachedDetached m i hi h
    · simp at h; rw [h, hfresh] at hi; exact fresh_not_mem_attrIdsAt s m hi
  · refine detNormal_of_forall fun b hb => ?_
    rcases List.mem_append.mp hb with h | h
    · exact hu.normalForm_detached h
    · simp at h; rw [h]; exact hn

theorem unique_createAttributeIn {s : DOMState} (hu : AttrIdsUnique s) (doc : NodeId)
    (ns pfx : Option String) (ln : String) : AttrIdsUnique (createAttributeIn s doc ns pfx ln).2 :=
  unique_addDetachedFresh hu _ rfl (normalForm_normalized _)

theorem unique_cloneAttrIn {s : DOMState} (hu : AttrIdsUnique s) (a : Attr) (doc : NodeId)
    (hn : AttrNormalForm (a.namespace, a.prefix)) : AttrIdsUnique (cloneAttrIn s a doc).2 :=
  unique_addDetachedFresh hu _ rfl hn

/-- `findAttr` が返す `Attr` は正規形にある。 -/
theorem AttrIdsUnique.normalForm_findAttr {s : DOMState} (hu : AttrIdsUnique s)
    (hav : AttributesValid s.tree) {aid : AttrId} {a : Attr} {o : Option NodeId}
    (h : findAttr s aid = some (a, o)) : AttrNormalForm (a.namespace, a.prefix) := by
  cases o with
  | none => exact hu.normalForm_detached (findAttr_detached h).1
  | some n =>
    obtain ⟨d, hd, ha, -⟩ := findAttr_attached h
    exact hu.normalForm_of_mem hav hd ha

/-! ## `Attr` を一つ書き換える -/

/-- id と namespace を変えない書き換えは枠を保つ。 -/
theorem attrFrame_modifyAttr (s : DOMState) (aid : AttrId) (f : Attr → Attr)
    (hf : ∀ b, (f b).id = b.id ∧ (f b).namespace = b.namespace ∧ (f b).prefix = b.prefix) :
    AttrFrame s (modifyAttr s aid f) := by
  unfold modifyAttr
  split
  · split
    · exact AttrFrame.refl _
    · next d hd =>
      split
      · refine ⟨fun m => ?_, rfl⟩
        show attrSigAt (setAttributes s.tree _ d _) m = _
        rw [attrSigAt_setAttributes hd]
        split
        · next hm =>
          subst hm; rw [attrSigAt_of_get? hd, List.map_map]
          congr 1; funext b
          simp only [Function.comp]
          split <;> simp [hf]
        · rfl
      · exact AttrFrame.refl _
  · refine ⟨fun m => rfl, ?_⟩
    show List.map _ (s.detachedAttrs.map _) = _
    rw [List.map_map]
    congr 1; funext b
    simp only [Function.comp]
    split <;> simp [detachedSig, hf]

theorem unique_adoptAttr {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId} {aid r : AttrId}
    (h : adoptAttr s doc aid = .ok (r, s')) : AttrIdsUnique s' := by
  unfold adoptAttr at h
  repeat' split at h
  all_goals first
    | (cases h; exact hu)
    | (cases h; exact (attrFrame_modifyAttr s aid (fun x => x.withOwnerDocument doc)
        (fun b => ⟨rfl, rfl, rfl⟩)).unique hu)
    | (cases h; done)

theorem unique_importAttr {s s' : DOMState} (hu : AttrIdsUnique s) (hav : AttributesValid s.tree)
    {doc : NodeId} {aid r : AttrId}
    (h : importAttr s doc aid = .ok (r, s')) : AttrIdsUnique s' := by
  unfold importAttr at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_cloneAttrIn hu _ _ (hu.normalForm_findAttr hav (by assumption)))
    | (cases h; done)

theorem unique_cloneAttr {s s' : DOMState} (hu : AttrIdsUnique s) (hav : AttributesValid s.tree)
    {aid r : AttrId}
    (h : cloneAttr s aid = .ok (r, s')) : AttrIdsUnique s' := by
  unfold cloneAttr at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_cloneAttrIn hu _ _ (hu.normalForm_findAttr hav (by assumption)))
    | (cases h; done)

theorem unique_setAttrValue {s s' : DOMState} (hu : AttrIdsUnique s) {aid : AttrId} {v : String}
    (h : setAttrValue s aid v = .ok s') : AttrIdsUnique s' := by
  unfold setAttrValue at h
  repeat' split at h
  all_goals first
    | (cases h; exact (attrFrame_modifyAttr s aid (fun b => { b with value := v })
        (fun b => ⟨rfl, rfl, rfl⟩)).unique hu)
    | (cases h; exact (attrFrame_changeAttribute (by assumption) _ _).unique hu)
    | (cases h; done)

theorem unique_createAttribute {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {ln : String} {r : AttrId} (h : createAttribute s doc ln = .ok (r, s')) : AttrIdsUnique s' := by
  unfold createAttribute at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_createAttributeIn hu _ _ _ _)
    | (cases h; done)

theorem unique_createAttributeNS {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {ns : Option String} {qn : String} {r : AttrId}
    (h : createAttributeNS s doc ns qn = .ok (r, s')) : AttrIdsUnique s' := by
  unfold createAttributeNS at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_createAttributeIn hu _ _ _ _)
    | (cases h; done)

/-! ## `Element` の method -/

theorem unique_setAttributeValue {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {localName value : String} {pfx ns : Option String}
    (h : setAttributeValue s element localName value pfx ns = .ok s') : AttrIdsUnique s' := by
  unfold setAttributeValue at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · split at h
      · rw [← Except.ok.inj h]
        exact unique_appendAttribute hu hd _ rfl (normalizeNamespace_idem _)
      · rw [← Except.ok.inj h]
        exact (attrFrame_changeAttribute hd _ _).unique hu

theorem unique_setAttribute {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {qn value : String} (h : setAttribute s element qn value = .ok s') : AttrIdsUnique s' := by
  unfold setAttribute at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next d hd =>
      split at h
      · simp at h
      · split at h
        · rw [← Except.ok.inj h]; exact (attrFrame_changeAttribute hd _ _).unique hu
        · rw [← Except.ok.inj h]; exact unique_appendAttribute hu hd _ rfl rfl

theorem unique_setAttributeNS {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {ns : Option String} {qn value : String} (h : setAttributeNS s element ns qn value = .ok s') :
    AttrIdsUnique s' := by
  unfold setAttributeNS at h
  split at h
  · simp at h
  · exact unique_setAttributeValue hu h

theorem unique_removeAttribute {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {qn : String} (h : removeAttribute s element qn = .ok s') : AttrIdsUnique s' := by
  unfold removeAttribute at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · split at h
      · rw [← Except.ok.inj h]; exact hu
      · rw [← Except.ok.inj h]; exact unique_removeAttributeFrom hu hd _

theorem unique_removeAttributeNS {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {ns : Option String} {ln : String} (h : removeAttributeNS s element ns ln = .ok s') :
    AttrIdsUnique s' := by
  unfold removeAttributeNS at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · split at h
      · rw [← Except.ok.inj h]; exact hu
      · rw [← Except.ok.inj h]; exact unique_removeAttributeFrom hu hd _

theorem unique_toggleAttribute {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {qn : String} {force : Option Bool} {b : Bool}
    (h : toggleAttribute s element qn force = .ok (s', b)) : AttrIdsUnique s' := by
  unfold toggleAttribute at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next d hd =>
      split at h
      · simp at h
      · split at h
        · split at h
          · cases h; exact hu
          · cases h; exact unique_appendAttribute hu hd _ rfl rfl
        · split at h
          · cases h; exact hu
          · cases h; exact unique_removeAttributeFrom hu hd _

/-! ## reflect・dataset・classList -/

theorem unique_tokenListUpdate {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {d : NodeData} {set : List String} (h : tokenListUpdate s element d set = .ok s') :
    AttrIdsUnique s' := by
  unfold tokenListUpdate at h
  split at h
  · rw [← Except.ok.inj h]; exact hu
  · exact unique_setAttributeValue hu h

private theorem unique_of_update_pair {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {d : NodeData} {set : List String} {b b' : Bool}
    (h : (do let s₁ ← tokenListUpdate s element d set; pure (s₁, b) :
      Except DOMException (DOMState × Bool)) = .ok (s', b')) : AttrIdsUnique s' := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i s₁ hupd
    have : s₁ = s' := (Prod.mk.inj (Except.ok.inj h)).1
    subst this
    exact unique_tokenListUpdate hu hupd

theorem unique_classListAdd {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {tokens : List String} (h : classListAdd s element tokens = .ok s') : AttrIdsUnique s' := by
  unfold classListAdd at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · exact unique_tokenListUpdate hu h

theorem unique_classListRemove {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {tokens : List String} (h : classListRemove s element tokens = .ok s') : AttrIdsUnique s' := by
  unfold classListRemove at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · exact unique_tokenListUpdate hu h

theorem unique_classListToggle {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {token : String} {force : Option Bool} {b : Bool}
    (h : classListToggle s element token force = .ok (s', b)) : AttrIdsUnique s' := by
  unfold classListToggle at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · split at h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact hu
        · exact unique_of_update_pair hu h
      · split at h
        · exact unique_of_update_pair hu h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact hu

theorem unique_classListReplace {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {token newToken : String} {b : Bool}
    (h : classListReplace s element token newToken = .ok (s', b)) : AttrIdsUnique s' := by
  unfold classListReplace at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact hu
        · exact unique_of_update_pair hu h

theorem unique_setReflectedProp {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {r : ReflectSpec} {v : String} (h : setReflectedProp s element r v = .ok s') :
    AttrIdsUnique s' := by
  unfold setReflectedProp at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · exact unique_setAttributeValue hu h

theorem unique_setReflectedBool {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {r : ReflectSpec} {b : Bool} (h : setReflectedBool s element r b = .ok s') :
    AttrIdsUnique s' := by
  unfold setReflectedBool at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · exact unique_setAttributeValue hu h
    · exact unique_removeAttributeNS hu h

theorem unique_datasetSet {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {name v : String} (h : datasetSet s element name v = .ok s') : AttrIdsUnique s' := by
  unfold datasetSet at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact unique_setAttributeValue hu h

theorem unique_datasetDelete {s s' : DOMState} (hu : AttrIdsUnique s) {element : NodeId}
    {name : String} (h : datasetDelete s element name = .ok s') : AttrIdsUnique s' := by
  unfold datasetDelete at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]; exact hu
    · exact unique_removeAttribute hu h

/-! ## node を新しく作る -/

/-- 状態にある attribute の id は、どれも `stateMaxAttrId` 以下である。 -/
theorem le_stateMaxAttrId_of_mem (s : DOMState) {m : NodeId} {i : AttrId}
    (h : i ∈ attrIdsAt s.tree m) : i.id ≤ stateMaxAttrId s := by
  rw [attrIdsAt_eq] at h
  unfold attrSigAt at h
  cases hd : s.tree.get? m with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd, map_fst_sig] at h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact Nat.le_trans (attrId_le_maxAttrId hd ha) (Nat.le_max_left _ _)

theorem le_stateMaxAttrId_of_detached (s : DOMState) {i : AttrId}
    (h : i ∈ s.detachedAttrs.map (·.id)) : i.id ≤ stateMaxAttrId s := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  exact Nat.le_trans (attrId_le_maxDetachedAttrId s.detachedAttrs 0 ha) (Nat.le_max_right _ _)

/--
**fresh な node を足す。** その node の attribute の id が重複せず、どれも状態の最大より大きく、
namespace が正規化されていれば、一意性は保たれる。
-/
theorem unique_withFresh {s : DOMState} (hu : AttrIdsUnique s) (d : NodeData)
    (hnd : (d.attributes.map (·.id)).Nodup)
    (hbig : ∀ a ∈ d.attributes, stateMaxAttrId s < a.id.id)
    (hns : ∀ a ∈ d.attributes, normalizeNamespace a.namespace = a.namespace) :
    AttrIdsUnique (withFresh s d).2 := by
  have hfresh := freshId_get?_eq_none s.tree
  refine hu.of_change (freshId s.tree) (d.attributes.map (fun a => (a.id, a.namespace)))
    _ (fun m => ?_) rfl (by rw [map_fst_sig]; exact hnd) hu.detached ?_ ?_ ?_ ?_ hu.detachedNormal
  · show attrSigAt (s.tree.insertNode (freshId s.tree) d) m = _
    by_cases hm : m = freshId s.tree
    · subst hm; rw [if_pos rfl]; unfold attrSigAt; rw [get?_insertNode_self]
    · rw [if_neg hm]; unfold attrSigAt; rw [get?_insertNode_ne _ hm]
  · intro i hi hD
    rw [map_fst_sig] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    have := le_stateMaxAttrId_of_detached s hD
    have := hbig a ha
    omega
  · intro m _ i hi hm
    rw [map_fst_sig] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    have := le_stateMaxAttrId_of_mem s hm
    have := hbig a ha
    omega
  · intro m _ i hi; exact hu.attachedDetached m i hi
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hns a ha

private theorem unique_withFresh_empty {s : DOMState} (hu : AttrIdsUnique s) (d : NodeData)
    (h : d.attributes = []) : AttrIdsUnique (withFresh s d).2 :=
  unique_withFresh hu d (by simp [h]) (by simp [h]) (by simp [h])

theorem unique_createTextNode {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {data : String} {n : NodeId} (h : createTextNode s doc data = .ok (n, s')) : AttrIdsUnique s' := by
  unfold createTextNode at h
  split at h
  · cases h
  · cases h; exact unique_withFresh_empty hu _ rfl

theorem unique_createComment {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {data : String} {n : NodeId} (h : createComment s doc data = .ok (n, s')) : AttrIdsUnique s' := by
  unfold createComment at h
  split at h
  · cases h
  · cases h; exact unique_withFresh_empty hu _ rfl

theorem unique_createDocumentFragment {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {n : NodeId} (h : createDocumentFragment s doc = .ok (n, s')) : AttrIdsUnique s' := by
  unfold createDocumentFragment at h
  split at h
  · cases h
  · cases h; exact unique_withFresh_empty hu _ rfl

theorem unique_createElement {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {ln : String} {n : NodeId} (h : createElement s doc ln = .ok (n, s')) : AttrIdsUnique s' := by
  unfold createElement at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_withFresh_empty hu _ rfl)
    | (cases h; done)

theorem unique_createElementNS {s s' : DOMState} (hu : AttrIdsUnique s) {doc : NodeId}
    {ns : Option String} {qn : String} {n : NodeId} (h : createElementNS s doc ns qn = .ok (n, s')) :
    AttrIdsUnique s' := by
  unfold createElementNS at h
  repeat' split at h
  all_goals first
    | (cases h; exact unique_withFresh_empty hu _ rfl)
    | (cases h; done)

/-! ## clone -/

private theorem zipIdx_ids {α : Type _} (b : Nat) : ∀ (l : List α) (k : Nat),
    ((l.zipIdx k).map (fun p => (⟨b + p.2⟩ : AttrId))).Nodup ∧
      ∀ i ∈ (l.zipIdx k).map (fun p => (⟨b + p.2⟩ : AttrId)), b + k ≤ i.id
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons]
    obtain ⟨hnd, hge⟩ := zipIdx_ids b l (k + 1)
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun i hi => ?_⟩
    · have := hge _ hm; simp at this; omega
    · rcases List.mem_cons.mp hi with rfl | hi
      · simp
      · have := hge i hi; omega

private theorem mem_of_mem_zipIdx' {α : Type _} {l : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ l.zipIdx) : x ∈ l := by
  obtain ⟨-, hlt, he⟩ := List.mem_zipIdx h
  rw [he]
  exact List.getElem_mem _

theorem unique_cloneSingle {s : DOMState} (hu : AttrIdsUnique s) {n : NodeId} {d : NodeData}
    (hd : s.tree.get? n = some d) (doc : NodeId) : AttrIdsUnique (cloneSingle s d doc).2 := by
  unfold cloneSingle
  refine unique_withFresh hu _ ?_ ?_ ?_
  · rw [cloneData_attributes, List.map_map]
    exact (zipIdx_ids (stateMaxAttrId s + 1) d.attributes 0).1
  · intro a ha
    rw [cloneData_attributes] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    show stateMaxAttrId s < stateMaxAttrId s + 1 + p.2
    omega
  · intro a ha
    rw [cloneData_attributes] at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    show normalizeNamespace p.1.namespace = p.1.namespace
    exact hu.normalized_of_mem hd (mem_of_mem_zipIdx' (x := p.1) (i := p.2) hp)

theorem unique_cloneMany : ∀ (fuel : Nat) {s : DOMState} {ns : List NodeId} {doc : NodeId}
    {parent : Option NodeId} {r : List NodeId} {s' : DOMState}, AttrIdsUnique s →
    cloneMany fuel s ns doc parent = .ok (r, s') → AttrIdsUnique s'
  | _, s, [], _, _, _, _, hu, h => by
    rw [cloneMany] at h; cases h; exact hu
  | 0, _, _ :: _, _, _, _, _, _, h => by rw [cloneMany] at h; cases h
  | fuel + 1, s, n :: rest, doc, parent, r, s', hu, h => by
    rw [cloneMany] at h
    split at h
    · cases h
    · next d hd =>
      have h₁ := unique_cloneSingle hu hd doc
      simp only [] at h
      split at h
      · cases h
      · next s₂ hap =>
        have h₂ : AttrIdsUnique s₂ := by
          unfold cloneAppend at hap
          split at hap
          · cases hap; exact h₁
          · exact (attrFrame_preInsert hap).unique h₁
        split at h
        · cases h
        · next res₃ hc =>
          obtain ⟨_, s₃⟩ := res₃
          have h₃ := unique_cloneMany fuel h₂ hc
          split at h
          · cases h
          · next res₄ hc' =>
            obtain ⟨_, s₄⟩ := res₄
            cases h
            exact unique_cloneMany fuel h₃ hc'

theorem unique_cloneNodeIn {s s' : DOMState} (hu : AttrIdsUnique s) {n doc : NodeId}
    {deep : Bool} {c : NodeId} (h : cloneNodeIn s n doc deep = .ok (c, s')) : AttrIdsUnique s' := by
  unfold cloneNodeIn at h
  split at h
  · cases h
  · next d hd =>
    split at h
    · split at h
      · cases h
      · next res hc => cases h; exact unique_cloneMany _ hu hc
      · cases h
    · cases h; exact unique_cloneSingle hu hd doc

theorem unique_cloneNode {s s' : DOMState} (hu : AttrIdsUnique s) {n : NodeId} {deep : Bool}
    {c : NodeId} (h : cloneNode s n deep = .ok (c, s')) : AttrIdsUnique s' := by
  unfold cloneNode at h
  split at h
  · cases h
  · exact unique_cloneNodeIn hu h

theorem unique_importNode {s s' : DOMState} (hu : AttrIdsUnique s) {doc n : NodeId} {deep : Bool}
    {c : NodeId} (h : importNode s doc n deep = .ok (c, s')) : AttrIdsUnique s' := by
  unfold importNode at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact unique_cloneNodeIn hu h

end Dom
