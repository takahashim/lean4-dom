import Dom.Attribute.Algorithms
import Dom.Properties.Algorithms
import Dom.Validity.Iterators
import Dom.Validity.AttributeList

/-!
# attribute list の妥当性

`AdmissibleDOMState` の第七成分。§4.9 の algorithm が保つ、attribute list の局所不変条件である。

仕様は attribute list に明文の不変条件を置いていないが、次の二つを前提にしている。

* attribute を持つのは Element だけである（attribute list は Element の状態である）。
* 一つの element の attribute list は namespace と local name の組で一意である。
  "get an attribute by namespace and local name" が
  「その attribute（あれば）」と単数で書いているのはこの前提による。
* namespace prefix があるなら namespace もある
  （"validate and extract" の step 8 が毎回これを保証している）。

三つ目は二つ目を保つのに要る。attribute list に prefix 付き・namespace 無しの attribute が
あると、`setAttribute` が qualified name で探して見つけられないまま
同じ鍵の attribute を append してしまう。
-/

namespace Dom

open Dom.ListUtil

/-!
## attribute list 以外を変えない変更

§4.9 の algorithm はどれも `setAttributes` を通るだけなので、
木の形も node document も `data` も変えない。
`AdmissibleDOMState` の他の成分がそのまま移ることを、この関係を通して一度に示す。
-/

/-- attribute list 以外を変えない変更。 -/
def AttributesOnly (t t' : Tree) : Prop :=
  ∀ m, (t'.get? m).map (fun d => { d with attributes := ([] : List Attr) })
     = (t.get? m).map (fun d => { d with attributes := ([] : List Attr) })

namespace AttributesOnly

theorem refl (t : Tree) : AttributesOnly t t := fun _ => rfl

theorem symm {t t' : Tree} (h : AttributesOnly t t') : AttributesOnly t' t := fun m => (h m).symm

/-- attribute だけを落とした node data が等しいなら、他の五つの field は等しい。 -/
theorem eq_of_erase {d₀ d : NodeData}
    (he : { d₀ with attributes := ([] : List Attr) } = { d with attributes := ([] : List Attr) }) :
    d₀.kind = d.kind ∧ d₀.parent = d.parent ∧ d₀.children = d.children ∧
      d₀.ownerDocument = d.ownerDocument ∧ d₀.data = d.data := by
  cases d₀; cases d
  simp only [NodeData.mk.injEq] at he
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1⟩

/-- 変更後に node があるなら変更前にもあり、attribute list 以外は同じである。 -/
theorem exists_get? {t t' : Tree} (h : AttributesOnly t t') {m : NodeId} {d : NodeData}
    (hd : t'.get? m = some d) :
    ∃ d₀, t.get? m = some d₀ ∧ d₀.kind = d.kind ∧ d₀.parent = d.parent ∧
      d₀.children = d.children ∧ d₀.ownerDocument = d.ownerDocument ∧ d₀.data = d.data := by
  have hm := h m
  rw [hd] at hm
  cases hd₀ : t.get? m with
  | none => rw [hd₀] at hm; simp at hm
  | some d₀ =>
    rw [hd₀] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    exact ⟨d₀, rfl, eq_of_erase hm.symm⟩

theorem get?_eq_none {t t' : Tree} (h : AttributesOnly t t') {m : NodeId}
    (hd : t'.get? m = none) : t.get? m = none := by
  have hm := h m
  rw [hd] at hm
  cases hd₀ : t.get? m with
  | none => rfl
  | some _ => rw [hd₀] at hm; simp at hm

@[simp] theorem kindOf {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    kindOf t' m = kindOf t m := by
  cases hd : t'.get? m with
  | none => simp [Dom.kindOf, hd, h.get?_eq_none hd]
  | some d =>
    obtain ⟨d₀, hd₀, hk, _⟩ := h.exists_get? hd
    simp [Dom.kindOf, hd, hd₀, hk]

@[simp] theorem parentOf {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    parentOf t' m = parentOf t m := by
  cases hd : t'.get? m with
  | none => simp [Dom.parentOf, hd, h.get?_eq_none hd]
  | some d =>
    obtain ⟨d₀, hd₀, _, hp, _⟩ := h.exists_get? hd
    simp [Dom.parentOf, hd, hd₀, hp]

@[simp] theorem childrenOf {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    childrenOf t' m = childrenOf t m := by
  cases hd : t'.get? m with
  | none => simp [Dom.childrenOf, hd, h.get?_eq_none hd]
  | some d =>
    obtain ⟨d₀, hd₀, _, _, hc, _⟩ := h.exists_get? hd
    simp [Dom.childrenOf, hd, hd₀, hc]

@[simp] theorem ownerDocumentOf {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    ownerDocumentOf t' m = ownerDocumentOf t m := by
  cases hd : t'.get? m with
  | none => simp [Dom.ownerDocumentOf, hd, h.get?_eq_none hd]
  | some d =>
    obtain ⟨d₀, hd₀, _, _, _, ho, _⟩ := h.exists_get? hd
    simp [Dom.ownerDocumentOf, hd, hd₀, ho]

@[simp] theorem lengthOf {t t' : Tree} (h : AttributesOnly t t') (m : NodeId) :
    lengthOf t' m = lengthOf t m := by
  cases hd : t'.get? m with
  | none => simp [Dom.lengthOf, hd, h.get?_eq_none hd]
  | some d =>
    obtain ⟨d₀, hd₀, hk, _, hc, _, hdata⟩ := h.exists_get? hd
    simp [Dom.lengthOf, hd, hd₀, NodeData.length, hk, hc, hdata]

/-- `Ancestor` は parent だけで決まる。 -/
theorem ancestor {t t' : Tree} (h : AttributesOnly t t') {a n : NodeId} (ha : Ancestor t a n) :
    Ancestor t' a n := ancestor_congr (fun m => h.parentOf m) ha

end AttributesOnly

/-! ## 他の成分がそのまま移ること -/

theorem wellFormed_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    (hwf : WellFormed t) : WellFormed t' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p pd hp c hc
    obtain ⟨pd₀, hpd₀, _, _, hch, _⟩ := h.exists_get? hp
    obtain ⟨cd₀, hcd₀, hcp⟩ := hwf.parent_child p pd₀ hpd₀ c (by rw [hch]; exact hc)
    obtain ⟨cd, hcd, _, hp', _⟩ := h.symm.exists_get? hcd₀
    exact ⟨cd, hcd, by rw [hp']; exact hcp⟩
  · intro c cd p hc hp
    obtain ⟨cd₀, hcd₀, _, hpar, _⟩ := h.exists_get? hc
    obtain ⟨pd₀, hpd₀, hmem⟩ := hwf.child_parent c cd₀ p hcd₀ (by rw [hpar]; exact hp)
    obtain ⟨pd, hpd, _, _, hch', _⟩ := h.symm.exists_get? hpd₀
    exact ⟨pd, hpd, by rw [hch']; exact hmem⟩
  · intro n d hd
    obtain ⟨d₀, hd₀, _, _, hch, _⟩ := h.exists_get? hd
    rw [← hch]
    exact hwf.children_nodup n d₀ hd₀
  · intro n hn
    exact hwf.acyclic n (h.symm.ancestor hn)
  · intro n d hd
    obtain ⟨d₀, hd₀, _, _, _, ho, _⟩ := h.exists_get? hd
    obtain ⟨dd₀, hdd₀, hk⟩ := hwf.ownerDocument_is_document n d₀ hd₀
    obtain ⟨dd, hdd, hk', _⟩ := h.symm.exists_get? hdd₀
    exact ⟨dd, by rw [← ho]; exact hdd, by rw [hk']; exact hk⟩

theorem structurallyValid_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    (hs : StructurallyValid t) : StructurallyValid t' := by
  refine ⟨wellFormed_of_attributesOnly h hs.wellFormed, ?_, ?_, ?_, ?_⟩
  · intro n d hd hk
    obtain ⟨d₀, hd₀, hkk, hp, _⟩ := h.exists_get? hd
    rw [← hp]
    exact hs.documentHasNoParent n d₀ hd₀ (by rw [hkk]; exact hk)
  · intro n d hd hk
    obtain ⟨d₀, hd₀, hkk, hp, _⟩ := h.exists_get? hd
    rw [← hp]
    exact hs.fragmentHasNoParent n d₀ hd₀ (by rw [hkk]; exact hk)
  · intro n d hd hc
    obtain ⟨d₀, hd₀, hkk, _, hch, _⟩ := h.exists_get? hd
    rw [← hkk]
    exact hs.childrenOnlyUnderContainers n d₀ hd₀ (by rw [hch]; exact hc)
  · intro n d hd hk p hp pd hpd
    obtain ⟨d₀, hd₀, hkk, hpar, _⟩ := h.exists_get? hd
    obtain ⟨pd₀, hpd₀, hkp, _⟩ := h.exists_get? hpd
    rw [← hkp]
    exact hs.doctypeParentIsDocument n d₀ hd₀ (by rw [hkk]; exact hk) p
      (by rw [hpar]; exact hp) pd₀ hpd₀

theorem nodeDocumentsValid_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    (hn : NodeDocumentsValid t) : NodeDocumentsValid t' := by
  refine ⟨?_, ?_⟩
  · intro n d hd hk
    obtain ⟨d₀, hd₀, hkk, _, _, ho, _⟩ := h.exists_get? hd
    rw [← ho]
    exact hn.documentIsOwnNodeDocument n d₀ hd₀ (by rw [hkk]; exact hk)
  · intro c p hp
    rw [h.ownerDocumentOf, h.ownerDocumentOf]
    exact hn.treeEdgePreservesNodeDocument c p (by rw [← h.parentOf]; exact hp)

theorem documentTreesValid_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    (hd : DocumentTreesValid t) : DocumentTreesValid t' :=
  documentTreesValid_of_sameShape (fun m => h.kindOf m) (fun m => h.childrenOf m) hd

/-! ## `setAttributes` はこの関係を満たす -/

theorem attributesOnly_setAttributes {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (as : List Attr) : AttributesOnly t (setAttributes t n d as) := by
  intro m
  rw [get?_setAttributes hd]
  by_cases hm : m = n
  · subst hm; simp [hd]
  · rw [if_neg hm]

/-! ## 木の surgery は attribute を触らない -/

/-- `ShapePreserving` な変更は `AttributesValid` を保つ。 -/
theorem AttributesValid.map {t t' : Tree} (hs : ShapePreserving t t') (h : AttributesValid t) :
    AttributesValid t' := by
  refine ⟨?_, ?_, ?_⟩ <;> intro n d hd
  · obtain ⟨d₀, hd₀, hk, ha, _⟩ := hs.exists_get? hd
    intro hne
    rw [← ha]
    exact h.onlyElements n d₀ hd₀ (by rw [hk]; exact hne)
  · obtain ⟨d₀, hd₀, _, ha, _⟩ := hs.exists_get? hd
    rw [← ha]
    exact h.keysNodup n d₀ hd₀
  · obtain ⟨d₀, hd₀, _, ha, _⟩ := hs.exists_get? hd
    rw [← ha]
    exact h.prefixHasNamespace n d₀ hd₀


/-! ## attribute list を差し替える側 -/

/--
`setAttributes` が `AttributesValid` を保つ条件。

差し替える先が element であり、新しい list が鍵について重複を持たず、
prefix があるなら namespace もあればよい。
-/
theorem attributesValid_setAttributes {t : Tree} {n : NodeId} {d : NodeData} {as : List Attr}
    (hd : t.get? n = some d) (h : AttributesValid t) (hk : d.kind = .element)
    (hnd : (as.map Attr.key).Nodup)
    (hpfx : ∀ a ∈ as, a.prefix.isSome → a.namespace.isSome) :
    AttributesValid (setAttributes t n d as) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro m d' hd' <;> rw [get?_setAttributes hd] at hd' <;>
    by_cases hm : m = n
  · rw [if_pos hm] at hd'
    rw [← Option.some.inj hd']
    intro hne
    exact absurd hk hne
  · rw [if_neg hm] at hd'
    exact h.onlyElements m d' hd'
  · rw [if_pos hm] at hd'
    rw [← Option.some.inj hd']
    exact hnd
  · rw [if_neg hm] at hd'
    exact h.keysNodup m d' hd'
  · rw [if_pos hm] at hd'
    rw [← Option.some.inj hd']
    exact hpfx
  · rw [if_neg hm] at hd'
    exact h.prefixHasNamespace m d' hd'

/-! ## §4.9 の algorithm は木の形を変えない -/

@[simp] theorem handleAttributeChanges_tree (s : DOMState) (element : NodeId) (a : Attr)
    (ov : Option String) : (handleAttributeChanges s element a ov).tree = s.tree := by
  unfold handleAttributeChanges; simp

@[simp] theorem handleAttributeChanges_ranges (s : DOMState) (element : NodeId) (a : Attr)
    (ov : Option String) : (handleAttributeChanges s element a ov).ranges = s.ranges := by
  unfold handleAttributeChanges; simp

@[simp] theorem handleAttributeChanges_iterators (s : DOMState) (element : NodeId) (a : Attr)
    (ov : Option String) : (handleAttributeChanges s element a ov).iterators = s.iterators := by
  unfold handleAttributeChanges; simp

@[simp] theorem handleAttributeChanges_registrations (s : DOMState) (element : NodeId) (a : Attr)
    (ov : Option String) :
    (handleAttributeChanges s element a ov).registrations = s.registrations := by
  unfold handleAttributeChanges; simp

@[simp] theorem handleAttributeChanges_observers_length (s : DOMState) (element : NodeId)
    (a : Attr) (ov : Option String) :
    (handleAttributeChanges s element a ov).observers.length = s.observers.length := by
  unfold handleAttributeChanges; simp

/-!
## attribute list の三つの変更が妥当性を保つこと

どれも `attributesValid_setAttributes` に落ちる。示すのは新しい list の性質だけである。
-/

theorem attributesValid_change {t : Tree} {n : NodeId} {d : NodeData} {a : Attr} {value : String}
    (hd : t.get? n = some d) (h : AttributesValid t) (hk : d.kind = .element) :
    AttributesValid (setAttributes t n d
      (updateFirst (fun b => b.key == a.key) (fun b => { b with value := value }) d.attributes)) := by
  refine attributesValid_setAttributes hd h hk ?_ ?_
  · rw [map_updateFirst (p := fun b => b.key == a.key)
        (f := fun b => { b with value := value }) (g := Attr.key) (fun _ => rfl)]
    exact h.keysNodup n d hd
  · intro b hb
    rcases mem_updateFirst hb with hb' | ⟨b₀, hb₀, rfl⟩
    · exact h.prefixHasNamespace n d hd b hb'
    · exact h.prefixHasNamespace n d hd b₀ hb₀

theorem attributesValid_append {t : Tree} {n : NodeId} {d : NodeData} {a : Attr}
    (hd : t.get? n = some d) (h : AttributesValid t) (hk : d.kind = .element)
    (hnew : a.key ∉ d.attributes.map Attr.key)
    (hpfx : a.prefix.isSome → a.namespace.isSome) :
    AttributesValid (setAttributes t n d (d.attributes ++ [a])) := by
  refine attributesValid_setAttributes hd h hk ?_ ?_
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨h.keysNodup n d hd, by simp, ?_⟩
    intro x hx y hy heq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    exact hnew ((heq.trans hy) ▸ hx)
  · intro b hb
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.prefixHasNamespace n d hd b hb'
    · simp at hb'; subst hb'; exact hpfx

theorem attributesValid_erase {t : Tree} {n : NodeId} {d : NodeData} {p : Attr → Bool}
    (hd : t.get? n = some d) (h : AttributesValid t) (hk : d.kind = .element) :
    AttributesValid (setAttributes t n d (eraseFirst p d.attributes)) := by
  have hsub : (eraseFirst p d.attributes).Sublist d.attributes := eraseFirst_sublist _
  refine attributesValid_setAttributes hd h hk ?_ ?_
  · exact ((hsub.map Attr.key).nodup (h.keysNodup n d hd))
  · intro b hb
    exact h.prefixHasNamespace n d hd b (hsub.subset hb)

/-! ## 三つの primitive の frame -/

@[simp] theorem changeAttribute_tree (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr)
    (value : String) : (changeAttribute s element d a value).tree =
      setAttributes s.tree element d
        (updateFirst (fun b => b.key == a.key) (fun b => { b with value := value }) d.attributes) := by
  unfold changeAttribute; simp

@[simp] theorem changeAttribute_ranges (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr)
    (value : String) : (changeAttribute s element d a value).ranges = s.ranges := by
  unfold changeAttribute; simp

@[simp] theorem changeAttribute_iterators (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) (value : String) :
    (changeAttribute s element d a value).iterators = s.iterators := by
  unfold changeAttribute; simp

@[simp] theorem changeAttribute_registrations (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) (value : String) :
    (changeAttribute s element d a value).registrations = s.registrations := by
  unfold changeAttribute; simp

@[simp] theorem changeAttribute_observers_length (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) (value : String) :
    (changeAttribute s element d a value).observers.length = s.observers.length := by
  unfold changeAttribute; simp

@[simp] theorem appendAttribute_tree (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) :
    (appendAttribute s element d a).tree =
      setAttributes s.tree element d (d.attributes ++ [a]) := by
  unfold appendAttribute; simp

@[simp] theorem appendAttribute_ranges (s : DOMState) (element : NodeId) (d : NodeData) (a : Attr) :
    (appendAttribute s element d a).ranges = s.ranges := by
  unfold appendAttribute; simp

@[simp] theorem appendAttribute_iterators (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (appendAttribute s element d a).iterators = s.iterators := by
  unfold appendAttribute; simp

@[simp] theorem appendAttribute_registrations (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (appendAttribute s element d a).registrations = s.registrations := by
  unfold appendAttribute; simp

@[simp] theorem appendAttribute_observers_length (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (appendAttribute s element d a).observers.length = s.observers.length := by
  unfold appendAttribute; simp

@[simp] theorem removeAttributeFrom_tree (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (removeAttributeFrom s element d a).tree =
      setAttributes s.tree element d (eraseFirst (fun b => b.key == a.key) d.attributes) := by
  unfold removeAttributeFrom; simp

@[simp] theorem removeAttributeFrom_ranges (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (removeAttributeFrom s element d a).ranges = s.ranges := by
  unfold removeAttributeFrom; simp

@[simp] theorem removeAttributeFrom_iterators (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (removeAttributeFrom s element d a).iterators = s.iterators := by
  unfold removeAttributeFrom; simp

@[simp] theorem removeAttributeFrom_registrations (s : DOMState) (element : NodeId) (d : NodeData)
    (a : Attr) : (removeAttributeFrom s element d a).registrations = s.registrations := by
  unfold removeAttributeFrom; simp

@[simp] theorem removeAttributeFrom_observers_length (s : DOMState) (element : NodeId)
    (d : NodeData) (a : Attr) :
    (removeAttributeFrom s element d a).observers.length = s.observers.length := by
  unfold removeAttributeFrom; simp

/-! ## 鍵が使われていないこと -/

/--
namespace と local name で見つからないなら、その鍵を持つ attribute は無い。

`getAttributeByKey` は namespace を正規化してから探すので、鍵も正規化した側で述べる。
-/
theorem key_not_mem_of_getAttributeByKey_none {d : NodeData} {ns : Option String}
    {localName : String} (hnone : getAttributeByKey d ns localName = none) :
    (normalizeNamespace ns, localName) ∉ d.attributes.map Attr.key := by
  intro hmem
  obtain ⟨b, hb, hkey⟩ := List.mem_map.mp hmem
  simp only [Attr.key, Prod.mk.injEq] at hkey
  have := (List.find?_eq_none.mp hnone) b hb
  simp [hkey.1, hkey.2] at this

/--
qualified name で見つからないなら、`(null, qualifiedName)` を鍵に持つ attribute も無い。

prefix があるなら namespace もある（`AttributesValid.prefixHasNamespace`）ので、
namespace が null の attribute の qualified name は local name そのものである。
この invariant が無いと、prefix 付き・namespace 無しの attribute が
qualified name による探索から隠れたまま同じ鍵で append されてしまう。
-/
theorem key_not_mem_of_getAttributeByName_none {t : Tree} {n : NodeId} {d : NodeData}
    (hd : t.get? n = some d) (h : AttributesValid t) {qn : String}
    (hnone : getAttributeByName t d qn = none) :
    ((none : Option String), attrNameFor t d qn) ∉ d.attributes.map Attr.key := by
  intro hmem
  obtain ⟨b, hb, hkey⟩ := List.mem_map.mp hmem
  simp only [Attr.key, Prod.mk.injEq] at hkey
  have hpfx : b.prefix = none := by
    cases hp : b.prefix with
    | none => rfl
    | some _ =>
      exfalso
      have hns := h.prefixHasNamespace n d hd b hb (by rw [hp]; rfl)
      rw [hkey.1] at hns
      simp at hns
  have := (List.find?_eq_none.mp hnone) b hb
  simp [Attr.qualifiedName, hpfx, hkey.2] at this

/-!
## §4.9 の method がまとめて満たすこと

attribute の algorithm は木の attribute list 以外を変えず、live object と registration を
そのまま残し、observer の数も変えない。加えて `AttributesValid` を保つ。
public API ごとの分岐をここで一度だけ潰しておく。
-/

/-- attribute の algorithm が返す状態が満たす性質。 -/
structure AttrOpResult (s s' : DOMState) : Prop where
  tree : AttributesOnly s.tree s'.tree
  ranges : s'.ranges = s.ranges
  iterators : s'.iterators = s.iterators
  registrations : s'.registrations = s.registrations
  observersLength : s'.observers.length = s.observers.length
  attributes : AttributesValid s.tree → AttributesValid s'.tree

theorem AttrOpResult.refl (s : DOMState) : AttrOpResult s s :=
  ⟨AttributesOnly.refl _, rfl, rfl, rfl, rfl, id⟩

theorem attrOpResult_change {s : DOMState} {element : NodeId} {d : NodeData} {a : Attr}
    {value : String} (hd : s.tree.get? element = some d) (hk : d.kind = .element) :
    AttrOpResult s (changeAttribute s element d a value) :=
  ⟨by rw [changeAttribute_tree]; exact attributesOnly_setAttributes hd _,
    changeAttribute_ranges .., changeAttribute_iterators .., changeAttribute_registrations ..,
    changeAttribute_observers_length ..,
    fun h => by rw [changeAttribute_tree]; exact attributesValid_change hd h hk⟩

theorem attrOpResult_append {s : DOMState} {element : NodeId} {d : NodeData} {a : Attr}
    (hd : s.tree.get? element = some d) (hk : d.kind = .element)
    (hnew : AttributesValid s.tree → a.key ∉ d.attributes.map Attr.key)
    (hpfx : a.prefix.isSome → a.namespace.isSome) :
    AttrOpResult s (appendAttribute s element d a) :=
  ⟨by rw [appendAttribute_tree]; exact attributesOnly_setAttributes hd _,
    appendAttribute_ranges .., appendAttribute_iterators .., appendAttribute_registrations ..,
    appendAttribute_observers_length ..,
    fun h => by rw [appendAttribute_tree]; exact attributesValid_append hd h hk (hnew h) hpfx⟩

theorem attrOpResult_remove {s : DOMState} {element : NodeId} {d : NodeData} {a : Attr}
    (hd : s.tree.get? element = some d) (hk : d.kind = .element) :
    AttrOpResult s (removeAttributeFrom s element d a) :=
  ⟨by rw [removeAttributeFrom_tree]; exact attributesOnly_setAttributes hd _,
    removeAttributeFrom_ranges .., removeAttributeFrom_iterators ..,
    removeAttributeFrom_registrations .., removeAttributeFrom_observers_length ..,
    fun h => by rw [removeAttributeFrom_tree]; exact attributesValid_erase hd h hk⟩

theorem attrOpResult_setAttribute {s s' : DOMState} {element : NodeId} {qn value : String}
    (hr : setAttribute s element qn value = .ok s') : AttrOpResult s s' := by
  unfold setAttribute at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next d hd =>
      split at hr
      · simp at hr
      · next hk =>
        have hk' : d.kind = .element := by simpa using hk
        split at hr
        · next a ha =>
          rw [← Except.ok.inj hr]; exact attrOpResult_change hd hk'
        · next hnone =>
          rw [← Except.ok.inj hr]
          refine attrOpResult_append hd hk' ?_ (by simp)
          intro h
          exact key_not_mem_of_getAttributeByName_none hd h hnone

theorem attrOpResult_setAttributeValue {s s' : DOMState} {element : NodeId}
    {localName value : String} {pfx ns : Option String}
    (hpfx : pfx.isSome → (normalizeNamespace ns).isSome)
    (hr : setAttributeValue s element localName value pfx ns = .ok s') : AttrOpResult s s' := by
  unfold setAttributeValue at hr
  split at hr
  · simp at hr
  · next d hd =>
    split at hr
    · simp at hr
    · next hk =>
      have hk' : d.kind = .element := by simpa using hk
      split at hr
      · next hnone =>
        rw [← Except.ok.inj hr]
        refine attrOpResult_append hd hk' ?_ hpfx
        exact fun _ => key_not_mem_of_getAttributeByKey_none hnone
      · next a ha =>
        rw [← Except.ok.inj hr]; exact attrOpResult_change hd hk'

theorem attrOpResult_removeAttribute {s s' : DOMState} {element : NodeId} {qn : String}
    (hr : removeAttribute s element qn = .ok s') : AttrOpResult s s' := by
  unfold removeAttribute at hr
  split at hr
  · simp at hr
  · next d hd =>
    split at hr
    · simp at hr
    · next hk =>
      have hk' : d.kind = .element := by simpa using hk
      split at hr
      · rw [← Except.ok.inj hr]; exact AttrOpResult.refl _
      · rw [← Except.ok.inj hr]; exact attrOpResult_remove hd hk'

theorem attrOpResult_removeAttributeNS {s s' : DOMState} {element : NodeId} {ns : Option String}
    {localName : String} (hr : removeAttributeNS s element ns localName = .ok s') :
    AttrOpResult s s' := by
  unfold removeAttributeNS at hr
  split at hr
  · simp at hr
  · next d hd =>
    split at hr
    · simp at hr
    · next hk =>
      have hk' : d.kind = .element := by simpa using hk
      split at hr
      · rw [← Except.ok.inj hr]; exact AttrOpResult.refl _
      · rw [← Except.ok.inj hr]; exact attrOpResult_remove hd hk'

theorem attrOpResult_toggleAttribute {s s' : DOMState} {element : NodeId} {qn : String}
    {force : Option Bool} {b : Bool} (hr : toggleAttribute s element qn force = .ok (s', b)) :
    AttrOpResult s s' := by
  unfold toggleAttribute at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next d hd =>
      split at hr
      · simp at hr
      · next hk =>
        have hk' : d.kind = .element := by simpa using hk
        split at hr
        · next hnone =>
          split at hr
          · have : s' = s := congrArg Prod.fst (Except.ok.inj hr).symm
            rw [this]; exact AttrOpResult.refl _
          · have : s' = appendAttribute s element d
                { id := freshAttrId s.tree, localName := attrNameFor s.tree d qn } :=
              congrArg Prod.fst (Except.ok.inj hr).symm
            rw [this]
            refine attrOpResult_append hd hk' ?_ (by simp)
            intro h
            exact key_not_mem_of_getAttributeByName_none hd h hnone
        · next a ha =>
          split at hr
          · have : s' = s := congrArg Prod.fst (Except.ok.inj hr).symm
            rw [this]; exact AttrOpResult.refl _
          · have : s' = removeAttributeFrom s element d a :=
              congrArg Prod.fst (Except.ok.inj hr).symm
            rw [this]; exact attrOpResult_remove hd hk'

/--
`setAttributeNS` は "validate and extract" が prefix と namespace の対応を保証するので、
`setAttributeValue` の前提が揃う。
-/
theorem attrOpResult_setAttributeNS {s s' : DOMState} {element : NodeId} {ns : Option String}
    {qn value : String} (hr : setAttributeNS s element ns qn value = .ok s') :
    AttrOpResult s s' := by
  unfold setAttributeNS at hr
  split at hr
  · simp at hr
  · next res he =>
    obtain ⟨ns', pfx, localName⟩ := res
    obtain ⟨hns, hpfx⟩ := validateAndExtractAttribute_ok he
    refine attrOpResult_setAttributeValue ?_ hr
    rw [hns, normalizeNamespace_idem, ← hns]
    exact hpfx

/-! ## live object の妥当性も移る -/

theorem validBoundaryPoint_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    {bp : BoundaryPoint} (hv : ValidBoundaryPoint t bp) : ValidBoundaryPoint t' bp := by
  obtain ⟨d, hd, hle⟩ := hv
  cases hd' : t'.get? bp.node with
  | none =>
    exfalso
    rw [h.get?_eq_none hd'] at hd
    simp at hd
  | some d' =>
    refine ⟨d', hd', ?_⟩
    have : lengthOf t' bp.node = lengthOf t bp.node := h.lengthOf bp.node
    simp only [Dom.lengthOf, hd, hd'] at this
    rw [this]
    exact hle

theorem validIterator_of_attributesOnly {t t' : Tree} (h : AttributesOnly t t')
    {it : IteratorState} (hv : ValidIterator t it) : ValidIterator t' it := by
  obtain ⟨⟨d, hd⟩, hanc⟩ := hv
  refine ⟨?_, ?_⟩
  · cases hd' : t'.get? it.reference with
    | none => exfalso; rw [h.get?_eq_none hd'] at hd; simp at hd
    | some d' => exact ⟨d', rfl⟩
  · rcases hanc with he | ha
    · exact Or.inl he
    · exact Or.inr (h.ancestor ha)

end Dom
