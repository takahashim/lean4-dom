import Dom.Properties.Tree

/-!
# attribute list の妥当性

`AdmissibleDOMState` の第七成分。§4.9 の algorithm が保つ、attribute list の局所不変条件である。

仕様は attribute list に明文の不変条件を置いていないが、次の三つを前提にしている。

* attribute を持つのは Element だけである（attribute list は Element の状態である）。
* 一つの element の attribute list は namespace と local name の組で一意である。
  "get an attribute by namespace and local name" が
  「その attribute（あれば）」と単数で書いているのはこの前提による。
* namespace prefix があるなら namespace もある
  （"validate and extract" の step 8 が毎回これを保証している）。

三つ目は二つ目を保つのに要る。attribute list に prefix 付き・namespace 無しの attribute が
あると、`setAttribute` が qualified name で探して見つけられないまま
同じ鍵の attribute を append してしまう。

保存の証明は `Dom/Validity/Attributes.lean` にある。
定義だけをここに置いてあるのは、`Dom/Validity/State.lean` から参照するためである。
-/

namespace Dom

/-- attribute list の局所不変条件。 -/
structure AttributesValid (t : Tree) : Prop where
  /-- Element 以外は attribute を持たない。 -/
  onlyElements : ∀ n d, t.get? n = some d → d.kind ≠ .element → d.attributes = []
  /-- 一つの element の attribute list は namespace と local name の組で一意である。 -/
  keysNodup : ∀ n d, t.get? n = some d → (d.attributes.map Attr.key).Nodup
  /-- prefix があるなら namespace もある。 -/
  prefixHasNamespace : ∀ n d, t.get? n = some d → ∀ a ∈ d.attributes,
    a.prefix.isSome → a.namespace.isSome

/-! ## 実行時の検査 -/

def checkAttributesValid (t : Tree) : Bool :=
  t.nodes.checkAll fun _ d =>
    (d.kind == .element || d.attributes.isEmpty) &&
      Dom.ListUtil.nodupB (d.attributes.map Attr.key) &&
      d.attributes.all fun a => !a.prefix.isSome || a.namespace.isSome

theorem checkAttributesValid_iff (t : Tree) :
    checkAttributesValid t = true ↔ AttributesValid t := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> intro n d hd
    · intro hne
      have := (NodeStore.checkAll_iff t.nodes _).mp h n d hd
      simp only [Bool.and_eq_true] at this
      have h1 := this.1.1
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hne
      · exact List.isEmpty_iff.mp h1
    · have := (NodeStore.checkAll_iff t.nodes _).mp h n d hd
      simp only [Bool.and_eq_true] at this
      exact (Dom.ListUtil.nodupB_iff _).mp this.1.2
    · intro a ha hp
      have := (NodeStore.checkAll_iff t.nodes _).mp h n d hd
      simp only [Bool.and_eq_true] at this
      have := List.all_eq_true.mp this.2 a ha
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
      rcases this with h1 | h1
      · rw [hp] at h1; simp at h1
      · exact h1
  · intro h
    refine (NodeStore.checkAll_iff t.nodes _).mpr fun n d hd => ?_
    refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩, ?_⟩
    · by_cases hk : d.kind = .element
      · simp [hk]
      · simp [h.onlyElements n d hd hk]
    · exact (Dom.ListUtil.nodupB_iff _).mpr (h.keysNodup n d hd)
    · refine List.all_eq_true.mpr fun a ha => ?_
      by_cases hp : a.prefix.isSome
      · simp [hp, h.prefixHasNamespace n d hd a ha hp]
      · simp [hp]

end Dom
