import Dom.Attribute.AsNode
import Dom.Validity.AttrNode

/-!
# `Attr` を `Node` として扱う操作も妥当性を保つ

`adoptNode(attr)`・`importNode(attr)`・`cloneNode()`・value の setter は、どれも
`Attr` 一つの node document か value を書き換えるか、detach された `Attr` を一つ足すだけである。
鍵（namespace と local name）も prefix も変えないので、`AttrOpResult` にそのまま乗る。
-/

namespace Dom

/-- 鍵・prefix・namespace を変えない書き換えは、attribute list の妥当性を保つ。 -/
theorem attrOpResult_modifyAttr (s : DOMState) (aid : AttrId) (f : Attr → Attr)
    (hkey : ∀ b, (f b).key = b.key) (hpfx : ∀ b, (f b).prefix = b.prefix)
    (hns : ∀ b, (f b).namespace = b.namespace) :
    AttrOpResult s (modifyAttr s aid f) := by
  unfold modifyAttr
  split
  · next n _ =>
    split
    · exact AttrOpResult.refl _
    · next d hd =>
      split
      · next hk =>
        refine ⟨attributesOnly_setAttributes hd _, rfl, rfl, rfl, rfl, fun h => ?_⟩
        refine attributesValid_setAttributes hd h hk ?_ ?_
        · have : (d.attributes.map fun b => if b.id == aid then f b else b).map Attr.key =
              d.attributes.map Attr.key := by
            rw [List.map_map]
            refine List.map_congr_left fun b _ => ?_
            simp only [Function.comp_apply]
            split <;> simp [hkey]
          rw [this]
          exact h.keysNodup n d hd
        · intro a ha hp
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          by_cases hb' : (b.id == aid) = true
          · simp only [hb', if_true] at hp ⊢
            rw [hns]; rw [hpfx] at hp; exact h.prefixHasNamespace n d hd b hb hp
          · simp only [hb', Bool.false_eq_true, if_false] at hp ⊢
            exact h.prefixHasNamespace n d hd b hb hp
      · exact AttrOpResult.refl _
  · exact ⟨AttributesOnly.refl _, rfl, rfl, rfl, rfl, id⟩

theorem attrOpResult_cloneAttrIn (s : DOMState) (a : Attr) (doc : NodeId) :
    AttrOpResult s (cloneAttrIn s a doc).2 :=
  ⟨AttributesOnly.refl _, rfl, rfl, rfl, rfl, id⟩

theorem attrOpResult_adoptAttr {s s' : DOMState} {doc : NodeId} {aid ret : AttrId}
    (hr : adoptAttr s doc aid = .ok (ret, s')) : AttrOpResult s s' := by
  unfold adoptAttr at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · split at hr
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hr); exact AttrOpResult.refl _
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hr)
        exact attrOpResult_modifyAttr _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem attrOpResult_importAttr {s s' : DOMState} {doc : NodeId} {aid ret : AttrId}
    (hr : importAttr s doc aid = .ok (ret, s')) : AttrOpResult s s' := by
  unfold importAttr at hr
  split at hr
  · simp at hr
  · split at hr
    · simp at hr
    · next a _ _ =>
      have he := congrArg Prod.snd (Except.ok.inj hr)
      simp only at he
      rw [← he]; exact attrOpResult_cloneAttrIn ..

theorem attrOpResult_cloneAttr {s s' : DOMState} {aid ret : AttrId}
    (hr : cloneAttr s aid = .ok (ret, s')) : AttrOpResult s s' := by
  unfold cloneAttr at hr
  split at hr
  · simp at hr
  · have he := congrArg Prod.snd (Except.ok.inj hr)
    simp only at he
    rw [← he]; exact attrOpResult_cloneAttrIn ..

theorem attrOpResult_setAttrValue {s s' : DOMState} {aid : AttrId} {value : String}
    (hr : setAttrValue s aid value = .ok s') : AttrOpResult s s' := by
  unfold setAttrValue at hr
  split at hr
  · simp at hr
  · rw [← Except.ok.inj hr]
    exact attrOpResult_modifyAttr _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · split at hr
    · simp at hr
    · next d hd =>
      split at hr
      · next hk => rw [← Except.ok.inj hr]; exact attrOpResult_change hd hk
      · simp at hr

theorem admissible_adoptAttr {s s' : DOMState} {doc : NodeId} {aid ret : AttrId}
    (h : AdmissibleDOMState s) (hr : adoptAttr s doc aid = .ok (ret, s')) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_adoptAttr hr)

theorem admissible_importAttr {s s' : DOMState} {doc : NodeId} {aid ret : AttrId}
    (h : AdmissibleDOMState s) (hr : importAttr s doc aid = .ok (ret, s')) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_importAttr hr)

theorem admissible_cloneAttr {s s' : DOMState} {aid ret : AttrId}
    (h : AdmissibleDOMState s) (hr : cloneAttr s aid = .ok (ret, s')) : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_cloneAttr hr)

theorem admissible_setAttrValue {s s' : DOMState} {aid : AttrId} {value : String}
    (h : AdmissibleDOMState s) (hr : setAttrValue s aid value = .ok s') : AdmissibleDOMState s' :=
  admissible_of_attrOp h (attrOpResult_setAttrValue hr)

/-- `Attr` が絡む `appendChild` は、どちらも node のときしか成功しない。 -/
theorem admissible_appendChildRef {s s' : DOMState} {parent node : NodeRef}
    (h : AdmissibleDOMState s) (hr : appendChildRef s parent node = .ok s') : AdmissibleDOMState s' := by
  unfold appendChildRef at hr
  split at hr
  · exact admissible_appendChild h hr
  · split at hr <;> simp at hr
  · split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · split at hr <;> simp at hr

end Dom
