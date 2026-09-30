import Selectors.Spec.Attr

/-!
# attribute selector の構文の関係仕様は実行関数を特徴づける

`Selectors/Parser.lean` の `attrFlag` / `attrValue` / `attrTail` / `parseAttrBlock` が、
`Selectors/Spec/Attr.lean` の関係をちょうど満たすことを示す。
-/

namespace Selectors.Spec

open Selectors
open Infra

/-- **`attrFlag` は flag の関係をちょうど表す。** -/
theorem attrFlag_spec (name : String) (anyNs : Bool) (op : AttrOp) (v : String)
    (l : List Component) (s : Simple) :
    attrFlag name anyNs op v l = some s ↔
      ∃ c : AttrCase, AttrFlagSyntax l c ∧ s = .attr name anyNs (some ⟨op, v, c⟩) := by
  constructor
  · intro h
    unfold attrFlag at h
    split at h
    · next hd => exact ⟨.byDocument, .none hd, by simp_all⟩
    · next f rest hd =>
      split at h
      · simp at h
      · next hne =>
        have he : dropWs rest = [] := by simpa using hne
        dsimp only at h
        split at h
        · next hf => exact ⟨.insensitive, .insensitive hd he hf, by simp_all⟩
        · split at h
          · next hf => exact ⟨.sensitive, .sensitive hd he hf, by simp_all⟩
          · simp at h
    · simp at h
  · rintro ⟨c, hc, rfl⟩
    cases hc with
    | none hd => unfold attrFlag; simp [hd]
    | insensitive hd he hf =>
      rw [beq_iff_eq] at hf
      unfold attrFlag; simp [hd, he, hf]
    | sensitive hd he hf =>
      rw [beq_iff_eq] at hf
      unfold attrFlag; simp [hd, he, hf]

/-- **`attrValue` は値の関係をちょうど表す。** -/
theorem attrValue_spec (name : String) (anyNs : Bool) (op : AttrOp) (l : List Component)
    (s : Simple) :
    attrValue name anyNs op l = some s ↔
      ∃ t : AttrTest, AttrValueSyntax l op t ∧ s = .attr name anyNs (some t) := by
  constructor
  · intro h
    unfold attrValue at h
    split at h
    · next v rest hd =>
      obtain ⟨c, hc, hs⟩ := (attrFlag_spec name anyNs op v rest _).mp h
      exact ⟨⟨op, v, c⟩, .str hd hc, by simp_all⟩
    · next v rest hd =>
      obtain ⟨c, hc, hs⟩ := (attrFlag_spec name anyNs op v rest _).mp h
      exact ⟨⟨op, v, c⟩, .ident hd hc, by simp_all⟩
    · simp at h
  · rintro ⟨t, ht, rfl⟩
    cases ht with
    | str hd hc =>
      unfold attrValue
      rw [hd]
      exact (attrFlag_spec name anyNs op _ _ _).mpr ⟨_, hc, rfl⟩
    | ident hd hc =>
      unfold attrValue
      rw [hd]
      exact (attrFlag_spec name anyNs op _ _ _).mpr ⟨_, hc, rfl⟩

/-- **`attrTail` は `[name]` / `[name op value flag]` の関係をちょうど表す。** -/
theorem attrTail_spec (name : String) (anyNs : Bool) (l : List Component) (s : Simple) :
    attrTail name anyNs l = some s ↔ AttrTailSyntax name anyNs l s := by
  constructor
  · intro h
    unfold attrTail at h
    split at h
    · next hd =>
      simp only [Option.some.injEq] at h
      subst h
      exact .plain hd
    · next d rest hd =>
      split at h
      · next he =>
        obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .exact rest _).mp h
        subst hs
        exact .exact hd he ht
      · next hne =>
        split at h
        · next e rest2 =>
          split at h
          · simp at h
          · next heq =>
            split at h
            · next hd1 =>
              obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .includes rest2 _).mp h
              subst hs
              exact .includes hd hd1 (by simpa using heq) ht
            · split at h
              · next hd1 =>
                obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .dashMatch rest2 _).mp h
                subst hs
                exact .dashMatch hd hd1 (by simpa using heq) ht
              · split at h
                · next hd1 =>
                  obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .prefixMatch rest2 _).mp h
                  subst hs
                  exact .prefixMatch hd hd1 (by simpa using heq) ht
                · split at h
                  · next hd1 =>
                    obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .suffixMatch rest2 _).mp h
                    subst hs
                    exact .suffixMatch hd hd1 (by simpa using heq) ht
                  · split at h
                    · next hd1 =>
                      obtain ⟨t, ht, hs⟩ := (attrValue_spec name anyNs .substring rest2 _).mp h
                      subst hs
                      exact .substring hd hd1 (by simpa using heq) ht
                    · simp at h
        · simp at h
    · simp at h
  · intro h
    cases h with
    | plain hd => unfold attrTail; simp [hd]
    | exact hd h1 ht =>
      unfold attrTail
      rw [hd]
      simp only [if_pos h1]
      exact (attrValue_spec name anyNs .exact _ _).mpr ⟨_, ht, rfl⟩
    | includes hd h1 he ht =>
      unfold attrTail
      rw [hd]
      simp only [beq_iff_eq] at h1 he
      simp [h1, he]
      exact (attrValue_spec name anyNs .includes _ _).mpr ⟨_, ht, rfl⟩
    | dashMatch hd h1 he ht =>
      unfold attrTail
      rw [hd]
      simp only [beq_iff_eq] at h1 he
      simp [h1, he]
      exact (attrValue_spec name anyNs .dashMatch _ _).mpr ⟨_, ht, rfl⟩
    | prefixMatch hd h1 he ht =>
      unfold attrTail
      rw [hd]
      simp only [beq_iff_eq] at h1 he
      simp [h1, he]
      exact (attrValue_spec name anyNs .prefixMatch _ _).mpr ⟨_, ht, rfl⟩
    | suffixMatch hd h1 he ht =>
      unfold attrTail
      rw [hd]
      simp only [beq_iff_eq] at h1 he
      simp [h1, he]
      exact (attrValue_spec name anyNs .suffixMatch _ _).mpr ⟨_, ht, rfl⟩
    | substring hd h1 he ht =>
      unfold attrTail
      rw [hd]
      simp only [beq_iff_eq] at h1 he
      simp [h1, he]
      exact (attrValue_spec name anyNs .substring _ _).mpr ⟨_, ht, rfl⟩

/-- **`parseAttrBlock` は `[*|name ...]` / `[name ...]` の関係をちょうど表す。** -/
theorem parseAttrBlock_spec (items : List Component) (s : Simple) :
    parseAttrBlock items = some s ↔ AttrBlockSyntax items s := by
  constructor
  · intro h
    unfold parseAttrBlock at h
    split at h
    · next d p name rest hd =>
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨rfl, rfl⟩ := hcond
        exact .anyNs hd ((attrTail_spec name true rest _).mp h)
      · simp at h
    · next name rest hd => exact .plain hd ((attrTail_spec name false rest _).mp h)
    · simp at h
  · intro h
    cases h with
    | plain hd ht =>
      unfold parseAttrBlock
      rw [hd]
      exact (attrTail_spec _ false _ _).mpr ht
    | anyNs hd ht =>
      unfold parseAttrBlock
      rw [hd]
      simp only [beq_self_eq_true, Bool.and_self, if_true]
      exact (attrTail_spec _ true _ _).mpr ht

end Selectors.Spec
