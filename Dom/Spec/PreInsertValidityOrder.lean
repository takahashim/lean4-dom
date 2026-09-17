import Dom.Spec.PreInsertValidity
import Dom.Validity.Structural
import Dom.Properties.Tree

/-!
# `following` / `preceding` の二つの読みが一致すること

`Dom/Spec/PreInsertValidity.lean` の `DoctypeFollowing` / `ElementPreceding` は、
仕様の "a doctype is **following** child" / "an element is **preceding** child" を
**`parent` の children の中での前後**として書いた。仕様の `following` / `preceding` は
**木の順序**（§1.4）である。

ここでその二つが一致することを示す。一致するのは step 9 / step 11 の文脈、つまり
`parent` が Document で `child` がその子であるときだけで、根拠は構造上の制約である。

* **doctype 側**：doctype の親は Document だけ（`doctypeParentIsDocument`）で、
  Document は parent を持たない（`documentHasNoParent`）。だから木順で `child` の後ろに
  来る doctype は `child` の兄弟でしかありえない。
* **element 側**：element は木のどこにでもあるので、`child` より前の兄弟の**子孫**が
  element ということがありうる。しかし子を持てるのは
  Document / DocumentFragment / Element だけ（`childrenOnlyUnderContainers`）で、
  Document の子は Document でも DocumentFragment でもない。つまり子孫を持つ兄弟は
  element そのものなので、やはり element の兄弟が前にいることになる。

これで `Dom/Spec/PreInsertValidity.lean` の関係が仕様の字義どおりだと言える。
-/

namespace Dom.Spec

open Dom

/-! ## 祖先についての補助 -/

/-- 祖先を持つ node は parent を持つ。 -/
theorem parentOf_isSome_of_ancestor {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    (parentOf t n).isSome := by
  cases h with
  | step hp => rw [hp]; rfl
  | trans hp _ => rw [hp]; rfl

/-- 祖先は子を持つ。 -/
theorem exists_child_of_ancestor {t : Tree} {a n : NodeId} (h : Ancestor t a n) :
    ∃ c, parentOf t c = some a := by
  induction h with
  | @step x hp => exact ⟨_, hp⟩
  | trans _ _ ih => exact ih

/-- parent が根（parent を持たない）なら、祖先はその parent しかない。 -/
theorem ancestor_eq_of_root_parent {t : Tree} {a n p : NodeId}
    (hn : parentOf t n = some p) (hp : parentOf t p = none) (h : Ancestor t a n) : a = p := by
  cases h with
  | step hq => rw [hn] at hq; exact (Option.some.inj hq).symm
  | trans hq hrest =>
    rw [hn] at hq
    cases hq
    exact absurd (parentOf_isSome_of_ancestor hrest) (by rw [hp]; simp)

/-- 同じ条件の下で、inclusive ancestor で parent を持つものは自分自身しかない。 -/
theorem eq_of_inclusiveAncestor_of_root_parent {t : Tree} {cx c parent p : NodeId}
    (hc : parentOf t c = some parent) (hpar : parentOf t parent = none)
    (hcx : parentOf t cx = some p) (h : InclusiveAncestor t cx c) : cx = c := by
  rcases h with he | ha
  · exact he
  · exfalso
    rw [ancestor_eq_of_root_parent hc hpar ha, hpar] at hcx
    simp at hcx

/-- Document は parent を持たない。 -/
theorem parentOf_eq_none_of_document {t : Tree} (hsv : StructurallyValid t) {n : NodeId}
    {d : NodeData} (hd : t.get? n = some d) (hk : d.kind = .document) :
    parentOf t n = none := by
  rw [parentOf_of_get? hd, hsv.documentHasNoParent n d hd hk]

/-! ## index と分割 -/

/-- 分割の後ろ側にいる子は index が大きい。 -/
theorem index_lt_of_mem_right {t : Tree} (hwf : WellFormed t) {p c d : NodeId}
    {A B : List NodeId} (hL : childrenOf t p = A ++ c :: B) (hnot : c ∉ A) (hd : d ∈ B)
    (hc : parentOf t c = some p) (hdp : parentOf t d = some p) :
    ∃ i j, index t c = some i ∧ index t d = some j ∧ i < j := by
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hc
  have hnd : (childrenOf t p).Nodup := by
    rw [childrenOf_eq hpd]; exact hwf.children_nodup p pd hpd
  obtain ⟨B₁, B₂, hB⟩ := Dom.ListUtil.mem_split hd
  have hL2 : childrenOf t p = (A ++ c :: B₁) ++ d :: B₂ := by rw [hL, hB]; simp
  have hnd2 : ((A ++ c :: B₁) ++ d :: B₂).Nodup := by rw [← hL2]; exact hnd
  have hdnot : d ∉ A ++ c :: B₁ := by
    intro hm
    exact (List.nodup_append.mp hnd2).2.2 d hm d (List.mem_cons_self ..) rfl
  refine ⟨A.length, (A ++ c :: B₁).length,
    (index_eq_some_iff_split hc).mpr ⟨A, B, hL, rfl, hnot⟩,
    (index_eq_some_iff_split hdp).mpr ⟨A ++ c :: B₁, B₂, hL2, rfl, hdnot⟩, ?_⟩
  simp [Nat.lt_succ_of_le]

/-- 分割の前側にいる子は index が小さい。 -/
theorem index_lt_of_mem_left {t : Tree} (hwf : WellFormed t) {p c e : NodeId}
    {A B : List NodeId} (hL : childrenOf t p = A ++ c :: B) (hnot : c ∉ A) (he : e ∈ A)
    (hc : parentOf t c = some p) (hep : parentOf t e = some p) :
    ∃ i j, index t e = some i ∧ index t c = some j ∧ i < j := by
  obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hc
  have hnd : (childrenOf t p).Nodup := by
    rw [childrenOf_eq hpd]; exact hwf.children_nodup p pd hpd
  obtain ⟨A₁, A₂, hA⟩ := Dom.ListUtil.mem_split he
  have hL2 : childrenOf t p = A₁ ++ e :: (A₂ ++ c :: B) := by rw [hL, hA]; simp
  have hnd2 : (A₁ ++ e :: (A₂ ++ c :: B)).Nodup := by rw [← hL2]; exact hnd
  have henot : e ∉ A₁ :=
    fun hm => (List.nodup_append.mp hnd2).2.2 e hm e (List.mem_cons_self ..) rfl
  refine ⟨A₁.length, A.length,
    (index_eq_some_iff_split hep).mpr ⟨A₁, A₂ ++ c :: B, hL2, rfl, henot⟩,
    (index_eq_some_iff_split hc).mpr ⟨A, B, hL, rfl, hnot⟩, ?_⟩
  rw [hA]
  simp

/-! ## doctype 側 -/

/-- doctype の parent は Document で、その Document は parent を持たない。 -/
private theorem doctype_parent_root {t : Tree} (hsv : StructurallyValid t) {d : NodeId}
    {dd : NodeData} (hdd : t.get? d = some dd) (hkd : dd.kind = .documentType)
    {q : NodeId} (hq : parentOf t d = some q) : parentOf t q = none := by
  obtain ⟨qd, hqd⟩ := exists_data_of_parentOf hsv.wellFormed hq
  refine parentOf_eq_none_of_document hsv hqd ?_
  exact hsv.doctypeParentIsDocument d dd hdd hkd q (by rw [← parentOf_of_get? hdd]; exact hq) qd hqd

/--
**step 9 の `following` は、二つの読みで一致する。**

`parent` が Document で `c` がその子であるとき、木順で `c` の後ろに来る doctype は
`c` の後ろの兄弟でしかない。
-/
theorem doctypeFollowing_iff_precedes {t : Tree} (hsv : StructurallyValid t)
    {parent c : NodeId} {pd : NodeData}
    (hpd : t.get? parent = some pd) (hk : pd.kind = .document)
    (hc : parentOf t c = some parent) :
    DoctypeFollowing t parent c ↔ ∃ d, KindIs t d .documentType ∧ PrecedesStruct t c d := by
  have hwf := hsv.wellFormed
  have hpnone : parentOf t parent = none := parentOf_eq_none_of_document hsv hpd hk
  constructor
  · rintro ⟨A, B, hL, hnot, d, hd, hkd⟩
    refine ⟨d, hkd, Or.inr ?_⟩
    have hdp : parentOf t d = some parent :=
      parentOf_of_mem_childrenOf hwf (by rw [hL]; simp [hd])
    obtain ⟨i, j, hi, hj, hij⟩ := index_lt_of_mem_right hwf hL hnot hd hc hdp
    exact ⟨parent, c, d, i, j, hc, hdp, hi, hj, hij, Or.inl rfl, Or.inl rfl⟩
  · rintro ⟨d, hkd, hpre⟩
    obtain ⟨dd, hdd, hkdd⟩ := hkd
    have hdpar : parentOf t d = some parent ∧ ∃ i j, index t c = some i ∧ index t d = some j ∧
        i < j := by
      rcases hpre with ha | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxc, hyd⟩
      · exfalso
        obtain ⟨q, hq⟩ : ∃ q, parentOf t d = some q :=
          Option.isSome_iff_exists.mp (parentOf_isSome_of_ancestor ha)
        have hqn := doctype_parent_root hsv hdd hkdd hq
        rw [ancestor_eq_of_root_parent hq hqn ha, hqn] at hc
        simp at hc
      · have hcyd : cy = d := by
          rcases hyd with he | hay
          · exact he
          · exfalso
            obtain ⟨q, hq⟩ : ∃ q, parentOf t d = some q :=
              Option.isSome_iff_exists.mp (parentOf_isSome_of_ancestor hay)
            have hqn := doctype_parent_root hsv hdd hkdd hq
            rw [ancestor_eq_of_root_parent hq hqn hay, hqn] at hcy
            simp at hcy
        have hcxc : cx = c := eq_of_inclusiveAncestor_of_root_parent hc hpnone hcx hxc
        subst hcxc
        subst hcyd
        rw [hc] at hcx
        have hpe : p = parent := (Option.some.inj hcx).symm
        subst hpe
        exact ⟨hcy, i, j, hi, hj, hij⟩
    obtain ⟨hdp, i, j, hi, hj, hij⟩ := hdpar
    obtain ⟨u, v, hL, hmem⟩ := index_split_lt hwf hc hdp hi hj hij
    obtain ⟨pd', hpd'⟩ := exists_data_of_parentOf hwf hc
    have hnd : (childrenOf t parent).Nodup := by
      rw [childrenOf_eq hpd']; exact hwf.children_nodup parent pd' hpd'
    rw [hL] at hnd
    exact ⟨u, v, hL,
      fun hm => (List.nodup_append.mp hnd).2.2 c hm c (List.mem_cons_self ..) rfl,
      d, hmem, dd, hdd, hkdd⟩

/-! ## element 側 -/

/-- Document の子で、子を持つものは element である。 -/
private theorem element_of_has_child {t : Tree} (hsv : StructurallyValid t)
    {parent cx ch : NodeId} (hcx : parentOf t cx = some parent)
    (hch : parentOf t ch = some cx) : KindIs t cx .element := by
  obtain ⟨cd, hcd⟩ := exists_data_of_parentOf hsv.wellFormed hch
  refine ⟨cd, hcd, ?_⟩
  have hcan : cd.kind.canHaveChildren = true :=
    hsv.canHaveChildren_of_parentOf hch hcd
  -- 子を持てるのは Document / DocumentFragment / Element だけで、
  -- parent を持つので前二つではない。
  cases hkk : cd.kind with
  | document =>
    exfalso
    rw [parentOf_of_get? hcd, hsv.documentHasNoParent cx cd hcd hkk] at hcx
    simp at hcx
  | documentFragment =>
    exfalso
    rw [parentOf_of_get? hcd, hsv.fragmentHasNoParent cx cd hcd hkk] at hcx
    simp at hcx
  | element => rfl
  | _ => rw [hkk] at hcan; simp [NodeKind.canHaveChildren] at hcan

/--
**step 11 の `preceding` も、二つの読みで一致する。**

element は木のどこにでもあるが、`parent` が Document のとき、木順で `c` より前に来る
element は「`c` より前の兄弟」か「その兄弟の子孫」しかない。子孫を持つ兄弟は
子を持てる kind であり、Document の子は Document でも DocumentFragment でもないので
element である。どちらにしても element の兄弟が前にいる。
-/
theorem elementPreceding_iff_precedes {t : Tree} (hsv : StructurallyValid t)
    {parent c : NodeId} {pd : NodeData}
    (hpd : t.get? parent = some pd) (hk : pd.kind = .document)
    (hc : parentOf t c = some parent) :
    ElementPreceding t parent c ↔ ∃ e, KindIs t e .element ∧ PrecedesStruct t e c := by
  have hwf := hsv.wellFormed
  have hpnone : parentOf t parent = none := parentOf_eq_none_of_document hsv hpd hk
  constructor
  · rintro ⟨A, B, hL, hnot, e, he, hke⟩
    refine ⟨e, hke, Or.inr ?_⟩
    have hep : parentOf t e = some parent :=
      parentOf_of_mem_childrenOf hwf (by rw [hL]; simp [he])
    obtain ⟨i, j, hi, hj, hij⟩ := index_lt_of_mem_left hwf hL hnot he hc hep
    exact ⟨parent, e, c, i, j, hep, hc, hi, hj, hij, Or.inl rfl, Or.inl rfl⟩
  · rintro ⟨e, hke, hpre⟩
    rcases hpre with ha | ⟨p, cx, cy, i, j, hcx, hcy, hi, hj, hij, hxe, hyc⟩
    · exfalso
      obtain ⟨ed, hed, hked⟩ := hke
      rw [ancestor_eq_of_root_parent hc hpnone ha] at hed
      rw [hpd] at hed
      cases hed
      rw [hk] at hked
      exact NodeKind.noConfusion hked
    · have hcyc : cy = c := eq_of_inclusiveAncestor_of_root_parent hc hpnone hcy hyc
      have hjc : index t c = some j := by rw [← hcyc]; exact hj
      rw [hcyc, hc] at hcy
      have hpe : p = parent := (Option.some.inj hcy).symm
      have hcxp : parentOf t cx = some parent := by rw [← hpe]; exact hcx
      -- cx は element である
      have hkcx : KindIs t cx .element := by
        rcases hxe with he | hax
        · rw [he]; exact hke
        · obtain ⟨ch, hch⟩ := exists_child_of_ancestor hax
          exact element_of_has_child hsv hcxp hch
      -- cx は c より前の兄弟である
      obtain ⟨u, v, hL, hmem⟩ := index_split_lt hwf hcxp hc hi hjc hij
      obtain ⟨pd', hpd'⟩ := exists_data_of_parentOf hwf hc
      have hnd : (childrenOf t parent).Nodup := by
        rw [childrenOf_eq hpd']; exact hwf.children_nodup parent pd' hpd'
      obtain ⟨v₁, v₂, hv⟩ := Dom.ListUtil.mem_split hmem
      have hL2 : childrenOf t parent = (u ++ cx :: v₁) ++ c :: v₂ := by rw [hL, hv]; simp
      have hnd2 : ((u ++ cx :: v₁) ++ c :: v₂).Nodup := by rw [← hL2]; exact hnd
      refine ⟨u ++ cx :: v₁, v₂, hL2,
        fun hm => (List.nodup_append.mp hnd2).2.2 c hm c (List.mem_cons_self ..) rfl,
        cx, ?_, hkcx⟩
      simp

end Dom.Spec
