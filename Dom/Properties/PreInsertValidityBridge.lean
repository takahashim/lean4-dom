import Dom.Properties.PreInsertValidity
import Dom.Properties.Tree
import Dom.Spec.PreInsertValidity

/-!
# `ensure pre-insert validity` と仕様語彙の validity の一致

`Dom/Spec/PreInsertValidity.lean` が仕様本文から独立に書き写した
`PreInsertValid` / `PreInsertError` が、実行関数 `ensurePreInsertionValidity`
の `.ok` / `.error` と一致することを示す。

関係の側は実行側の名前を触らない。この file が bridge である。
-/

namespace Dom

open Dom.Spec

/-! ## kind の条件 -/

/-- step 1 の kind 条件。 -/
@[simp] theorem canHaveChildren_beq (k : NodeKind) :
    (k == NodeKind.document || k == NodeKind.documentFragment || k == NodeKind.element) =
      k.canHaveChildren := by
  cases k <;> simp [NodeKind.canHaveChildren]

/-- step 4 の kind 条件。 -/
theorem nodeKindOk_beq (k : NodeKind) :
    (k == NodeKind.documentFragment || k == NodeKind.documentType || k == NodeKind.element ||
      k.isCharacterData) = true ↔
      (k = NodeKind.documentFragment ∨ k = NodeKind.documentType ∨ k = NodeKind.element ∨
        k.isCharacterData = true) := by
  cases k <;> simp [NodeKind.isCharacterData]

/-! ## 祖先・child・kind の条件 -/

/-- step 2 の条件。 -/
theorem isInclusiveAncestorOf_eq_false_iff {t : Tree} (hwf : WellFormed t) (a n : NodeId) :
    isInclusiveAncestorOf t a n = false ↔ ¬ InclusiveAncestor t a n := by
  constructor
  · intro h hincl
    have ht : isInclusiveAncestorOf t a n = true := (isInclusiveAncestorOf_iff hwf a n).mpr hincl
    rw [ht] at h
    exact Bool.noConfusion h
  · intro h
    rw [Bool.eq_false_iff]
    intro ht
    exact h ((isInclusiveAncestorOf_iff hwf a n).mp ht)

/-- step 3 の条件（成功側）。 -/
theorem childHasParent_eq_true_iff {t : Tree} {child : Option NodeId} {parent : NodeId} :
    childHasParent t child parent = true ↔
      ∀ c, child = some c → parentOf t c = some parent := by
  cases child with
  | none => simp [childHasParent_none]
  | some c => simp [childHasParent_some_iff]

/-- step 3 の条件（失敗側）。 -/
theorem childHasParent_eq_false_iff {t : Tree} {child : Option NodeId} {parent : NodeId} :
    childHasParent t child parent = false ↔
      ∃ c, child = some c ∧ parentOf t c ≠ some parent := by
  cases child with
  | none => simp [childHasParent_none]
  | some c => simp [childHasParent_some]

/-! ## children の列と kind -/

@[simp] theorem elementChildren_eq_childrenOfKind (t : Tree) (p : NodeId) :
    elementChildren t p = childrenOfKind t p .element := rfl

@[simp] theorem doctypeChildren_eq_childrenOfKind (t : Tree) (p : NodeId) :
    doctypeChildren t p = childrenOfKind t p .documentType := rfl

@[simp] theorem textChildren_eq_textChildrenOf (t : Tree) (p : NodeId) :
    textChildren t p = textChildrenOf t p := rfl

/-- `excl` に無いものを一つも含まない。 -/
theorem any_not_contains_eq_false_iff {l excl : List NodeId} :
    (l.any (fun c => !excl.contains c)) = false ↔ ∀ c, c ∈ l → c ∈ excl := by
  rw [List.any_eq_false]
  constructor
  · intro h c hc
    simpa using h c hc
  · intro h c hc
    simpa using h c hc

/-- `excl` に無いものを含む。 -/
theorem any_not_contains_eq_true_iff {l excl : List NodeId} :
    (l.any (fun c => !excl.contains c)) = true ↔ ∃ c, c ∈ l ∧ c ∉ excl := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hq⟩
    exact ⟨c, hc, by simpa using hq⟩
  · rintro ⟨c, hc, hq⟩
    exact ⟨c, hc, by simpa using hq⟩

/-- `doctypeFollows` と仕様語彙 `HasKindAfter` の一致。 -/
theorem doctypeFollows_eq_true_iff {t : Tree} {parent c : NodeId} :
    doctypeFollows t parent c = true ↔ HasKindAfter t parent c .documentType := by
  unfold doctypeFollows HasKindAfter
  cases Dom.ListUtil.splitAt? (childrenOf t parent) c with
  | none => simp
  | some p =>
    obtain ⟨before, after⟩ := p
    simp [List.any_eq_true]

/-- `elementPrecedes` と仕様語彙 `HasKindBefore` の一致。 -/
theorem elementPrecedes_eq_true_iff {t : Tree} {parent c : NodeId} :
    elementPrecedes t parent c = true ↔ HasKindBefore t parent c .element := by
  unfold elementPrecedes HasKindBefore
  cases Dom.ListUtil.splitAt? (childrenOf t parent) c with
  | none => simp
  | some p =>
    obtain ⟨before, after⟩ := p
    simp [List.any_eq_true]

/-- `doctypeFollows` と仕様語彙 `HasKindAfter` の一致（失敗側）。 -/
theorem doctypeFollows_eq_false_iff {t : Tree} {parent c : NodeId} :
    doctypeFollows t parent c = false ↔ ¬ HasKindAfter t parent c .documentType := by
  constructor
  · intro h hh
    rw [(doctypeFollows_eq_true_iff (t := t) (parent := parent) (c := c)).mpr hh] at h
    exact Bool.noConfusion h
  · intro h
    rw [Bool.eq_false_iff]
    intro ht
    exact h ((doctypeFollows_eq_true_iff (t := t) (parent := parent) (c := c)).mp ht)

/-- `elementPrecedes` と仕様語彙 `HasKindBefore` の一致（失敗側）。 -/
theorem elementPrecedes_eq_false_iff {t : Tree} {parent c : NodeId} :
    elementPrecedes t parent c = false ↔ ¬ HasKindBefore t parent c .element := by
  constructor
  · intro h hh
    rw [(elementPrecedes_eq_true_iff (t := t) (parent := parent) (c := c)).mpr hh] at h
    exact Bool.noConfusion h
  · intro h
    rw [Bool.eq_false_iff]
    intro ht
    exact h ((elementPrecedes_eq_true_iff (t := t) (parent := parent) (c := c)).mp ht)

/-! ## step 8.2 / 9 の部分検査 -/

theorem checkElementInsertion_ok_iff {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} :
    checkElementInsertion t parent child excl = .ok () ↔
      ElementInsertionOk t parent child excl := by
  unfold checkElementInsertion ElementInsertionOk
  rw [elementChildren_eq_childrenOfKind]
  cases child with
  | none =>
    dsimp only
    by_cases hany : (childrenOfKind t parent .element).any (fun c => !excl.contains c) = true
    · rw [if_pos hany]
      refine iff_of_false (by simp) ?_
      rintro ⟨hall, -⟩
      obtain ⟨e, he, hne⟩ := any_not_contains_eq_true_iff.mp hany
      exact hne (hall e he)
    · rw [if_neg hany]
      exact iff_of_true (by simp)
        ⟨any_not_contains_eq_false_iff.mp (by simpa [Bool.not_eq_true] using hany), trivial⟩
  | some c =>
    dsimp only
    by_cases hany : (childrenOfKind t parent .element).any (fun c => !excl.contains c) = true
    · rw [if_pos hany]
      refine iff_of_false (by simp) ?_
      rintro ⟨hall, -⟩
      obtain ⟨e, he, hne⟩ := any_not_contains_eq_true_iff.mp hany
      exact hne (hall e he)
    · rw [if_neg hany]
      have hall := any_not_contains_eq_false_iff.mp (by simpa [Bool.not_eq_true] using hany)
      by_cases hdf : doctypeFollows t parent c = true
      · rw [if_pos hdf]
        refine iff_of_false (by simp) ?_
        rintro ⟨-, hna, -⟩
        exact hna ((doctypeFollows_eq_true_iff (t := t) (parent := parent) (c := c)).mp hdf)
      · have hna : ¬ HasKindAfter t parent c .documentType := by
          intro hh
          exact hdf ((doctypeFollows_eq_true_iff (t := t) (parent := parent) (c := c)).mpr hh)
        rw [if_neg hdf]
        by_cases hcd : (kindOf t c == some .documentType && !excl.contains c) = true
        · rw [if_pos hcd]
          refine iff_of_false (by simp) ?_
          rintro ⟨-, -, hmem⟩
          simp only [Bool.and_eq_true] at hcd
          obtain ⟨hk, hnc⟩ := hcd
          have hkc : kindOf t c = some NodeKind.documentType := by simpa using hk
          exact (by simpa using hnc : c ∉ excl) (hmem hkc)
        · rw [if_neg hcd]
          refine iff_of_true (by simp) ⟨hall, hna, ?_⟩
          intro hkc
          by_cases hc : c ∈ excl
          · exact hc
          · exfalso
            have hcont : excl.contains c = false := by simpa using hc
            have hkb : (kindOf t c == some NodeKind.documentType) = true := by simpa using hkc
            have hboth : (kindOf t c == some NodeKind.documentType && !excl.contains c) = true := by
              rw [hkb, hcont]; rfl
            exact hcd hboth

/-! ## step 10-11 の部分検査 -/

theorem checkDoctypeInsertion_ok_iff {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} :
    checkDoctypeInsertion t parent child excl = .ok () ↔
      DoctypeInsertionOk t parent child excl := by
  unfold checkDoctypeInsertion DoctypeInsertionOk
  rw [doctypeChildren_eq_childrenOfKind]
  cases child with
  | none =>
    dsimp only
    by_cases hany : (childrenOfKind t parent .documentType).any
        (fun c => !excl.contains c) = true
    · rw [if_pos hany]
      refine iff_of_false (by simp) ?_
      rintro ⟨hall, -⟩
      obtain ⟨d, hd, hne⟩ := any_not_contains_eq_true_iff.mp hany
      exact hne (hall d hd)
    · rw [if_neg hany]
      have hall := any_not_contains_eq_false_iff.mp (by simpa [Bool.not_eq_true] using hany)
      rw [elementChildren_eq_childrenOfKind]
      by_cases hele : (childrenOfKind t parent .element).any
          (fun c => !excl.contains c) = true
      · rw [if_pos hele]
        refine iff_of_false (by simp) ?_
        rintro ⟨-, hmem⟩
        obtain ⟨e, he, hne⟩ := any_not_contains_eq_true_iff.mp hele
        exact hne (hmem e he)
      · rw [if_neg hele]
        exact iff_of_true (by simp) ⟨hall,
          any_not_contains_eq_false_iff.mp (by simpa [Bool.not_eq_true] using hele)⟩
  | some c =>
    dsimp only
    by_cases hany : (childrenOfKind t parent .documentType).any
        (fun c => !excl.contains c) = true
    · rw [if_pos hany]
      refine iff_of_false (by simp) ?_
      rintro ⟨hall, -⟩
      obtain ⟨d, hd, hne⟩ := any_not_contains_eq_true_iff.mp hany
      exact hne (hall d hd)
    · rw [if_neg hany]
      have hall := any_not_contains_eq_false_iff.mp (by simpa [Bool.not_eq_true] using hany)
      by_cases hep : elementPrecedes t parent c = true
      · rw [if_pos hep]
        refine iff_of_false (by simp) ?_
        rintro ⟨-, hna⟩
        exact hna ((elementPrecedes_eq_true_iff (t := t) (parent := parent) (c := c)).mp hep)
      · rw [if_neg hep]
        refine iff_of_true (by simp) ⟨hall, ?_⟩
        intro hh
        exact hep ((elementPrecedes_eq_true_iff (t := t) (parent := parent) (c := c)).mpr hh)

/-- `checkElementInsertion` が返す例外は `hierarchyRequestError` だけである。 -/
theorem checkElementInsertion_error_eq {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} {e : DOMException}
    (h : checkElementInsertion t parent child excl = .error e) : e = .hierarchyRequestError := by
  unfold checkElementInsertion at h
  rw [elementChildren_eq_childrenOfKind] at h
  cases child with
  | none =>
    dsimp only at h
    cases hb : ((childrenOfKind t parent .element).any (fun c => !excl.contains c)) with
    | false => rw [hb] at h; simp at h
    | true => rw [hb] at h; exact (Except.error.inj h).symm
  | some c =>
    dsimp only at h
    cases hb : ((childrenOfKind t parent .element).any (fun c => !excl.contains c)) with
    | false =>
      rw [hb] at h
      cases hb2 : doctypeFollows t parent c with
      | true => rw [hb2] at h; exact (Except.error.inj h).symm
      | false =>
        rw [hb2] at h
        cases hb3 : (kindOf t c == some .documentType && !excl.contains c) with
        | true => rw [hb3] at h; exact (Except.error.inj h).symm
        | false => rw [hb3] at h; simp at h
    | true => rw [hb] at h; exact (Except.error.inj h).symm

/-- `checkDoctypeInsertion` が返す例外は `hierarchyRequestError` だけである。 -/
theorem checkDoctypeInsertion_error_eq {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} {e : DOMException}
    (h : checkDoctypeInsertion t parent child excl = .error e) : e = .hierarchyRequestError := by
  unfold checkDoctypeInsertion at h
  rw [doctypeChildren_eq_childrenOfKind, elementChildren_eq_childrenOfKind] at h
  cases child with
  | none =>
    dsimp only at h
    cases hb : ((childrenOfKind t parent .documentType).any (fun c => !excl.contains c)) with
    | false =>
      rw [hb] at h
      cases hb2 : ((childrenOfKind t parent .element).any (fun c => !excl.contains c)) with
      | true => rw [hb2] at h; exact (Except.error.inj h).symm
      | false => rw [hb2] at h; simp at h
    | true => rw [hb] at h; exact (Except.error.inj h).symm
  | some c =>
    dsimp only at h
    cases hb : ((childrenOfKind t parent .documentType).any (fun c => !excl.contains c)) with
    | false =>
      rw [hb] at h
      cases hb2 : elementPrecedes t parent c with
      | true => rw [hb2] at h; exact (Except.error.inj h).symm
      | false => rw [hb2] at h; simp at h
    | true => rw [hb] at h; exact (Except.error.inj h).symm

/-- 仕様語彙の側から `checkElementInsertion` の失敗が出る。 -/
theorem checkElementInsertion_error_of_not_ok {t : Tree} {parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (hne : ¬ ElementInsertionOk t parent child excl) :
    checkElementInsertion t parent child excl = .error .hierarchyRequestError := by
  cases hx : checkElementInsertion t parent child excl with
  | ok u =>
    cases u
    exact absurd ((checkElementInsertion_ok_iff (t := t) (parent := parent)
      (child := child) (excl := excl)).mp hx) hne
  | error e => exact congrArg Except.error (checkElementInsertion_error_eq hx)

/-- 仕様語彙の側から `checkDoctypeInsertion` の失敗が出る。 -/
theorem checkDoctypeInsertion_error_of_not_ok {t : Tree} {parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (hne : ¬ DoctypeInsertionOk t parent child excl) :
    checkDoctypeInsertion t parent child excl = .error .hierarchyRequestError := by
  cases hx : checkDoctypeInsertion t parent child excl with
  | ok u =>
    cases u
    exact absurd ((checkDoctypeInsertion_ok_iff (t := t) (parent := parent)
      (child := child) (excl := excl)).mp hx) hne
  | error e => exact congrArg Except.error (checkDoctypeInsertion_error_eq hx)

/-! ## 全体：`.ok` との一致 -/

/-- `.ok` から仕様語彙の validity が出る。 -/
theorem valid_of_ensurePreInsertionValidity_ok {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} (hwf : WellFormed t)
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    PreInsertValid t node parent child excl := by
  obtain ⟨pd, nd, hpd, hnd, h1, h2, h3, h4, h5⟩ := ensurePreInsertionValidity_ok_steps h
  have hcanHave : pd.kind.canHaveChildren = true := by rw [← canHaveChildren_beq]; exact h1
  have hanc : ¬ InclusiveAncestor t node parent :=
    (isInclusiveAncestorOf_eq_false_iff hwf node parent).mp h2
  have hchild := childHasParent_eq_true_iff.mp h3
  have hkind := (nodeKindOk_beq nd.kind).mp h4
  have hdt : PreDoctypeParentOk pd nd := by
    intro hk
    by_cases hdoc : pd.kind = NodeKind.document
    · exact hdoc
    · exact absurd (by simpa using h5 hdoc) (by simp [hk])
  by_cases hpdoc : pd.kind = NodeKind.document
  · obtain ⟨htext, hfrag, hele, hdoct⟩ :=
      ensurePreInsertionValidity_documentFacts hpd hnd hpdoc h
    refine ⟨pd, nd, hpd, hnd, hcanHave, hanc, hchild, hkind, hdt, ?_, ?_⟩
    · intro _; exact htext
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · intro hkf
        obtain ⟨hlen, htxt⟩ := hfrag hkf
        exact ⟨by simpa using hlen, by simpa using htxt⟩
      · intro hcase
        obtain ⟨hall, hc⟩ := hele hcase
        cases child with
        | none => exact ⟨by simpa using hall, trivial⟩
        | some c =>
          obtain ⟨hor, hdf⟩ := hc c rfl
          refine ⟨by simpa using hall, doctypeFollows_eq_false_iff.mp hdf, ?_⟩
          intro hk
          rcases hor with hf | hm
          · exact absurd (by simpa using hk : (kindOf t c == some NodeKind.documentType) = true)
              (by simp [hf])
          · exact hm
      · intro hkdt
        obtain ⟨hdhall, hprec, hnone⟩ := hdoct hkdt
        cases child with
        | none => exact ⟨by simpa using hdhall, by simpa using hnone rfl⟩
        | some c =>
          refine ⟨by simpa using hdhall, ?_⟩
          exact elementPrecedes_eq_false_iff.mp (hprec c rfl)
  · refine ⟨pd, nd, hpd, hnd, hcanHave, hanc, hchild, hkind, hdt, ?_, ?_⟩
    · intro hc; exact absurd hc hpdoc
    · intro hc; exact absurd hc hpdoc

/--
step 1-4 を通るなら、親が Document でない限り step 5.2 で `ok` になる。
仕様語彙の側から実行関数の `.ok` を出す逆向きの bridge の前段である。
-/
theorem ensurePreInsertionValidity_ok_of_valid {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} (hwf : WellFormed t)
    (hv : PreInsertValid t node parent child excl) :
    ensurePreInsertionValidity t node parent child excl = .ok () := by
  obtain ⟨pd, nd, hcore⟩ := hv
  obtain ⟨hpd, hnd, hk, hanc, hchild, hkind, hdt, hnotext, hdoc⟩ := hcore
  have hancB : isInclusiveAncestorOf t node parent = false :=
    (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
  have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
  have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
      pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
  have hkindB : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
      nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
    (nodeKindOk_beq nd.kind).mpr hkind
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
    if_neg (by simp [hkindB])]
  by_cases hpdoc : pd.kind = NodeKind.document
  · rw [if_neg (by simp [hpdoc])]
    rw [if_neg (by simp [hnotext hpdoc])]
    by_cases hcd : nd.kind.isCharacterData = true
    · rw [if_pos hcd]
    · rw [if_neg hcd]
      by_cases hfrag : (nd.kind == NodeKind.documentFragment) = true
      · rw [if_pos hfrag]
        have hkf : nd.kind = NodeKind.documentFragment := by simpa using hfrag
        obtain ⟨hlen, htxt⟩ := (hdoc hpdoc).1 hkf
        rw [elementChildren_eq_childrenOfKind, textChildren_eq_textChildrenOf]
        have htxt' : (textChildrenOf t node).isEmpty = true := by simp [htxt]
        have hlen' : ¬ 1 < (childrenOfKind t node .element).length := by omega
        rw [if_neg (by simp [hlen', htxt'])]
        by_cases hemp : (childrenOfKind t node .element).isEmpty = true
        · rw [if_pos hemp]
        · rw [if_neg hemp]
          have hne : childrenOfKind t node .element ≠ [] := by
            simpa [List.isEmpty_iff] using hemp
          exact (checkElementInsertion_ok_iff (t := t) (parent := parent) (child := child)
            (excl := excl)).mpr ((hdoc hpdoc).2.1 (Or.inr ⟨hkf, hne⟩))
      · rw [if_neg hfrag]
        by_cases helem : (nd.kind == NodeKind.element) = true
        · rw [if_pos helem]
          have hke : nd.kind = NodeKind.element := by simpa using helem
          exact (checkElementInsertion_ok_iff (t := t) (parent := parent) (child := child)
            (excl := excl)).mpr ((hdoc hpdoc).2.1 (Or.inl hke))
        · rw [if_neg helem]
          have hkdt : nd.kind = NodeKind.documentType := by
            rcases hkind with h | h | h | h
            · exact absurd (by simpa using h) hfrag
            · exact h
            · exact absurd (by simpa using h) helem
            · exact absurd h hcd
          exact (checkDoctypeInsertion_ok_iff (t := t) (parent := parent) (child := child)
            (excl := excl)).mpr ((hdoc hpdoc).2.2 hkdt)
  · rw [if_pos (by simpa using hpdoc)]
    rw [if_neg (by simp [show nd.kind ≠ NodeKind.documentType from fun heq => hpdoc (hdt heq)])]

/-- **`.ok` と仕様語彙の validity は一致する。** -/
theorem ensurePreInsertionValidity_ok_iff {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} (hwf : WellFormed t) :
    ensurePreInsertionValidity t node parent child excl = .ok () ↔
      PreInsertValid t node parent child excl :=
  ⟨valid_of_ensurePreInsertionValidity_ok hwf,
    ensurePreInsertionValidity_ok_of_valid hwf⟩

/--
**仕様語彙の側から実行関数の `.error` が出る。**

優先順位は `PreInsertError` の枝が先の step を通ることを前提に持つことで表されており、
各枝で `ensurePreInsertionValidity` がその例外で落ちることを直接示す。
-/
theorem ensurePreInsertionValidity_error_of_preInsertError {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {e : DOMException} (hwf : WellFormed t)
    (he : PreInsertError t node parent child excl e) :
    ensurePreInsertionValidity t node parent child excl = .error e := by
  rcases he with ⟨hp, rfl⟩ | ⟨pd, hp, hn, rfl⟩ |
    ⟨pd, nd, hp, hn, hk, rfl⟩ | ⟨pd, nd, hbase, hanc, rfl⟩ |
    ⟨pd, nd, hbase, hnanc, hc, rfl⟩ | ⟨pd, nd, hP123, hne, rfl⟩ |
    ⟨pd, nd, hP1234, hne, rfl⟩ | ⟨pd, nd, hP12345, hne, rfl⟩ |
    ⟨pd, nd, hP123456, hpdoc, hkf, hsize, rfl⟩ |
    ⟨pd, nd, hP123456, hpdoc, hkindcase, hne, rfl⟩ |
    ⟨pd, nd, hP123456, hpdoc, hkdt, hne, rfl⟩
  · simp [ensurePreInsertionValidity, hp]
  · simp [ensurePreInsertionValidity, hp, hn]
  · exact ensurePreInsertionValidity_step1 hp hn hk
  · obtain ⟨hp', hn', hk⟩ := hbase
    exact ensurePreInsertionValidity_step2 hp' hn' hk
      ((isInclusiveAncestorOf_iff hwf node parent).mpr hanc)
  · obtain ⟨hp', hn', hk⟩ := hbase
    exact ensurePreInsertionValidity_step3 hp' hn' hk
      ((isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hnanc)
      (childHasParent_eq_false_iff.mpr hc)
  · obtain ⟨⟨hp', hn', hk⟩, hanc, hchild⟩ := hP123
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4 : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      exact hne ((nodeKindOk_beq nd.kind).mp ht)
    unfold ensurePreInsertionValidity
    rw [hp', hn']
    simp only
    rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
      if_pos (by simp [hC4])]
  · obtain ⟨⟨⟨hp', hn', hk⟩, hanc, hchild⟩, hkk⟩ := hP1234
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4t : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
      (nodeKindOk_beq nd.kind).mpr hkk
    have hkdt : nd.kind = NodeKind.documentType := by
      by_cases h : nd.kind = NodeKind.documentType
      · exact h
      · exfalso; exact hne (fun hh => absurd hh h)
    have hpne : pd.kind ≠ NodeKind.document := fun hh => hne (fun _ => hh)
    unfold ensurePreInsertionValidity
    rw [hp', hn']
    simp only
    rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
      if_neg (by simp [hC4t]), if_pos (by simp [hpne]),
      if_pos (by simp [show (nd.kind == NodeKind.documentType) = true from by simpa using hkdt])]
  · obtain ⟨⟨⟨⟨hp', hn', hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩ := hP12345
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4t : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
      (nodeKindOk_beq nd.kind).mpr hkk
    have hpdoc' : pd.kind = NodeKind.document := by
      by_cases h : pd.kind = NodeKind.document
      · exact h
      · exfalso; exact hne (fun hh => absurd hh h)
    have htext : nd.kind.isText = true := by
      by_cases h : nd.kind.isText = true
      · exact h
      · exfalso; exact hne (fun _ => by simpa using h)
    unfold ensurePreInsertionValidity
    rw [hp', hn']
    simp only
    rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
      if_neg (by simp [hC4t]), if_neg (by simp [hpdoc']), if_pos (by simpa using htext)]
  · obtain ⟨⟨⟨⟨⟨hp', hn', hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩, hnotext⟩ := hP123456
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4t : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
      (nodeKindOk_beq nd.kind).mpr hkk
    have htext : nd.kind.isText = false := hnotext hpdoc
    have hsizeB : (1 < (elementChildren t node).length || !(textChildren t node).isEmpty) = true := by
      rw [elementChildren_eq_childrenOfKind, textChildren_eq_textChildrenOf]
      rcases hsize with h | h
      · simp [h]
      · have : (textChildrenOf t node).isEmpty = false := by simp [h]
        simp [this]
    unfold ensurePreInsertionValidity
    rw [hp', hn']
    simp only
    rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
      if_neg (by simp [hC4t]), if_neg (by simp [hpdoc]), if_neg (by simp [htext]),
      if_neg (by simp [show nd.kind.isCharacterData = false by rw [hkf]; rfl]),
      if_pos (by simp [show (nd.kind == NodeKind.documentFragment) = true by simpa using hkf]),
      if_pos hsizeB]
  · obtain ⟨⟨⟨⟨⟨hp', hn', hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩, hnotext⟩ := hP123456
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4t : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
      (nodeKindOk_beq nd.kind).mpr hkk
    have htext : nd.kind.isText = false := hnotext hpdoc
    have hcd : nd.kind.isCharacterData = false := by
      rcases hkindcase with h | ⟨h, -⟩ <;> rw [h] <;> rfl
    rcases hkindcase with hke | ⟨hkf, hne'⟩
    · unfold ensurePreInsertionValidity
      rw [hp', hn']
      simp only
      rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
        if_neg (by simp [hC4t]), if_neg (by simp [hpdoc]), if_neg (by simp [htext]),
        if_neg (by simp [hcd]),
        if_neg (by simp [show (nd.kind == NodeKind.documentFragment) = false by rw [hke]; rfl]),
        if_pos (by simp [show (nd.kind == NodeKind.element) = true by rw [hke]; rfl])]
      exact checkElementInsertion_error_of_not_ok hne
    · unfold ensurePreInsertionValidity
      rw [hp', hn']
      simp only
      rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
        if_neg (by simp [hC4t]), if_neg (by simp [hpdoc]), if_neg (by simp [htext]),
        if_neg (by simp [hcd]),
        if_pos (by simp [show (nd.kind == NodeKind.documentFragment) = true by rw [hkf]; rfl])]
      have hemp : (childrenOfKind t node .element).isEmpty = false := by
        simpa [Bool.eq_false_iff, List.isEmpty_iff] using hne'
      by_cases h81 : (1 < (elementChildren t node).length ||
          !(textChildren t node).isEmpty) = true
      · rw [if_pos h81]
      · rw [if_neg h81]
        rw [elementChildren_eq_childrenOfKind]
        rw [if_neg (by simpa using hemp)]
        exact checkElementInsertion_error_of_not_ok hne
  · obtain ⟨⟨⟨⟨⟨hp', hn', hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩, hnotext⟩ := hP123456
    have hkB : (pd.kind == NodeKind.document || pd.kind == NodeKind.documentFragment ||
        pd.kind == NodeKind.element) = true := by rw [canHaveChildren_beq]; exact hk
    have hancB : isInclusiveAncestorOf t node parent = false :=
      (isInclusiveAncestorOf_eq_false_iff hwf node parent).mpr hanc
    have hchildB : childHasParent t child parent = true := childHasParent_eq_true_iff.mpr hchild
    have hC4t : (nd.kind == NodeKind.documentFragment || nd.kind == NodeKind.documentType ||
        nd.kind == NodeKind.element || nd.kind.isCharacterData) = true :=
      (nodeKindOk_beq nd.kind).mpr hkk
    have htext : nd.kind.isText = false := hnotext hpdoc
    unfold ensurePreInsertionValidity
    rw [hp', hn']
    simp only
    rw [if_neg (by simp [hkB]), if_neg (by simp [hancB]), if_neg (by simp [hchildB]),
      if_neg (by simp [hC4t]), if_neg (by simp [hpdoc]), if_neg (by simp [htext]),
      if_neg (by simp [show nd.kind.isCharacterData = false by rw [hkdt]; rfl]),
      if_neg (by simp [show (nd.kind == NodeKind.documentFragment) = false by rw [hkdt]; rfl]),
      if_neg (by simp [show (nd.kind == NodeKind.element) = false by rw [hkdt]; rfl])]
    exact checkDoctypeInsertion_error_of_not_ok hne

/-- **`PreInsertError` は validity が失敗するとき必ず成り立つ。** -/
theorem preInsertError_of_not_valid {t : Tree} {node parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : ¬ PreInsertValid t node parent child excl) :
    ∃ e, PreInsertError t node parent child excl e := by
  cases hpp : t.get? parent with
  | none => exact ⟨_, Or.inl ⟨hpp, rfl⟩⟩
  | some pd =>
    cases hnn : t.get? node with
    | none => exact ⟨_, Or.inr (Or.inl ⟨pd, hpp, hnn, rfl⟩)⟩
    | some nd =>
      have hcore : ¬ PreInsertValidCore t node parent child excl pd nd :=
        fun hc => h ⟨pd, nd, hc⟩
      by_cases hk : pd.kind.canHaveChildren = true
      · by_cases hanc : ¬ InclusiveAncestor t node parent
        · by_cases hchild : ∀ c, child = some c → parentOf t c = some parent
          · by_cases hkk : PreNodeKindOk nd
            · by_cases hdtp : PreDoctypeParentOk pd nd
              · by_cases hnt : PreNoTextInDocument pd nd
                · have hdocnot : ¬ (pd.kind = NodeKind.document →
                      PreInsertDocumentOk t node parent child excl pd nd) :=
                    fun hc => hcore ⟨hpp, hnn, hk, hanc, hchild, hkk, hdtp, hnt, hc⟩
                  obtain ⟨hpdoc, hnotok⟩ := Classical.not_imp.mp hdocnot
                  have hP123456 : PreP123456 t node parent child pd nd := ⟨⟨⟨⟨⟨hpp, hnn, hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩, hnt⟩
                  by_cases hA : (nd.kind = NodeKind.documentFragment →
                      (childrenOfKind t node NodeKind.element).length ≤ 1 ∧
                        textChildrenOf t node = [])
                  · by_cases hB : ((nd.kind = NodeKind.element ∨
                        (nd.kind = NodeKind.documentFragment ∧
                          childrenOfKind t node NodeKind.element ≠ [])) →
                        ElementInsertionOk t parent child excl)
                    · have hC : ¬ (nd.kind = NodeKind.documentType →
                          DoctypeInsertionOk t parent child excl) :=
                        fun hc => hnotok ⟨hA, hB, hc⟩
                      obtain ⟨hkdt, hne⟩ := Classical.not_imp.mp hC
                      exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨pd, nd, hP123456, hpdoc, hkdt, hne, rfl⟩))))))))))⟩
                    · obtain ⟨hcase, hne⟩ := Classical.not_imp.mp hB
                      exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, hP123456, hpdoc, hcase, hne, rfl⟩)))))))))⟩
                  · obtain ⟨hkf, hsize⟩ := Classical.not_imp.mp hA
                    have hsize' : 1 < (childrenOfKind t node NodeKind.element).length ∨
                        textChildrenOf t node ≠ [] := by
                      by_cases h1 : 1 < (childrenOfKind t node NodeKind.element).length
                      · exact Or.inl h1
                      · exact Or.inr (fun htext => hsize ⟨by omega, htext⟩)
                    exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, hP123456, hpdoc, hkf, hsize', rfl⟩))))))))⟩
                · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, ⟨⟨⟨⟨⟨hpp, hnn, hk⟩, hanc, hchild⟩, hkk⟩, hdtp⟩, hnt, rfl⟩⟩)))))))⟩
              · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, ⟨⟨⟨⟨hpp, hnn, hk⟩, hanc, hchild⟩, hkk⟩, hdtp, rfl⟩⟩))))))⟩
            · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, ⟨⟨⟨hpp, hnn, hk⟩, hanc, hchild⟩, hkk, rfl⟩⟩)))))⟩
          · have hcex : ∃ c, child = some c ∧ parentOf t c ≠ some parent := by
              obtain ⟨c, hc⟩ := Classical.not_forall.mp hchild
              obtain ⟨hcs, hne⟩ := Classical.not_imp.mp hc
              exact ⟨c, hcs, hne⟩
            exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, ⟨hpp, hnn, hk⟩, hanc, hcex, rfl⟩))))⟩
        · have hinc : InclusiveAncestor t node parent := by
            by_cases hh : InclusiveAncestor t node parent
            · exact hh
            · exact absurd hh hanc
          exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ⟨pd, nd, ⟨hpp, hnn, hk⟩, hinc, rfl⟩)))⟩
      · have hkf : pd.kind.canHaveChildren = false := by
          cases h : pd.kind.canHaveChildren <;> simp_all
        exact ⟨_, Or.inr (Or.inr (Or.inl ⟨pd, nd, hpp, hnn, hkf, rfl⟩))⟩

/-- **実行関数の `.error` から仕様語彙の error 関係が出る。** -/
theorem preInsertError_of_ensurePreInsertionValidity_error {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {e : DOMException} (hwf : WellFormed t)
    (h : ensurePreInsertionValidity t node parent child excl = .error e) :
    PreInsertError t node parent child excl e := by
  have hnv : ¬ PreInsertValid t node parent child excl := fun hok => by
    rw [(ensurePreInsertionValidity_ok_iff hwf).mpr hok] at h
    simp at h
  obtain ⟨e', he'⟩ := preInsertError_of_not_valid hnv
  have h' := ensurePreInsertionValidity_error_of_preInsertError hwf he'
  rw [h] at h'
  rw [← Except.error.inj h'] at he'
  exact he'

/-- **`.error` と仕様語彙の error 関係は一致する。** -/
theorem ensurePreInsertionValidity_error_iff {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {e : DOMException} (hwf : WellFormed t) :
    ensurePreInsertionValidity t node parent child excl = .error e ↔
      PreInsertError t node parent child excl e :=
  ⟨preInsertError_of_ensurePreInsertionValidity_error hwf,
    ensurePreInsertionValidity_error_of_preInsertError hwf⟩

end Dom
