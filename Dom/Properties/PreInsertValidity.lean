import Dom.Mutation.Algorithms

/-!
# `ensure pre-insertion validity` の interface

`ensurePreInsertionValidity` は DOM Standard §4.2.3 の step 1-11 をそのまま
書き下した長い if 連鎖である。本体を開くのはこの file だけにして、
使う側は以下の四方向の補題だけを見る。

* 取り出す：`ensurePreInsertionValidity_ok_steps`（`.ok` から step 1-5 の事実）
* 作る：`ensurePreInsertionValidity_fresh`（全 step を満たすなら `.ok`）
* 順序：`ensurePreInsertionValidity_step1` / `_step2` / `_step3`
  （先に落ちる step が後の step より優先すること）
* `child` に関する congruence：`ensurePreInsertionValidity_child_congr`
-/

namespace Dom

/-- `!b` が真でないなら `b` は真。 -/
private theorem of_not_not_eq_true {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b with
  | true => rfl
  | false => simp at h

/-! ## 取り出す -/

/--
`.ok` から step 1-5 が保証する事実をまとめて取り出す。

個別の事実（parent の kind、循環の否定、reference child の parent、
node の kind、doctype の parent）はすべてこれから導く。
-/
theorem ensurePreInsertionValidity_ok_steps {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId}
    (h : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∃ pd nd, t.get? parent = some pd ∧ t.get? node = some nd ∧
      -- step 1
      (pd.kind == .document || pd.kind == .documentFragment || pd.kind == .element) = true ∧
      -- step 2
      isInclusiveAncestorOf t node parent = false ∧
      -- step 3
      childHasParent t child parent = true ∧
      -- step 4
      (nd.kind == .documentFragment || nd.kind == .documentType ||
        nd.kind == .element || nd.kind.isCharacterData) = true ∧
      -- step 5
      (pd.kind ≠ .document → ¬ (nd.kind == .documentType) = true) := by
  unfold ensurePreInsertionValidity at h
  split at h
  · simp at h
  · next pd hpd =>
    split at h
    · simp at h
    · next nd hnd =>
      split at h
      · simp at h
      · next h1 =>
        split at h
        · simp at h
        · next h2 =>
          split at h
          · simp at h
          · next h3 =>
            split at h
            · simp at h
            · next h4 =>
              refine ⟨pd, nd, hpd, hnd, of_not_not_eq_true h1, by simpa using h2,
                of_not_not_eq_true h3, of_not_not_eq_true h4, ?_⟩
              intro hpk
              rw [if_pos hpk] at h
              split at h
              · simp at h
              · next h5 => exact h5

/-! ## 作る -/

/--
作ったばかりの node（parent も children も持たない）を parent の末尾に入れるときの
pre-insert validity。

`child` が null なので step 3 は自明で、step 8 の DocumentFragment の枝も通らない。
残るのは step 1（parent の kind）・step 2（循環）・step 4（node の kind）・
step 5（doctype の parent）・step 6（Document に Text）・
step 9 と step 11（Document の children の制約）である。
-/
theorem ensurePreInsertionValidity_fresh {t : Tree} {node parent : NodeId} {pd nd : NodeData}
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hpk : pd.kind.canHaveChildren = true)
    (hanc : isInclusiveAncestorOf t node parent = false)
    (hnk : nd.kind ≠ .document) (hnf : nd.kind ≠ .documentFragment)
    (hdt : nd.kind = .documentType → pd.kind = .document)
    (hdocText : pd.kind = .document → nd.kind.isText = false)
    (hdocElem : pd.kind = .document → nd.kind = .element → elementChildren t parent = [])
    (hdocDoctype : pd.kind = .document → nd.kind = .documentType →
      doctypeChildren t parent = [] ∧ elementChildren t parent = []) :
    ensurePreInsertionValidity t node parent none [] = .ok () := by
  unfold ensurePreInsertionValidity
  split
  · next h => rw [h] at hpd; simp at hpd
  · next pd' hpd' =>
    rw [hpd'] at hpd
    cases hpd
    split
    · next h => rw [h] at hnd; simp at hnd
    · next nd' hnd' =>
      rw [hnd'] at hnd
      cases hnd
      -- step 1
      split
      · next hbad =>
        exfalso
        cases hk : pd.kind <;> rw [hk] at hpk hbad <;> simp_all [NodeKind.canHaveChildren]
      -- step 2
      · split
        · next hbad => rw [hanc] at hbad; simp at hbad
        -- step 3
        · split
          · next hbad => simp [childHasParent] at hbad
          -- step 4
          · split
            · next hbad =>
              exfalso
              cases hk : nd.kind <;> rw [hk] at hbad hnk hnf <;>
                simp_all [NodeKind.isCharacterData]
            -- step 5
            · split
              · next hpne =>
                split
                · next hdtb => exact absurd (hdt (by simpa using hdtb)) hpne
                · rfl
              · next hpne =>
                have hpdoc : pd.kind = NodeKind.document := by
                  by_cases h : pd.kind = NodeKind.document
                  · exact h
                  · exact absurd h hpne
                -- step 6
                split
                · next hbad => rw [hdocText hpdoc] at hbad; simp at hbad
                -- step 7
                · split
                  · rfl
                  -- step 8
                  · next hcd =>
                    split
                    · next hbad => exact absurd (by simpa using hbad) hnf
                    -- step 9
                    · split
                      · next helem =>
                        unfold checkElementInsertion
                        rw [hdocElem hpdoc (by simpa using helem)]
                        simp
                      -- step 10-11
                      · next helem =>
                        have hdoctype : nd.kind = NodeKind.documentType := by
                          cases hk : nd.kind <;> rw [hk] at hcd helem hnk hnf <;>
                            simp_all [NodeKind.isCharacterData]
                        obtain ⟨hdc, hec⟩ := hdocDoctype hpdoc hdoctype
                        unfold checkDoctypeInsertion
                        rw [hdc, hec]
                        simp

/-- step 9 / 8 の element 挿入検査が通ったときに得られる事実。 -/
theorem checkElementInsertion_ok {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : checkElementInsertion t parent child excl = .ok ()) :
    (∀ e ∈ elementChildren t parent, e ∈ excl) ∧
      ∀ c, child = some c →
        ((kindOf t c == some NodeKind.documentType) = false ∨ c ∈ excl) ∧
          doctypeFollows t parent c = false := by
  unfold checkElementInsertion at h
  split at h
  · simp at h
  · next hany =>
    have hall : ∀ e ∈ elementChildren t parent, e ∈ excl := by
      simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany
      intro e he
      have hb := hany e he
      simpa using hb
    refine ⟨hall, ?_⟩
    intro c hc
    subst hc
    simp only at h
    split at h
    · simp at h
    · next hfol =>
      split at h
      · simp at h
      · next hk =>
        refine ⟨?_, by simpa using hfol⟩
        by_cases hcm : c ∈ excl
        · exact Or.inr hcm
        · refine Or.inl ?_
          have hcont : excl.contains c = false := by simpa using hcm
          rw [Bool.not_eq_true, Bool.and_eq_false_iff, hcont] at hk
          simpa using hk

/-- step 10-11 の doctype 挿入検査が通ったときに得られる事実。 -/
theorem checkDoctypeInsertion_ok {t : Tree} {parent : NodeId} {child : Option NodeId}
    {excl : List NodeId} (h : checkDoctypeInsertion t parent child excl = .ok ()) :
    (∀ e ∈ doctypeChildren t parent, e ∈ excl) ∧
      (∀ c, child = some c → elementPrecedes t parent c = false) ∧
      (child = none → ∀ e ∈ elementChildren t parent, e ∈ excl) := by
  unfold checkDoctypeInsertion at h
  split at h
  · simp at h
  · next hany =>
    have hall : ∀ e ∈ doctypeChildren t parent, e ∈ excl := by
      simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany
      intro e he
      simpa using hany e he
    refine ⟨hall, ?_, ?_⟩
    · intro c hc
      subst hc
      simp only at h
      split at h
      · simp at h
      · next hp => simpa using hp
    · intro hc
      subst hc
      simp only at h
      split at h
      · simp at h
      · next hany' =>
        simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and] at hany'
        intro e he
        simpa using hany' e he

/--
parent が Document のとき、`ensure pre-insertion validity` が確立する事実。

step 6（Text は入れられない）、step 8（fragment の中身）、
step 9（element を入れる条件）、step 10-11（doctype を入れる条件）に対応する。
-/
theorem ensurePreInsertionValidity_documentFacts {t : Tree} {node parent : NodeId}
    {child : Option NodeId} {excl : List NodeId} {pd nd : NodeData}
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hdoc : pd.kind = NodeKind.document)
    (hv : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    nd.kind.isText = false ∧
    (nd.kind = NodeKind.documentFragment →
      (elementChildren t node).length ≤ 1 ∧ textChildren t node = []) ∧
    ((nd.kind = NodeKind.element ∨
        (nd.kind = NodeKind.documentFragment ∧ elementChildren t node ≠ [])) →
      (∀ e ∈ elementChildren t parent, e ∈ excl) ∧
        ∀ c, child = some c →
          ((kindOf t c == some NodeKind.documentType) = false ∨ c ∈ excl) ∧
            doctypeFollows t parent c = false) ∧
    (nd.kind = NodeKind.documentType →
      (∀ e ∈ doctypeChildren t parent, e ∈ excl) ∧
        (∀ c, child = some c → elementPrecedes t parent c = false) ∧
        (child = none → ∀ e ∈ elementChildren t parent, e ∈ excl)) := by
  unfold ensurePreInsertionValidity at hv
  rw [hpd, hnd] at hv
  simp only at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · split at hv
          · next hne => exact absurd hdoc hne
          · split at hv
            · simp at hv
            · next hisText =>
              have htext : nd.kind.isText = false := by simpa using hisText
              refine ⟨htext, ?_, ?_, ?_⟩ <;> split at hv
              -- step 7：CharacterData ならここで終わり
              · next hcd =>
                intro hfrag
                rw [hfrag] at hcd
                simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  split at hv
                  · simp at hv
                  · next hsizes =>
                    intro _
                    rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hsizes
                    obtain ⟨hlen, hemp⟩ := hsizes
                    refine ⟨by simp at hlen; omega, ?_⟩
                    rw [Bool.not_eq_false', List.isEmpty_iff] at hemp
                    exact hemp
                · next hnfrag =>
                  intro hfrag
                  rw [hfrag] at hnfrag
                  simp at hnfrag
              · next hcd =>
                intro hcase
                exfalso
                rcases hcase with hk | ⟨hk, _⟩
                · rw [hk] at hcd; simp [NodeKind.isCharacterData] at hcd
                · rw [hk] at hcd; simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  split at hv
                  · simp at hv
                  · split at hv
                    · next hempty =>
                      intro hcase
                      rcases hcase with hk | ⟨_, hne⟩
                      · rw [hk] at hfrag; simp at hfrag
                      · exact absurd (by simpa using hempty) hne
                    · intro _
                      exact checkElementInsertion_ok hv
                · next hnfrag =>
                  split at hv
                  · intro _
                    exact checkElementInsertion_ok hv
                  · next hnelem =>
                    intro hcase
                    exfalso
                    rcases hcase with hk | ⟨hk, _⟩
                    · rw [hk] at hnelem; simp at hnelem
                    · rw [hk] at hnfrag; simp at hnfrag
              · next hcd =>
                intro hdt
                exfalso
                rw [hdt] at hcd
                simp [NodeKind.isCharacterData] at hcd
              · next hcd =>
                split at hv
                · next hfrag =>
                  intro hdt
                  rw [hdt] at hfrag
                  simp at hfrag
                · split at hv
                  · next helem =>
                    intro hdt
                    rw [hdt] at helem
                    simp at helem
                  · intro _
                    exact checkDoctypeInsertion_ok hv

/-! ## 検査順序 -/

section PreInsertOrder

variable {t : Tree} {node parent : NodeId} {child : Option NodeId} {excl : List NodeId}
  {pd nd : NodeData}

/-- step 1。parent が children を持てない kind なら、他に何があっても HierarchyRequestError。 -/
theorem ensurePreInsertionValidity_step1
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = false) :
    ensurePreInsertionValidity t node parent child excl = .error .hierarchyRequestError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  refine if_pos ?_
  cases hkk : pd.kind <;> rw [hkk] at hk <;> simp_all [NodeKind.canHaveChildren]

/-- step 2。cycle は step 3 以降の違反より先に返る。 -/
theorem ensurePreInsertionValidity_step2
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = true)
    (hanc : isInclusiveAncestorOf t node parent = true) :
    ensurePreInsertionValidity t node parent child excl = .error .hierarchyRequestError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by cases hkk : pd.kind <;> rw [hkk] at hk <;>
    simp_all [NodeKind.canHaveChildren]), if_pos hanc]

/-- step 3。reference child が parent の子でないなら NotFoundError。 -/
theorem ensurePreInsertionValidity_step3
    (hpd : t.get? parent = some pd) (hnd : t.get? node = some nd)
    (hk : pd.kind.canHaveChildren = true)
    (hanc : isInclusiveAncestorOf t node parent = false)
    (hch : childHasParent t child parent = false) :
    ensurePreInsertionValidity t node parent child excl = .error .notFoundError := by
  unfold ensurePreInsertionValidity
  rw [hpd, hnd]
  simp only
  rw [if_neg (by cases hkk : pd.kind <;> rw [hkk] at hk <;>
    simp_all [NodeKind.canHaveChildren]), if_neg (by rw [hanc]; simp),
    if_pos (by rw [hch]; simp)]

end PreInsertOrder

/-! ## `child` に関する congruence -/

/-- step 4 を通った node が Element でも CharacterData でも DocumentFragment でもなければ doctype。 -/
theorem kind_documentType_of {k : NodeKind}
    (h4 : ¬ (!(k == NodeKind.documentFragment || k == NodeKind.documentType ||
      k == NodeKind.element || k.isCharacterData)) = true)
    (h7 : ¬ k.isCharacterData = true) (h8 : ¬ (k == NodeKind.documentFragment) = true)
    (h9 : ¬ (k == NodeKind.element) = true) : k = NodeKind.documentType := by
  cases k <;> simp_all [NodeKind.isCharacterData]

/--
`ensure pre-insertion validity` のうち `child` に依存するのは
step 3 と step 8-11 の検査だけである。
-/
theorem ensurePreInsertionValidity_child_congr {t : Tree} {node parent : NodeId}
    {c₁ c₂ : Option NodeId} {excl : List NodeId}
    (h3 : childHasParent t c₂ parent = true)
    (hel : ∀ nd, t.get? node = some nd →
      checkElementInsertion t parent c₁ excl = .ok () →
      checkElementInsertion t parent c₂ excl = .ok ())
    (hdt : ∀ nd, t.get? node = some nd → nd.kind = NodeKind.documentType →
      checkDoctypeInsertion t parent c₁ excl = .ok () →
      checkDoctypeInsertion t parent c₂ excl = .ok ())
    (hv : ensurePreInsertionValidity t node parent c₁ excl = .ok ()) :
    ensurePreInsertionValidity t node parent c₂ excl = .ok () := by
  unfold ensurePreInsertionValidity at hv ⊢
  split at hv
  · simp at hv
  · next pd hpd =>
    split at hv
    · simp at hv
    · next nd hnd =>
      split at hv
      · simp at hv
      · next h1 =>
        rw [if_neg h1]
        split at hv
        · simp at hv
        · next h2 =>
          rw [if_neg h2]
          rw [if_neg (show ¬(!childHasParent t c₂ parent) = true by simpa using h3)]
          split at hv
          · simp at hv
          · split at hv
            · simp at hv
            · next h4 =>
              rw [if_neg h4]
              split at hv
              · next h5 => rw [if_pos h5]; exact hv
              · next h5 =>
                rw [if_neg h5]
                split at hv
                · simp at hv
                · next h6 =>
                  rw [if_neg h6]
                  split at hv
                  · next h7 => rw [if_pos h7]
                  · next h7 =>
                    rw [if_neg h7]
                    split at hv
                    · next h8 =>
                      rw [if_pos h8]
                      split at hv
                      · simp at hv
                      · next h8a =>
                        rw [if_neg h8a]
                        split at hv
                        · next h8b => rw [if_pos h8b]
                        · next h8b => rw [if_neg h8b]; exact hel nd hnd hv
                    · next h8 =>
                      rw [if_neg h8]
                      split at hv
                      · next h9 => rw [if_pos h9]; exact hel nd hnd hv
                      · next h9 =>
                        rw [if_neg h9]
                        refine hdt nd hnd ?_ hv
                        exact kind_documentType_of h4 h7 h8 h9

end Dom
