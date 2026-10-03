import Dom.Spec.NormalizeSound
import Dom.Spec.NormalizeCongr
import Dom.Properties.Contract
import Dom.Properties.Iterator

/-!
# `normalize()` の、結果まで含めた関係

`normalize` が失敗するのは `this` が木に無いときだけであることを示し、
`NormalizeResult` の soundness・一意性・完全性をまとめる。

失敗しないことの芯は二つである。

* 兄弟を一つ畳む段は、survivor と兄弟がどちらも exclusive Text で、兄弟に parent があれば
  成功する。replace data は survivor の末尾（offset = length、count = 0）に足すだけなので、
  surrogate pair を割ることがない。
* 畳む段も外す段も node の kind を変えず、外す兄弟以外の parent を変えない。
  したがって run の残りの兄弟は、順番が来たときにも上の条件を満たしている。
-/

namespace Dom.Spec

open Dom

/-! ## 末尾に足す replace data は成功する -/

theorem spliceData?_at_end (old data : String) :
    spliceData? old (Utf16.length old) 0 data = some (old ++ data) :=
  spliceData?_of_dataSpliced ⟨old.toList, [], [], by simp, rfl, rfl, by simp⟩

theorem replaceData_append_isOk {s : DOMState} {n : NodeId} {d : NodeData} (data : String)
    (hd : s.tree.get? n = some d) (hk : d.kind = .text) :
    ∃ s', replaceData s n d.length 0 data = .ok s' := by
  have hlen : d.length = Utf16.length d.data := by
    unfold NodeData.length; rw [if_pos (by rw [hk]; rfl)]
  unfold replaceData
  simp only [hd]
  rw [if_neg (by rw [hk]; decide), if_neg (by omega)]
  rw [show adjustedCount d.length d.length 0 = 0 from by unfold adjustedCount; split <;> omega,
    hlen, spliceData?_at_end]
  exact ⟨_, rfl⟩

/-! ## 兄弟を一つ畳む段 -/

/-- 兄弟を一つ畳む段は、外す兄弟以外の parent を変えず、kind も変えない。 -/
theorem normalizeMergeOne_frame {s s' : DOMState} {survivor sib : NodeId}
    (h : normalizeMergeOne s survivor sib = .ok s') :
    (∀ x, x ≠ sib → parentOf s'.tree x = parentOf s.tree x) ∧ ShapePreserving s.tree s'.tree := by
  unfold normalizeMergeOne at h
  split at h
  · next dsurv dsib parent idx hsurv hsib hp hidx =>
    by_cases hbad : (survivor == sib || dsurv.kind != NodeKind.text ||
        dsib.kind != NodeKind.text) = true
    · simp only [hbad, if_true] at h
      cases h
    · simp only [hbad, Bool.false_eq_true, if_false] at h
      -- step 3-4 の後の状態を `s₁` として、step 6-7 を一度に扱う
      have tail : ∀ s₁ s₂ : DOMState, ShapePreserving s.tree s₁.tree →
          (∀ x, parentOf s₁.tree x = parentOf s.tree x) →
          s₂ = { s₁ with
            ranges := s₁.ranges.map (normalizeMergeRange survivor sib parent idx dsurv.length) } →
          remove s₂ sib = .ok s' →
          (∀ x, x ≠ sib → parentOf s'.tree x = parentOf s.tree x) ∧
            ShapePreserving s.tree s'.tree := by
        intro s₁ s₂ hsp hpar hs₂ hr
        have ht : s₂.tree = s₁.tree := by rw [hs₂]
        refine ⟨fun x hx => ?_, hsp.trans (ht ▸ shapePreserving_remove hr)⟩
        rw [parentOf_detach (remove_ok hr).2 x, if_neg hx, ht]
        exact hpar x
      by_cases hemp : dsib.data.isEmpty = true
      · simp only [hemp, if_true] at h
        exact tail s _ (ShapePreserving.refl _) (fun _ => rfl) rfl h
      · simp only [hemp, Bool.false_eq_true, if_false] at h
        cases hrd : replaceData s survivor dsurv.length 0 dsib.data with
        | error e => rw [hrd] at h; cases h
        | ok s₁ =>
          rw [hrd] at h
          obtain ⟨d, sp, hd, -, -, -, ht, -⟩ := replaceData_ok hrd
          refine tail s₁ _ (shapePreserving_replaceData hrd) (fun x => ?_) rfl h
          rw [ht, parentOf_withData hd]
  · cases h

/-- **兄弟を一つ畳む段は、survivor と兄弟が exclusive Text で、兄弟に parent があれば成功する。** -/
theorem normalizeMergeOne_isOk {s : DOMState} {survivor sib p : NodeId} {dsurv dsib : NodeData}
    (hwf : WellFormed s.tree) (hsurv : s.tree.get? survivor = some dsurv)
    (hks : dsurv.kind = .text) (hsib : s.tree.get? sib = some dsib) (hkb : dsib.kind = .text)
    (hne : survivor ≠ sib) (hp : parentOf s.tree sib = some p) :
    ∃ s', normalizeMergeOne s survivor sib = .ok s' := by
  obtain ⟨idx, hidx⟩ := index_isSome hwf hp
  -- step 6-7：range を渡した状態でも `sib` の parent は残っているので外せる
  have tail : ∀ s₁ s₂ : DOMState, WellFormed s₁.tree → parentOf s₁.tree sib = some p →
      s₂ = { s₁ with
        ranges := s₁.ranges.map (normalizeMergeRange survivor sib p idx dsurv.length) } →
      ∃ s', remove s₂ sib = .ok s' := by
    intro s₁ s₂ hwf₁ hp₁ hs₂
    have ht : s₂.tree = s₁.tree := by rw [hs₂]
    refine (remove_succeeds_iff (by rw [ht]; exact hwf₁)).mpr ?_
    rw [ht, hp₁]; rfl
  unfold normalizeMergeOne
  simp only [hsurv, hsib, hp, hidx]
  rw [if_neg (by simp [hne, hks, hkb])]
  by_cases hemp : dsib.data.isEmpty = true
  · simp only [hemp, if_true]
    exact tail s _ hwf hp rfl
  · simp only [hemp, Bool.false_eq_true, if_false]
    obtain ⟨s₁, hrd⟩ := replaceData_append_isOk (s := s) dsib.data hsurv hks
    rw [hrd]
    obtain ⟨d, sp, hd, -, -, -, ht, -⟩ := replaceData_ok hrd
    refine tail s₁ _ (replaceData_preserves_wellformed hwf hrd) ?_ rfl
    rw [ht, parentOf_withData hd]
    exact hp

/-! ## run -/

/-- kind は shape に入っているので、shape を保つ変化は exclusive Text であることを保つ。 -/
theorem kind_of_shapePreserving {t t' : Tree} (h : ShapePreserving t t') {m : NodeId}
    {d : NodeData} (hd : t.get? m = some d) :
    ∃ d', t'.get? m = some d' ∧ d'.kind = d.kind := by
  obtain ⟨d', hd'⟩ := exists_get?_of_kindPreserving h hd
  have hk := h.kind m
  rw [hd, hd'] at hk
  exact ⟨d', hd', Option.some.inj hk⟩

/-- run を畳む段は、kind を変えず、run に入っていない node の parent を変えない。 -/
theorem normalizeRun_frame {survivor : NodeId} : ∀ (sibs : List NodeId) {s s' : DOMState},
    normalizeRun s survivor sibs = .ok s' →
    (∀ x, x ∉ sibs → parentOf s'.tree x = parentOf s.tree x) ∧ ShapePreserving s.tree s'.tree
  | [], s, s', h => by
    rw [normalizeRun] at h
    cases h
    exact ⟨fun _ _ => rfl, ShapePreserving.refl _⟩
  | sib :: rest, s, s', h => by
    rw [normalizeRun] at h
    split at h
    · cases h
    · next s₁ hm =>
      obtain ⟨hp₁, hsp₁⟩ := normalizeMergeOne_frame hm
      obtain ⟨hp₂, hsp₂⟩ := normalizeRun_frame rest h
      refine ⟨fun x hx => ?_, hsp₁.trans hsp₂⟩
      rw [hp₂ x (fun hm' => hx (by simp [hm'])), hp₁ x (fun he => hx (by simp [he]))]

/--
**run を畳む段は、survivor と残りの兄弟が exclusive Text で、兄弟に parent があれば成功する。**
-/
theorem normalizeRun_isOk {survivor : NodeId} : ∀ (sibs : List NodeId) {s : DOMState}
    {dsurv : NodeData}, WellFormed s.tree → s.tree.get? survivor = some dsurv →
    dsurv.kind = .text →
    (∀ x ∈ sibs, (∃ p, parentOf s.tree x = some p) ∧
      ∃ dx, s.tree.get? x = some dx ∧ dx.kind = .text) →
    survivor ∉ sibs → sibs.Nodup →
    ∃ s', normalizeRun s survivor sibs = .ok s'
  | [], s, _, _, _, _, _, _, _ => ⟨s, rfl⟩
  | sib :: rest, s, dsurv, hwf, hsurv, hks, hsibs, hnot, hnd => by
    obtain ⟨⟨p, hp⟩, dsib, hsib, hkb⟩ := hsibs sib (by simp)
    obtain ⟨s₁, hm⟩ := normalizeMergeOne_isOk hwf hsurv hks hsib hkb
      (fun he => hnot (by simp [he])) hp
    obtain ⟨hpar, hsp⟩ := normalizeMergeOne_frame hm
    have hwf₁ : WellFormed s₁.tree := (normalizeMergeOne_sound hwf hm).2
    obtain ⟨dsurv₁, hsurv₁, hks₁⟩ := kind_of_shapePreserving hsp hsurv
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨s', hr⟩ := normalizeRun_isOk rest hwf₁ hsurv₁ (by rw [hks₁, hks])
      (fun x hx => by
        have hxs : x ≠ sib := fun he => hnd'.1 (he ▸ hx)
        obtain ⟨⟨q, hq⟩, dx, hdx, hkx⟩ := hsibs x (by simp [hx])
        obtain ⟨dx₁, hdx₁, hkx₁⟩ := kind_of_shapePreserving hsp hdx
        exact ⟨⟨q, by rw [hpar x hxs]; exact hq⟩, dx₁, hdx₁, by rw [hkx₁, hkx]⟩)
      (fun hm' => hnot (by simp [hm'])) hnd'.2
    refine ⟨s', ?_⟩
    rw [normalizeRun, hm]
    exact hr

/-- `followingTexts` は run を畳む段の前提を満たす。 -/
theorem followingTexts_facts {t : Tree} (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) :
    (∀ x ∈ followingTexts t n, (∃ q, parentOf t x = some q) ∧
      ∃ dx, t.get? x = some dx ∧ dx.kind = .text) ∧
    n ∉ followingTexts t n ∧ (followingTexts t n).Nodup := by
  obtain ⟨p', pre, post, hp', hc, hex, -⟩ := followingTexts_spec hwf hp
  have hnd : (pre ++ n :: (followingTexts t n ++ post)).Nodup := by
    rw [← hc]; exact childrenOf_nodup hwf p'
  have hnd₂ : (n :: (followingTexts t n ++ post)).Nodup := (List.nodup_append.mp hnd).2.1
  refine ⟨fun x hx => ⟨⟨p', (mem_childrenOf_iff hwf x p').mpr (by rw [hc]; simp [hx])⟩, hex x hx⟩,
    fun hm => (List.nodup_cons.mp hnd₂).1 (by simp [hm]), ?_⟩
  exact (List.nodup_append.mp (List.nodup_cons.mp hnd₂).2).1

/-! ## 候補列 -/

/-- **候補列の処理は、候補がどれも exclusive Text なら成功する。** -/
theorem normalizeList_isOk (this : NodeId) : ∀ (cands : List NodeId) {s : DOMState},
    WellFormed s.tree → (∀ x ∈ cands, ∀ dx, s.tree.get? x = some dx → dx.kind = .text) →
    ∃ s', normalizeList s this cands = .ok s'
  | [], s, _, _ => ⟨s, rfl⟩
  | n :: rest, s, hwf, hk => by
    -- 残りの候補が exclusive Text であることは shape を保つ変化で残る
    have hrest : ∀ {s' : DOMState}, ShapePreserving s.tree s'.tree →
        ∀ x ∈ rest, ∀ dx, s'.tree.get? x = some dx → dx.kind = .text := by
      intro s' hsp x hx dx hdx
      obtain ⟨d₀, hd₀, hk₀, -⟩ := hsp.exists_get? hdx
      rw [← hk₀]
      exact hk x (by simp [hx]) d₀ hd₀
    rw [normalizeList]
    split
    · next hanc =>
      have hanc' : Ancestor s.tree this n := (isAncestorOf_iff hwf this n).mp hanc
      obtain ⟨p, hp⟩ := hanc'.parent_isSome
      split
      · exact normalizeList_isOk this rest hwf (fun x hx => hk x (by simp [hx]))
      · next d hd =>
        split
        · obtain ⟨s₁, hr⟩ := (remove_succeeds_iff hwf (n := n) (b := false)).mpr (by rw [hp]; rfl)
          rw [hr]
          exact normalizeList_isOk this rest (remove_preserves_wellformed hwf hr)
            (hrest (shapePreserving_remove hr))
        · obtain ⟨hsibs, hnot, hnd⟩ := followingTexts_facts hwf hp
          obtain ⟨s₁, hr⟩ := normalizeRun_isOk _ hwf hd (hk n (by simp) d hd) hsibs hnot hnd
          rw [hr]
          exact normalizeList_isOk this rest (normalizeRun_sound _ hwf hr).2
            (hrest (normalizeRun_frame _ hr).2)
    · exact normalizeList_isOk this rest hwf (fun x hx => hk x (by simp [hx]))

/-- **`normalize` は `this` が木にあれば成功する。** -/
theorem normalize_isOk {s : DOMState} {this : NodeId} {d : NodeData} (hwf : WellFormed s.tree)
    (hd : s.tree.get? this = some d) : ∃ s', normalize s this = .ok s' := by
  unfold normalize
  simp only [hd]
  refine normalizeList_isOk this _ hwf ?_
  intro x hx dx hdx
  have := (List.mem_filter.mp hx).2
  unfold isExclusiveText at this
  rw [hdx] at this
  simpa using this

/-! ## 結果まで含めた関係 -/

theorem normalize_result_sound {s : DOMState} (hwf : WellFormed s.tree) (this : NodeId) :
    NormalizeResult s this (normalize s this) := by
  cases h : normalize s this with
  | ok s' => exact normalize_sound hwf h
  | error e =>
    cases hd : s.tree.get? this with
    | none =>
      unfold normalize at h
      rw [hd] at h
      exact ⟨hd, (Except.error.inj h).symm⟩
    | some d =>
      obtain ⟨s', h'⟩ := normalize_isOk hwf hd
      rw [h] at h'
      cases h'

theorem normalize_result_deterministic {s : DOMState} (hwf : WellFormed s.tree) {this : NodeId}
    {r₁ r₂ : Except DOMException DOMState}
    (h₁ : NormalizeResult s this r₁) (h₂ : NormalizeResult s this r₂) : ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok o₁ =>
    cases r₂ with
    | ok o₂ => exact normalizeSpec_deterministic hwf h₁ h₂
    | error e₂ =>
      obtain ⟨⟨d, hd⟩, -⟩ := h₁
      rw [h₂.1] at hd
      cases hd
  | error e₁ =>
    cases r₂ with
    | ok o₂ =>
      obtain ⟨⟨d, hd⟩, -⟩ := h₂
      rw [h₁.1] at hd
      cases hd
    | error e₂ => show e₁ = e₂; rw [h₁.2, h₂.2]

theorem normalize_result_complete {s : DOMState} (hwf : WellFormed s.tree) {this : NodeId}
    {r : Except DOMException DOMState} (h : NormalizeResult s this r) :
    ResultObsEq r (normalize s this) :=
  normalize_result_deterministic hwf h (normalize_result_sound hwf this)

end Dom.Spec
