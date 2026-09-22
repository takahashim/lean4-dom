import Dom.Spec.Complete
import Dom.Spec.Validity
import Dom.Spec.MoveValidity
import Dom.Properties.MoveContract

/-!
# 例外まで含めた関係意味論

`Dom/Spec/` の関係は **成功したときの状態遷移**だけを述べる。
`remove_sound` のように `= .ok s'` を仮定に置くので、
「どの入力でどの例外を返すか」は関係の外（`Dom/Properties/Contract.lean`）にある。

その形だと、**極端には「常に失敗する実装」でも soundness を満たす**。
completeness（`remove_complete`）がそれを塞ぐが、
「関係が結果そのものを決める」とは言えていない。

失敗側の条件そのものは `Dom/Spec/Validity.lean` に独立に書いてある
（`ensure pre-insert validity` の step 1-11）。ここはそれを使って結果を組む。

ここでは結果（`Except DOMException DOMState`）まで含めた関係を置き、

* soundness を**仮定なし**にする（`remove_result_sound`）
* 一意性を結果の水準で述べる（`remove_result_deterministic`）

の二つを言う。成功するかどうかまで関係が決めるので、
「常に失敗する実装」は soundness の時点で落ちる。

## どこまで書けるか

書けるのは、失敗条件が両側で捕まっているものだけである。

* algorithm では `remove`（`remove_error_iff`）。
* public API では `preInsert`（`insertBefore` / `appendChild`）。
  `insert` は algorithm 単体の失敗条件を持たないが、呼び出し側では
  step 1 の validity がすべてを決める。
* public API では `replace`（`replace_error_iff`）。step 1 は `preInsert` と同じ
  `ensurePreInsertionValidity` なので、`PreInsertValidity` をそのまま使い回せる。
* public API では `moveBefore`（`moveBefore_error_iff` / `moveBefore_error_receiver`）。
  step 1-6 は `MoveValidity`（`Dom/Spec/MoveValidity.lean`）で独立に書いた。
  receiver 自身の失敗が二つあるぶん、関係は三枝になる。
-/

namespace Dom.Spec

open Dom

/--
**§4.2.3 remove の、結果まで含めた関係。**

成功なら `RemoveSpec`、失敗なら「parent が無く、例外は `NotFoundError`」である。
-/
def RemoveResult (s : DOMState) (node : NodeId) (suppress : Bool) :
    Except DOMException DOMState → Prop
  | .ok s' => RemoveSpec s node suppress s'
  | .error e => parentOf s.tree node = none ∧ e = .notFoundError

/--
**`remove` の結果は、成否によらず関係を満たす。**

`remove_sound` と違って `= .ok s'` を仮定しない。
これが「常に失敗する実装」を排除する。
-/
theorem remove_result_sound {s : DOMState} (hwf : WellFormed s.tree) (node : NodeId)
    (suppress : Bool) : RemoveResult s node suppress (remove s node suppress) := by
  cases h : remove s node suppress with
  | ok s' => exact remove_sound hwf h
  | error e => exact (remove_error_iff hwf).mp h

/-- 関係を満たす結果が成功なら、node は parent を持つ。 -/
theorem removeResult_parentOf_isSome {s : DOMState} {node : NodeId} {suppress : Bool}
    {s' : DOMState} (h : RemoveResult s node suppress (.ok s')) :
    (parentOf s.tree node).isSome := by
  obtain ⟨p, -, hp, -⟩ := h
  rw [hp]; rfl

/--
**関係は結果を一つに決める。**

成功するかどうかも、成功したときの観測も、失敗したときの例外も決まる。
-/
theorem remove_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {node : NodeId} {suppress : Bool} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : RemoveResult s node suppress r₁) (h₂ : RemoveResult s node suppress r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok s₁ =>
    cases r₂ with
    | ok s₂ => exact removeSpec_congr hwf (ObsEq.refl s) h₁ h₂
    | error e₂ =>
      exfalso
      have := removeResult_parentOf_isSome h₁
      rw [h₂.1] at this
      exact Bool.noConfusion this
  | error e₁ =>
    cases r₂ with
    | ok s₂ =>
      exfalso
      have := removeResult_parentOf_isSome h₂
      rw [h₁.1] at this
      exact Bool.noConfusion this
    | error e₂ => show e₁ = e₂; rw [h₁.2, h₂.2]

/--
**完全性も結果の水準で言える。**

関係を満たす結果があるなら、`remove` の結果はそれと観測として等しい。
失敗する側も含むので、「関係が失敗を許す入力では実行関数も失敗する」まで言っている。
-/
theorem remove_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {node : NodeId} {suppress : Bool} {r : Except DOMException DOMState}
    (h : RemoveResult s node suppress r) : ResultObsEq r (remove s node suppress) :=
  remove_result_deterministic hwf h (remove_result_sound hwf node suppress)

/-! ### 関係が成否を決めていることの証人 -/

/-- parent を持つ node については、関係は失敗を許さない。 -/
theorem removeResult_not_error_of_parent {s : DOMState} {node parent : NodeId} {suppress : Bool}
    {e : DOMException} (hp : parentOf s.tree node = some parent) :
    ¬ RemoveResult s node suppress (.error e) := by
  intro h
  have h1 : parentOf s.tree node = none := h.1
  rw [hp] at h1
  exact absurd h1 (by simp)

/-- parent を持たない node については、関係は成功を許さない。 -/
theorem removeResult_not_ok_of_no_parent {s : DOMState} {node : NodeId} {suppress : Bool}
    {s' : DOMState} (hp : parentOf s.tree node = none) :
    ¬ RemoveResult s node suppress (.ok s') := by
  intro h
  have := removeResult_parentOf_isSome h
  rw [hp] at this
  exact Bool.noConfusion this

/-! ## public API：`insertBefore` / `appendChild` -/

/--
step 1 の validity は、step 4 が要る acyclicity を含んでいる。

fragment の children が `parent` の inclusive ancestor なら fragment 自身もそうなるので、
validity の step 2 がそれを弾いている。
-/
theorem nodesToInsert_not_ancestor_of_validity {t : Tree} (hwf : WellFormed t)
    {node parent : NodeId} {child : Option NodeId} {excl : List NodeId}
    (hv : ensurePreInsertionValidity t node parent child excl = .ok ()) :
    ∀ ns : List NodeId, NodesToInsert t node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor t m parent := by
  obtain ⟨-, ⟨nd, hnd⟩, hanc, -⟩ := ensurePreInsertionValidity_ok hv
  have hnotanc : ¬ InclusiveAncestor t node parent := by
    intro hq
    rw [(isInclusiveAncestorOf_iff hwf node parent).mpr hq] at hanc
    exact Bool.noConfusion hanc
  intro ns hns m hm
  obtain ⟨nd', hnd', hcase⟩ := hns
  rw [hnd] at hnd'
  cases hnd'
  rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · -- fragment の children。`node` はその parent なので、祖先関係が `node` へ伝わる。
    intro hq
    obtain ⟨md, hmd, hmp⟩ := hwf.parent_child node nd hnd m hm
    have hnm : Ancestor t node m := Ancestor.step (by rw [parentOf_of_get? hmd]; exact hmp)
    refine hnotanc ?_
    rcases hq with he | ha
    · exact Or.inr (by rw [← he]; exact hnm)
    · exact Or.inr (hnm.trans_ancestor ha)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [hm]
    exact hnotanc

/--
**§4.2.3 pre-insert の、結果まで含めた関係。**

成功なら「step 1 を通り、step 4 の `insert` が関係を満たす」、
失敗なら「step 1 がその例外で落ちる」である。
`insertBefore` と `appendChild` はこれに委譲するだけである。

## 独立性

失敗側は `PreInsertValidity`（`Dom/Spec/Validity.lean`）で書く。仕様の step 1-11 を
実行側の関数を呼ばずに写した関係で、`ensurePreInsertionValidity_spec`（仮定なしの
soundness）と `preInsertValidity_deterministic` が実行側との対応を与える。
step 2-3 の reference child も、`preInsertReferenceChild` を呼ばずに
「`node` 自身なら次の兄弟、でなければそのまま」と書いてある。

したがってこの関係は、仕様の step を読み違えた実装に合わせて成り立つことはない。
`ruby test/spec_dependence.rb` にも出ない。
-/
def PreInsertResult (s : DOMState) (node parent : NodeId) (child : Option NodeId) :
    Except DOMException DOMState → Prop
  | .ok s' => PreInsertValidity s.tree node parent child [] (.ok ()) ∧
      -- step 2-3。reference child は `node` 自身なら次の兄弟に取り替える。
      ∃ ref, (child = some node → ref = nextSibling s.tree node) ∧
        (child ≠ some node → ref = child) ∧
        InsertSpec s node parent ref false s'
  | .error e => PreInsertValidity s.tree node parent child [] (.error e)

/-- **`preInsert` の結果は、成否によらず関係を満たす。** -/
theorem preInsert_result_sound {s : DOMState} (hwf : WellFormed s.tree)
    (node parent : NodeId) (child : Option NodeId) :
    PreInsertResult s node parent child (preInsert s node parent child) := by
  cases h : preInsert s node parent child with
  | ok s' =>
    obtain ⟨hv, hi⟩ := preInsert_cases h
    refine ⟨(preInsertValidity_iff hwf).mpr hv, preInsertReferenceChild s.tree node child,
      ?_, ?_, insert_sound hwf hi⟩
    · intro hc; rw [preInsertReferenceChild_eq, if_pos hc]
    · intro hc; rw [preInsertReferenceChild_eq, if_neg hc]
  | error e => exact (preInsertValidity_iff hwf).mpr ((preInsert_error_iff hwf).mp h)

/-- **関係は結果を一つに決める。** -/
theorem preInsert_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : PreInsertResult s node parent child r₁)
    (h₂ : PreInsertResult s node parent child r₂) : ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok s₁ =>
    cases r₂ with
    | ok s₂ =>
      obtain ⟨ref₁, ha₁, hb₁, hi₁⟩ := h₁.2
      obtain ⟨ref₂, ha₂, hb₂, hi₂⟩ := h₂.2
      have hre : ref₂ = ref₁ := by
        by_cases hc : child = some node
        · rw [ha₁ hc, ha₂ hc]
        · rw [hb₁ hc, hb₂ hc]
      rw [hre] at hi₂
      refine insertSpec_deterministic hwf ?_ hi₁ hi₂
      have hv : ensurePreInsertionValidity s.tree node parent child [] = .ok () :=
        (preInsertValidity_iff hwf).mp h₁.1
      have hshift := ensurePreInsertionValidity_shift hwf hv
      have hv' : ensurePreInsertionValidity s.tree node parent ref₁ [] = .ok () := by
        by_cases hc : child = some node
        · rw [ha₁ hc]; rw [if_pos hc] at hshift; exact hshift
        · rw [hb₁ hc]; rw [if_neg hc] at hshift; exact hshift
      exact nodesToInsert_not_ancestor_of_validity hwf hv'
    | error e₂ =>
      exfalso
      have h2 := (preInsertValidity_iff hwf).mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂))
      rw [(preInsertValidity_iff hwf).mp h₁.1] at h2
      simp at h2
  | error e₁ =>
    cases r₂ with
    | ok s₂ =>
      exfalso
      have h1 := (preInsertValidity_iff hwf).mp (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁))
      rw [(preInsertValidity_iff hwf).mp h₂.1] at h1
      simp at h1
    | error e₂ =>
      show e₁ = e₂
      have h1 := (preInsertValidity_iff hwf).mp (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁))
      have h2 := (preInsertValidity_iff hwf).mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂))
      rw [h1] at h2
      exact Except.error.inj h2

/-- **完全性も結果の水準で言える。** -/
theorem preInsert_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {r : Except DOMException DOMState}
    (h : PreInsertResult s node parent child r) :
    ResultObsEq r (preInsert s node parent child) :=
  preInsert_result_deterministic hwf h (preInsert_result_sound hwf node parent child)

/-! ### 関係が成否を決めていることの証人 -/

/-- step 1 を通る入力については、関係は失敗を許さない。 -/
theorem preInsertResult_not_error_of_validity {s : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {e : DOMException}
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .ok ()) :
    ¬ PreInsertResult s node parent child (.error e) := by
  intro h
  have h1 := (preInsertValidity_iff hwf).mp (h : PreInsertValidity _ _ _ _ _ (.error e))
  rw [hv] at h1
  simp at h1

/-- step 1 で落ちる入力については、関係は成功を許さない。 -/
theorem preInsertResult_not_ok_of_validity_error {s s' : DOMState} (hwf : WellFormed s.tree)
    {node parent : NodeId} {child : Option NodeId} {e : DOMException}
    (hv : ensurePreInsertionValidity s.tree node parent child [] = .error e) :
    ¬ PreInsertResult s node parent child (.ok s') := by
  intro h
  have h1 := (preInsertValidity_iff hwf).mp h.1
  rw [hv] at h1
  simp at h1

/-! ## public API：`replaceChild` -/

/--
**§4.2.3 replace の、結果まで含めた関係。**

成功なら「step 1 を通り、`ReplaceSpec` を満たす」、失敗なら「step 1 がその例外で落ちる」
である。`replaceChild` はこれに委譲するだけである。

## 独立性

失敗側は `PreInsertResult` と同じ `PreInsertValidity`（`Dom/Spec/Validity.lean`）で書く。
`replace` の step 1 は `ensurePreInsertionValidity` そのもので、`excl` に `[child]` を渡す
（置き換えられる `child` 自身は、fragment の子孫チェックから除く。`child` は
`node` の子ではありえないので、`node` が fragment でも `child` が
その中に紛れ込むことはないが、`excl` はそれを実行側と同じ形で明示する）。

したがってこの関係も、`PreInsertResult` と同じ理由で、仕様の step を読み違えた
実装に合わせて成り立つことはない。
-/
def ReplaceResult (s : DOMState) (child node parent : NodeId) :
    Except DOMException DOMState → Prop
  | .ok s' => PreInsertValidity s.tree node parent (some child) [child] (.ok ()) ∧
      ReplaceSpec s child node parent s'
  | .error e => PreInsertValidity s.tree node parent (some child) [child] (.error e)

/--
**`replace` の結果は、成否によらず関係を満たす。**

`ReplaceSpec` 自体が要る `StructurallyValid`（step 10 の assertion。
`node` と `child` が同じ空の `DocumentFragment` という場合を `fragmentHasNoParent` が
禁じることで成り立つ）をそのまま引き継ぐ。
-/
theorem replace_result_sound {s : DOMState} (hsv : StructurallyValid s.tree)
    (child node parent : NodeId) :
    ReplaceResult s child node parent (replace s child node parent) := by
  have hwf := hsv.wellFormed
  cases h : replace s child node parent with
  | ok s' =>
    exact ⟨(preInsertValidity_iff hwf).mpr ((replace_succeeds_iff hwf).mp ⟨s', h⟩),
      replace_sound hsv h⟩
  | error e => exact (preInsertValidity_iff hwf).mpr ((replace_error_iff hwf).mp h)

/-- **関係は結果を一つに決める。** -/
theorem replace_result_deterministic {s : DOMState} (hsv : StructurallyValid s.tree)
    {child node parent : NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : ReplaceResult s child node parent r₁) (h₂ : ReplaceResult s child node parent r₂) :
    ResultObsEq r₁ r₂ := by
  have hwf := hsv.wellFormed
  cases r₁ with
  | ok s₁ =>
    cases r₂ with
    | ok s₂ =>
      have hv := (preInsertValidity_iff hwf).mp h₁.1
      obtain ⟨-, -, -, hchild⟩ := ensurePreInsertionValidity_ok hv
      exact replaceSpec_deterministic hwf (replace_node_ne_parent hwf hv) (hchild child rfl)
        (nodesToInsert_not_ancestor_of_validity hwf hv) h₁.2 h₂.2
    | error e₂ =>
      exfalso
      have h1 := (preInsertValidity_iff hwf).mp h₁.1
      have h2 := (preInsertValidity_iff hwf).mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂))
      rw [h1] at h2
      simp at h2
  | error e₁ =>
    cases r₂ with
    | ok s₂ =>
      exfalso
      have h1 := (preInsertValidity_iff hwf).mp (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁))
      have h2 := (preInsertValidity_iff hwf).mp h₂.1
      rw [h1] at h2
      simp at h2
    | error e₂ =>
      show e₁ = e₂
      have h1 := (preInsertValidity_iff hwf).mp (h₁ : PreInsertValidity _ _ _ _ _ (.error e₁))
      have h2 := (preInsertValidity_iff hwf).mp (h₂ : PreInsertValidity _ _ _ _ _ (.error e₂))
      rw [h1] at h2
      exact Except.error.inj h2

/-- **完全性も結果の水準で言える。** -/
theorem replace_result_complete {s : DOMState} (hsv : StructurallyValid s.tree)
    {child node parent : NodeId} {r : Except DOMException DOMState}
    (h : ReplaceResult s child node parent r) :
    ResultObsEq r (replace s child node parent) :=
  replace_result_deterministic hsv h (replace_result_sound hsv child node parent)

/-! ### 関係が成否を決めていることの証人 -/

/-- step 1 を通る入力については、関係は失敗を許さない。 -/
theorem replaceResult_not_error_of_validity {s : DOMState} (hsv : StructurallyValid s.tree)
    {child node parent : NodeId} {e : DOMException}
    (hv : ensurePreInsertionValidity s.tree node parent (some child) [child] = .ok ()) :
    ¬ ReplaceResult s child node parent (.error e) := by
  intro h
  have h1 := (preInsertValidity_iff hsv.wellFormed).mp
    (h : PreInsertValidity _ _ _ _ _ (.error e))
  rw [hv] at h1
  simp at h1

/-- step 1 で落ちる入力については、関係は成功を許さない。 -/
theorem replaceResult_not_ok_of_validity_error {s s' : DOMState} (hwf : WellFormed s.tree)
    {child node parent : NodeId} {e : DOMException}
    (hv : ensurePreInsertionValidity s.tree node parent (some child) [child] = .error e) :
    ¬ ReplaceResult s child node parent (.ok s') := by
  intro h
  have h1 := (preInsertValidity_iff hwf).mp h.1
  rw [hv] at h1
  simp at h1

/-! ## public API：`moveBefore` -/

/--
**§4.2.4 move の、結果まで含めた関係。**

`moveBefore` は `ParentNode` の method なので、失敗しうる箇所が三つある。

* receiver（`parent`）が木に無い（`NotFoundError`）
* receiver が `ParentNode`（`canHaveChildren`）でない（`TypeError`、WebIDL による）
* step 1-2 が決める reference child のもとで、step 1-6 の validity が落ちる

前の二つが無ければ、reference child は `child` が `node` 自身なら
`node` の次の兄弟に取り替えたもので、`move` の結果は `MoveValidity` と `MoveSpec` で
決まる。成功できるのは三つ目も通ったときだけなので、成功側は一枝で足りる。

## 独立性

三つ目は `MoveValidity`（`Dom/Spec/MoveValidity.lean`）で書く。仕様の step 1-6 を
実行側の関数を呼ばずに写した関係なので、`PreInsertResult` / `ReplaceResult` と
同じ理由で、仕様の step を読み違えた実装に合わせて成り立つことはない。
-/
def MoveResult (s : DOMState) (parent node : NodeId) (child : Option NodeId) :
    Except DOMException DOMState → Prop
  | .ok s' =>
      ∃ pd, s.tree.get? parent = some pd ∧ pd.kind.canHaveChildren = true ∧
        ∃ ref, (child = some node → ref = nextSibling s.tree node) ∧
          (child ≠ some node → ref = child) ∧
          MoveValidity s.tree node parent ref (.ok ()) ∧ MoveSpec s node parent ref s'
  | .error e =>
      (s.tree.get? parent = none ∧ e = .notFoundError) ∨
      (∃ pd, s.tree.get? parent = some pd ∧ pd.kind.canHaveChildren = false ∧
        e = .typeError) ∨
      (∃ pd, s.tree.get? parent = some pd ∧ pd.kind.canHaveChildren = true ∧
        ∃ ref, (child = some node → ref = nextSibling s.tree node) ∧
          (child ≠ some node → ref = child) ∧
          MoveValidity s.tree node parent ref (.error e))

/-- **`moveBefore` の結果は、成否によらず関係を満たす。** -/
theorem move_result_sound {s : DOMState} (hwf : WellFormed s.tree) (parent node : NodeId)
    (child : Option NodeId) :
    MoveResult s parent node child (moveBefore s parent node child) := by
  cases hpd : s.tree.get? parent with
  | none =>
    have hmv0 : moveBefore s parent node child = .error .notFoundError := by
      unfold moveBefore; rw [hpd]
    rw [hmv0]
    exact Or.inl ⟨hpd, rfl⟩
  | some pd =>
    by_cases hk : pd.kind.canHaveChildren = true
    · cases hmv : moveBefore s parent node child with
      | ok s' =>
        refine ⟨pd, hpd, hk, if child = some node then nextSibling s.tree node else child,
          fun hc => if_pos hc, fun hc => if_neg hc, ?_, ?_⟩
        · exact (moveValidity_iff hwf).mpr ((moveBefore_succeeds_iff hwf hpd hk).mp ⟨s', hmv⟩)
        · have hmv' : move s node parent
              (if child = some node then nextSibling s.tree node else child) = .ok s' := by
            unfold moveBefore at hmv
            rw [hpd] at hmv
            simpa [hk] using hmv
          exact move_sound hwf hmv'
      | error e =>
        refine Or.inr (Or.inr ⟨pd, hpd, hk,
          if child = some node then nextSibling s.tree node else child,
          fun hc => if_pos hc, fun hc => if_neg hc, ?_⟩)
        exact (moveValidity_iff hwf).mpr ((moveBefore_error_iff hwf hpd hk).mp hmv)
    · have hkf : pd.kind.canHaveChildren = false := by simpa using hk
      have hmv0 : moveBefore s parent node child = .error .typeError := by
        unfold moveBefore; rw [hpd]; simp [hkf]
      rw [hmv0]
      exact Or.inr (Or.inl ⟨pd, hpd, hkf, rfl⟩)

/-- **関係は結果を一つに決める。** -/
theorem move_result_deterministic {s : DOMState} (hwf : WellFormed s.tree)
    {parent node : NodeId} {child : Option NodeId} {r₁ r₂ : Except DOMException DOMState}
    (h₁ : MoveResult s parent node child r₁) (h₂ : MoveResult s parent node child r₂) :
    ResultObsEq r₁ r₂ := by
  cases r₁ with
  | ok s₁ =>
    obtain ⟨pd₁, hp₁, hk₁, ref₁, hra₁, hrb₁, hv₁, hspec₁⟩ := h₁
    cases r₂ with
    | ok s₂ =>
      obtain ⟨pd₂, hp₂, hk₂, ref₂, hra₂, hrb₂, hv₂, hspec₂⟩ := h₂
      have href : ref₂ = ref₁ := by
        by_cases hc : child = some node
        · rw [hra₁ hc, hra₂ hc]
        · rw [hrb₁ hc, hrb₂ hc]
      rw [href] at hspec₂
      exact moveSpec_deterministic hwf hspec₁ hspec₂
    | error e₂ =>
      exfalso
      rcases h₂ with ⟨hp₂, -⟩ | ⟨pd₂, hp₂, hk₂, -⟩ |
        ⟨pd₂, hp₂, hk₂, ref₂, hra₂, hrb₂, hv₂⟩
      · rw [hp₁] at hp₂; simp at hp₂
      · have hpdeq : pd₁ = pd₂ := by rw [hp₁] at hp₂; exact Option.some.inj hp₂
        rw [hpdeq, hk₂] at hk₁
        simp at hk₁
      · have href : ref₂ = ref₁ := by
          by_cases hc : child = some node
          · rw [hra₁ hc, hra₂ hc]
          · rw [hrb₁ hc, hrb₂ hc]
        rw [href] at hv₂
        have h1 := (moveValidity_iff hwf).mp hv₁
        have h2 := (moveValidity_iff hwf).mp hv₂
        rw [h1] at h2
        simp at h2
  | error e₁ =>
    rcases h₁ with ⟨hp₁, he₁⟩ | ⟨pd₁, hp₁, hk₁, he₁⟩ |
      ⟨pd₁, hp₁, hk₁, ref₁, hra₁, hrb₁, hv₁⟩
    · cases r₂ with
      | ok s₂ =>
        exfalso
        obtain ⟨pd₂, hp₂, -, -⟩ := h₂
        rw [hp₁] at hp₂; simp at hp₂
      | error e₂ =>
        show e₁ = e₂
        rcases h₂ with ⟨hp₂, he₂⟩ | ⟨pd₂, hp₂, -, -⟩ | ⟨pd₂, hp₂, -, -⟩
        · rw [he₁, he₂]
        · rw [hp₁] at hp₂; simp at hp₂
        · rw [hp₁] at hp₂; simp at hp₂
    · cases r₂ with
      | ok s₂ =>
        exfalso
        obtain ⟨pd₂, hp₂, hk₂, -⟩ := h₂
        have hpdeq : pd₁ = pd₂ := by rw [hp₁] at hp₂; exact Option.some.inj hp₂
        rw [hpdeq, hk₂] at hk₁
        simp at hk₁
      | error e₂ =>
        show e₁ = e₂
        rcases h₂ with ⟨hp₂, he₂⟩ | ⟨pd₂, hp₂, hk₂, he₂⟩ | ⟨pd₂, hp₂, hk₂, -⟩
        · rw [hp₁] at hp₂; simp at hp₂
        · rw [he₁, he₂]
        · have hpdeq : pd₁ = pd₂ := by rw [hp₁] at hp₂; exact Option.some.inj hp₂
          rw [hpdeq, hk₂] at hk₁
          simp at hk₁
    · cases r₂ with
      | ok s₂ =>
        exfalso
        obtain ⟨pd₂, hp₂, -, ref₂, hra₂, hrb₂, hv₂, -⟩ := h₂
        have href : ref₂ = ref₁ := by
          by_cases hc : child = some node
          · rw [hra₁ hc, hra₂ hc]
          · rw [hrb₁ hc, hrb₂ hc]
        rw [href] at hv₂
        have h1 := (moveValidity_iff hwf).mp hv₁
        have h2 := (moveValidity_iff hwf).mp hv₂
        rw [h1] at h2
        simp at h2
      | error e₂ =>
        show e₁ = e₂
        rcases h₂ with ⟨hp₂, -⟩ | ⟨pd₂, hp₂, hk₂, -⟩ |
          ⟨pd₂, hp₂, hk₂, ref₂, hra₂, hrb₂, hv₂⟩
        · rw [hp₁] at hp₂; simp at hp₂
        · have hpdeq : pd₁ = pd₂ := by rw [hp₁] at hp₂; exact Option.some.inj hp₂
          rw [hpdeq, hk₂] at hk₁
          simp at hk₁
        · have href : ref₂ = ref₁ := by
            by_cases hc : child = some node
            · rw [hra₁ hc, hra₂ hc]
            · rw [hrb₁ hc, hrb₂ hc]
          rw [href] at hv₂
          have h1 := (moveValidity_iff hwf).mp hv₁
          have h2 := (moveValidity_iff hwf).mp hv₂
          rw [h1] at h2
          exact Except.error.inj h2

/-- **完全性も結果の水準で言える。** -/
theorem move_result_complete {s : DOMState} (hwf : WellFormed s.tree)
    {parent node : NodeId} {child : Option NodeId} {r : Except DOMException DOMState}
    (h : MoveResult s parent node child r) :
    ResultObsEq r (moveBefore s parent node child) :=
  move_result_deterministic hwf h (move_result_sound hwf parent node child)

end Dom.Spec
