import Dom.Spec.RemoveCongr
import Dom.Spec.AdoptCongr
import Dom.Spec.InsertCongr
import Dom.Spec.InsertSound
import Dom.Properties.Contract

/-!
# 関係を満たす状態は、実行関数が実際に作る

soundness（`Dom/Spec/RemoveSound.lean` ほか）は「実行関数の結果は関係を満たす」を言う。
その逆、**completeness** は二つに分かれる。

1. **余計な model が無いこと**：関係を満たす状態は、実行関数が作る状態と観測が等しい。
   これは soundness と一意性（`Dom/Spec/RemoveCongr.lean` ほか）から出る。
2. **実現できること**：関係が満たせるなら、実行関数は失敗しない。
   これは契約（`Dom/Properties/Contract.lean`）から出る。

二つ合わせて「関係と実行関数は観測の上で同じものを表す」と言える。
soundness だけだと、関係が緩くても（あるいは満たせなくても）成り立ってしまう。
-/

namespace Dom.Spec

open Dom

/-! ## `remove` -/

/--
**`RemoveSpec` を満たす状態があるなら、`remove` は成功してその観測を作る。**

関係の step 1-2（parent が非 null）がそのまま契約の成功条件である。
-/
theorem remove_complete {s s' : DOMState} {n : NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (h : RemoveSpec s n b s') : ∃ out, remove s n b = .ok out ∧ ObsEq s' out := by
  have hc := h
  obtain ⟨parent, -, hpre, -⟩ := hc
  obtain ⟨out, hout⟩ := (remove_succeeds_iff hwf (n := n) (b := b)).mpr (by rw [hpre]; rfl)
  exact ⟨out, hout, removeSpec_congr hwf (ObsEq.refl s) h (remove_sound hwf hout)⟩

/-! ## `adopt` -/

/--
`adopt` が成功する条件は step 1 だけである。

step 2 の `remove` は parent がある node にしか呼ばないので、そこでは失敗しない。
-/
theorem adopt_succeeds_of_ownerDocument {s : DOMState} {node doc oldDoc : NodeId}
    (hwf : WellFormed s.tree) (h : ownerDocumentOf s.tree node = some oldDoc) :
    ∃ out, adopt s node doc = .ok out := by
  cases hp : parentOf s.tree node with
  | none => exact ⟨_, adopt_of_steps h (Or.inl ⟨hp, rfl⟩)⟩
  | some p =>
    obtain ⟨s₁, hs₁⟩ := (remove_succeeds_iff hwf (n := node) (b := false)).mpr (by rw [hp]; rfl)
    exact ⟨_, adopt_of_steps h (Or.inr ⟨⟨p, hp⟩, hs₁⟩)⟩

/-- **`AdoptSpec` を満たす状態があるなら、`adopt` は成功してその観測を作る。** -/
theorem adopt_complete {s s' : DOMState} {node doc : NodeId} (hwf : WellFormed s.tree)
    (h : AdoptSpec s node doc s') : ∃ out, adopt s node doc = .ok out ∧ ObsEq s' out := by
  have hc := h
  obtain ⟨oldDoc, hod, -⟩ := hc
  obtain ⟨out, hout⟩ := adopt_succeeds_of_ownerDocument (doc := doc) hwf hod
  exact ⟨out, hout, adoptSpec_congr hwf (ObsEq.refl s) h (adopt_sound hwf hout)⟩

/-! ## `insert` -/

/--
**`InsertSpec` に余計な model は無い。**

`insert` が成功するなら、関係を満たす状態はその結果と観測が等しい。
「関係を満たせるなら `insert` は成功する」（実現できること）のほうは、
`insertAt` の step 4（`child` が `parent` の子であること）を関係が述べていないので
まだ言えない。仕様ではその検査は `insert` の呼び出し側（pre-insert）にある。
-/
theorem insert_no_extra_models {s s' out : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hwf : WellFormed s.tree)
    (hacyc : ∀ ns : List NodeId, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h : InsertSpec s node parent child b s') (hok : insert s node parent child b = .ok out) :
    ObsEq s' out :=
  insertSpec_congr hwf (ObsEq.refl s) hacyc h (insert_sound hwf hok)

end Dom.Spec
