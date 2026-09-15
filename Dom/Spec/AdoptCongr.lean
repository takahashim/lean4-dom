import Dom.Spec.RemoveCongr
import Dom.Spec.Adopt
import Dom.Properties.Algorithms

/-!
# `adopt` の congruence

`Dom/Spec/RemoveCongr.lean` と同じ目的で、`AdoptSpec` について
「入力の観測が等しければ出力の観測も等しい」を示す。

`remove` と違って transport では済まない。`AdoptSpec` の step 2 は
「parent が無ければ状態はそのまま」（`s₁ = s`）と書いてあり、これは
**その derivation の入力そのもの**を指すので、観測の等しい別の状態に差し替えられない。
そこで二つの derivation を並べたまま、段ごとに観測の一致を持ち上げる。

`DocumentAssigned` は node document しか変えないので木の well-formed も保つ。
ただし `ownerDocument_is_document` を保つには `doc` が document である必要がある。
それは `adopt` の呼び出し側（§4.2.1 の pre-insert）が保証する前提なので、
仮定として持ち回る。
-/

namespace Dom.Spec

open Dom

variable {t tb u ub : Tree} {s sb : DOMState} {node doc : NodeId}

/-! ## step 3：node document の付け替え -/

/-- 部分木の外にあるか、部分木の中で node document だけが差し替わるか、どちらかである。 -/
theorem documentAssigned_data {nd : NodeData} (hnd : t.get? node = some nd)
    (h : DocumentAssigned t u node doc) {m : NodeId} {d : NodeData} (hd : t.get? m = some d) :
    ∃ d', u.get? m = some d' ∧ d'.kind = d.kind ∧ d'.parent = d.parent ∧
      d'.children = d.children := by
  by_cases hm : InclusiveDescendant t m node
  · exact ⟨_, h.inside m d hd hm, rfl, rfl, rfl⟩
  · exact ⟨d, by rw [h.outside m hm]; exact hd, rfl, rfl, rfl⟩

/-- 木に無い node は増えない。 -/
theorem documentAssigned_none {nd : NodeData} (hnd : t.get? node = some nd)
    (h : DocumentAssigned t u node doc) {m : NodeId} (hd : t.get? m = none) : u.get? m = none := by
  have hout : ¬ InclusiveDescendant t m node := by
    intro hm
    obtain ⟨md, hmd⟩ := exists_data_of_inclusiveDescendant hnd hm
    rw [hd] at hmd
    simp at hmd
  rw [h.outside m hout, hd]

theorem documentAssigned_parentOf {nd : NodeData} (hnd : t.get? node = some nd)
    (h : DocumentAssigned t u node doc) (m : NodeId) : parentOf u m = parentOf t m := by
  cases hd : t.get? m with
  | none => rw [parentOf_eq_none_of_get?_eq_none (documentAssigned_none hnd h hd),
      parentOf_eq_none_of_get?_eq_none hd]
  | some d =>
    obtain ⟨d', hd', -, hpar, -⟩ := documentAssigned_data hnd h hd
    unfold parentOf
    rw [hd, hd']
    simp [hpar]

theorem documentAssigned_childrenOf {nd : NodeData} (hnd : t.get? node = some nd)
    (h : DocumentAssigned t u node doc) (m : NodeId) : childrenOf u m = childrenOf t m := by
  cases hd : t.get? m with
  | none => rw [childrenOf_eq_nil_of_get?_eq_none (documentAssigned_none hnd h hd),
      childrenOf_eq_nil_of_get?_eq_none hd]
  | some d =>
    obtain ⟨d', hd', -, -, hch⟩ := documentAssigned_data hnd h hd
    rw [childrenOf_eq hd', childrenOf_eq hd, hch]

/--
`DocumentAssigned` は入力の観測から出力の観測を決める。

部分木の中では node document だけが `doc` に差し替わり、外は何も変わらない。
-/
theorem documentAssigned_congr (h : TreeObsEq t tb) {nd : NodeData}
    (hnd : t.get? node = some nd)
    (h₁ : DocumentAssigned t u node doc) (h₂ : DocumentAssigned tb ub node doc) :
    TreeObsEq u ub := by
  intro m
  by_cases hm : InclusiveDescendant t m node
  · obtain ⟨md, hmd⟩ := exists_data_of_inclusiveDescendant hnd hm
    have hmb : tb.get? m = some md := by rw [h]; exact hmd
    rw [h₂.inside m md hmb (h.inclusiveAncestor_iff.mpr hm), h₁.inside m md hmd hm]
  · rw [h₂.outside m (fun hc => hm (h.inclusiveAncestor_iff.mp hc)), h₁.outside m hm, h]

/-- `DocumentAssigned` は parent と children を触らないので、well-formed を保つ。 -/
theorem documentAssigned_wellFormed (hwf : WellFormed t) {nd : NodeData}
    (hnd : t.get? node = some nd) (hdoc : IsDocument t doc)
    (h : DocumentAssigned t u node doc) : WellFormed u := by
  have hpar := documentAssigned_parentOf hnd h
  have hch := documentAssigned_childrenOf hnd h
  -- kind は変わらないので、document であることは移る。
  have hdocu : ∀ (m : NodeId) (d : NodeData), t.get? m = some d → d.kind = .document →
      ∃ d', u.get? m = some d' ∧ d'.kind = .document := by
    intro m d hd hk
    obtain ⟨d', hd', hk', -⟩ := documentAssigned_data hnd h hd
    exact ⟨d', hd', by rw [hk', hk]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p pd hpd c hc
    have hcm : c ∈ childrenOf t p := by rw [← hch p, childrenOf_eq hpd]; exact hc
    have hcp : parentOf u c = some p := by rw [hpar c]; exact parentOf_of_mem_childrenOf hwf hcm
    obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hcp
    exact ⟨cd, hcd, hcdp⟩
  · intro c cd p hcd hcdp
    have hcp : parentOf t c = some p := by rw [← hpar c]; unfold parentOf; rw [hcd]; exact hcdp
    have hmem : c ∈ childrenOf t p := mem_childrenOf_of_parentOf hwf hcp
    obtain ⟨pd, hpdt, -⟩ := exists_data_of_mem_childrenOf hmem
    obtain ⟨pd', hpd', -, -, -⟩ := documentAssigned_data hnd h hpdt
    exact ⟨pd', hpd', by rw [← childrenOf_eq hpd', hch p]; exact hmem⟩
  · intro n d hd
    cases hdt : t.get? n with
    | none => rw [documentAssigned_none hnd h hdt] at hd; simp at hd
    | some d₀ =>
      rw [← childrenOf_eq hd, hch n, childrenOf_eq hdt]
      exact hwf.children_nodup n d₀ hdt
  · intro n hn
    refine hwf.acyclic n ?_
    have key : ∀ m x : NodeId, parentOf u m = some x → parentOf t m = some x := by
      intro m x hm; rw [← hpar m]; exact hm
    have conv : ∀ {a m : NodeId}, Ancestor u a m → Ancestor t a m := by
      intro a m ha
      induction ha with
      | step hp => exact Ancestor.step (key _ _ hp)
      | trans hp _ ih => exact Ancestor.trans (key _ _ hp) ih
    exact conv hn
  · intro n d hd
    cases hdt : t.get? n with
    | none => rw [documentAssigned_none hnd h hdt] at hd; simp at hd
    | some d₀ =>
      obtain ⟨dd, hdd, hk⟩ := hdoc
      by_cases hm : InclusiveDescendant t n node
      · have : u.get? n = some { d₀ with ownerDocument := doc } := h.inside n d₀ hdt hm
        rw [this] at hd
        cases hd
        exact hdocu doc dd hdd hk
      · have : u.get? n = some d₀ := by rw [h.outside n hm]; exact hdt
        rw [this] at hd
        cases hd
        obtain ⟨dd₀, hdd₀, hk₀⟩ := hwf.ownerDocument_is_document n d hdt
        exact hdocu _ dd₀ hdd₀ hk₀


/-! ## 全体 -/

/-- `node` の node document があるなら、`node` は木にある。 -/
theorem exists_data_of_ownerDocumentOf {od : NodeId}
    (h : ownerDocumentOf t node = some od) : ∃ nd, t.get? node = some nd := by
  unfold ownerDocumentOf at h
  cases hx : t.get? node with
  | none => rw [hx] at h; simp at h
  | some nd => exact ⟨nd, rfl⟩

/-- `remove` は kind を変えないので、document は document のままである。 -/
theorem treeRemoved_isDocument {n p : NodeId} (hr : TreeRemoved t u n p)
    (hdoc : IsDocument t doc) : IsDocument u doc := by
  obtain ⟨dd, hdd, hk⟩ := hdoc
  obtain ⟨dd', hdd'⟩ := treeRemoved_exists hr hdd
  obtain ⟨hk', -⟩ := hr.sameData _ dd dd' hdd hdd'
  exact ⟨dd', hdd', by rw [hk', hk]⟩

/-- step 2 が一つの derivation について保証すること。 -/
theorem adoptStep2_facts {nd : NodeData} (hnd : s.tree.get? node = some nd) {s₁ : DOMState}
    (h : (parentOf s.tree node = none ∧ s₁ = s) ∨
      ((∃ p, parentOf s.tree node = some p) ∧ RemoveSpec s node false s₁)) :
    (∃ nd₁, s₁.tree.get? node = some nd₁) ∧ parentOf s₁.tree node = none ∧
      (∀ a b, Ancestor s₁.tree a b → Ancestor s.tree a b) ∧
      (∀ d, IsDocument s.tree d → IsDocument s₁.tree d) := by
  rcases h with ⟨hp, rfl⟩ | ⟨-, hr⟩
  · exact ⟨⟨nd, hnd⟩, hp, fun _ _ ha => ha, fun _ hd => hd⟩
  · obtain ⟨parent, -, -, -, -, -, htr, -, -⟩ := hr
    exact ⟨treeRemoved_exists htr hnd, htr.detached,
      fun _ _ ha => treeRemoved_ancestor htr ha, fun _ hd => treeRemoved_isDocument htr hd⟩

/-- step 3 が一つの derivation について保証すること。 -/
theorem adoptStep3_facts {s₁ out : DOMState} {od : NodeId} {nd₁ : NodeData}
    (hnd₁ : s₁.tree.get? node = some nd₁)
    (h : if doc = od then out = s₁
      else DocumentAssigned s₁.tree out.tree node doc ∧ LiveObjectsUnchangedExceptTree s₁ out) :
    (∀ m, parentOf out.tree m = parentOf s₁.tree m) ∧
      (∀ d, IsDocument s₁.tree d → IsDocument out.tree d) := by
  by_cases hdd : doc = od
  · rw [if_pos hdd] at h
    subst h
    exact ⟨fun _ => rfl, fun _ hd => hd⟩
  · rw [if_neg hdd] at h
    obtain ⟨hda, -⟩ := h
    refine ⟨documentAssigned_parentOf hnd₁ hda, fun d hd => ?_⟩
    obtain ⟨dd, hdd', hk⟩ := hd
    obtain ⟨dd', hdd'', hk', -⟩ := documentAssigned_data hnd₁ hda hdd'
    exact ⟨dd', hdd'', by rw [hk', hk]⟩

/-- **`adopt` の後、node は parent を持たない**（step 2）。 -/
theorem adoptSpec_detached {out : DOMState} (hq : AdoptSpec s node doc out) :
    parentOf out.tree node = none := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := hq
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
  obtain ⟨⟨nd₁, hnd₁⟩, hdet, -, -⟩ := adoptStep2_facts hnd hst2
  rw [(adoptStep3_facts hnd₁ hst3).1 node]
  exact hdet

/-- `adopt` は ancestor を増やさない。 -/
theorem adoptSpec_ancestor {out : DOMState} (hq : AdoptSpec s node doc out)
    {a b : NodeId} (h : Ancestor out.tree a b) : Ancestor s.tree a b := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := hq
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
  obtain ⟨⟨nd₁, hnd₁⟩, -, hanc, -⟩ := adoptStep2_facts hnd hst2
  have hpar := (adoptStep3_facts hnd₁ hst3).1
  refine hanc a b ?_
  induction h with
  | step hp => exact Ancestor.step (by rw [← hpar]; exact hp)
  | trans hp _ ih => exact Ancestor.trans (by rw [← hpar]; exact hp) ih

/-- `adopt` は kind を変えないので、document は document のままである。 -/
theorem adoptSpec_isDocument {out : DOMState} (hq : AdoptSpec s node doc out) {d : NodeId}
    (hd : IsDocument s.tree d) : IsDocument out.tree d := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := hq
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
  obtain ⟨⟨nd₁, hnd₁⟩, -, -, hkeep⟩ := adoptStep2_facts hnd hst2
  exact (adoptStep3_facts hnd₁ hst3).2 d (hkeep d hd)

/-- `AdoptSpec` の step 2 が二つの derivation を揃えることを言う。 -/
theorem adoptSpec_step2 (hwf : WellFormed s.tree) (h : ObsEq s sb) {s₁ s₂ : DOMState}
    (h₁ : (parentOf s.tree node = none ∧ s₁ = s) ∨
      ((∃ p, parentOf s.tree node = some p) ∧ RemoveSpec s node false s₁))
    (h₂ : (parentOf sb.tree node = none ∧ s₂ = sb) ∨
      ((∃ p, parentOf sb.tree node = some p) ∧ RemoveSpec sb node false s₂)) :
    ObsEq s₁ s₂ ∧ WellFormed s₁.tree := by
  rcases h₁ with ⟨hp₁, rfl⟩ | ⟨-, hr₁⟩
  · rcases h₂ with ⟨-, rfl⟩ | ⟨⟨p₂, hp₂⟩, -⟩
    · exact ⟨h, hwf⟩
    · exfalso
      rw [h.tree.parentOf, hp₁] at hp₂
      simp at hp₂
  · rcases h₂ with ⟨hp₂, rfl⟩ | ⟨-, hr₂⟩
    · exfalso
      obtain ⟨parent, -, hpre, -⟩ := hr₁
      rw [h.tree.parentOf, hpre] at hp₂
      simp at hp₂
    · exact ⟨removeSpec_congr hwf h hr₁ hr₂, removeSpec_wellFormed hwf hr₁⟩

/--
**`AdoptSpec` の congruence。**

step 2 の `remove` は `removeSpec_congr`、step 3 の node document 付け替えは
`documentAssigned_congr` で持ち上げる。木以外の成分は
`LiveObjectsUnchangedExceptTree` が中間状態と結び付けてくれる。
-/
theorem adoptSpec_congr (hwf : WellFormed s.tree) (h : ObsEq s sb) {o₁ o₂ : DOMState}
    (h₁ : AdoptSpec s node doc o₁) (h₂ : AdoptSpec sb node doc o₂) : ObsEq o₁ o₂ := by
  obtain ⟨od₁, hod₁, s₁, hst2₁, hst3₁⟩ := h₁
  obtain ⟨od₂, hod₂, s₂, hst2₂, hst3₂⟩ := h₂
  have hodeq : od₂ = od₁ := by
    have hw := h.tree.ownerDocumentOf node
    rw [hod₁, hod₂] at hw
    exact Option.some.inj hw
  subst hodeq
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod₁
  obtain ⟨hobs, hwf₁⟩ := adoptSpec_step2 hwf h hst2₁ hst2₂
  obtain ⟨⟨nd₁, hnd₁⟩, -, -, -⟩ := adoptStep2_facts hnd hst2₁
  by_cases hdd : doc = od₂
  · rw [if_pos hdd] at hst3₁ hst3₂
    subst hst3₁; subst hst3₂
    exact hobs
  · rw [if_neg hdd] at hst3₁ hst3₂
    obtain ⟨hda₁, hl₁⟩ := hst3₁
    obtain ⟨hda₂, hl₂⟩ := hst3₂
    exact
      { tree := documentAssigned_congr hobs.tree hnd₁ hda₁ hda₂
        ranges := by rw [hl₂.ranges, hobs.ranges, hl₁.ranges]
        iterators := by rw [hl₂.iterators, hobs.iterators, hl₁.iterators]
        registrations := fun r => by
          rw [hl₂.registrations, hl₁.registrations]; exact hobs.registrations r
        records := fun mo => by rw [hl₂.observers, hl₁.observers]; exact hobs.records mo
        pendingObservers := fun mo => by
          rw [hl₂.pendingObservers, hl₁.pendingObservers]; exact hobs.pendingObservers mo
        microtaskQueued := by
          rw [hl₂.microtaskQueued, hobs.microtaskQueued, hl₁.microtaskQueued] }

/--
`AdoptSpec` の結果も well-formed である。

`doc` が document であることは `adopt` 自身は保証しない。§4.2.1 の pre-insert が
document から呼ぶので、呼び出し側の前提として仮定する。
-/
theorem adoptSpec_wellFormed (hwf : WellFormed s.tree) (hdoc : IsDocument s.tree doc)
    {out : DOMState} (hq : AdoptSpec s node doc out) : WellFormed out.tree := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := hq
  obtain ⟨nd, hnd⟩ := exists_data_of_ownerDocumentOf hod
  obtain ⟨-, hwf₁⟩ := adoptSpec_step2 hwf (ObsEq.refl s) hst2 hst2
  obtain ⟨⟨nd₁, hnd₁⟩, -, -, hkeep⟩ := adoptStep2_facts hnd hst2
  by_cases hdd : doc = od
  · rw [if_pos hdd] at hst3
    subst hst3
    exact hwf₁
  · rw [if_neg hdd] at hst3
    obtain ⟨hda, hl⟩ := hst3
    exact documentAssigned_wellFormed hwf₁ hnd₁ (hkeep doc hdoc) hda

/-- **`AdoptSpec` は観測を一つに決める。** -/
theorem adoptSpec_deterministic (hwf : WellFormed s.tree) {o₁ o₂ : DOMState}
    (h₁ : AdoptSpec s node doc o₁) (h₂ : AdoptSpec s node doc o₂) : ObsEq o₁ o₂ :=
  adoptSpec_congr hwf (ObsEq.refl s) h₁ h₂


/--
`adopt` は、対象の node 自身の kind と children を変えない。

step 2 の `remove` は node を親から外すだけで node の children には触れず、
step 3 は node document しか書き換えないからである。
-/
theorem adoptSpec_selfData (hwf : WellFormed s.tree) {out : DOMState}
    (hq : AdoptSpec s node doc out) {nd : NodeData} (hnd : s.tree.get? node = some nd) :
    ∃ nd', out.tree.get? node = some nd' ∧ nd'.kind = nd.kind ∧ nd'.children = nd.children := by
  obtain ⟨od, hod, s₁, hst2, hst3⟩ := hq
  -- step 2
  obtain ⟨nd₁, hnd₁, hk₁, hch₁⟩ :
      ∃ nd₁, s₁.tree.get? node = some nd₁ ∧ nd₁.kind = nd.kind ∧ nd₁.children = nd.children := by
    rcases hst2 with ⟨-, rfl⟩ | ⟨-, hr⟩
    · exact ⟨nd, hnd, rfl, rfl⟩
    · refine removeSpec_data hr hnd fun p hp he => ?_
      subst he
      exact hwf.acyclic _ (Ancestor.step hp)
  -- step 3
  by_cases hdd : doc = od
  · rw [if_pos hdd] at hst3
    subst hst3
    exact ⟨nd₁, hnd₁, hk₁, hch₁⟩
  · rw [if_neg hdd] at hst3
    obtain ⟨hda, -⟩ := hst3
    obtain ⟨nd', hnd', hk', -, hch'⟩ := documentAssigned_data hnd₁ hda hnd₁
    exact ⟨nd', hnd', by rw [hk', hk₁], by rw [hch', hch₁]⟩

end Dom.Spec
