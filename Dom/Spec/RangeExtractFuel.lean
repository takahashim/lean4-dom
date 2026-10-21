import Dom.Spec.RangeExtractSound

/-!
# extract・clone the contents の fuel は足りる

`contentsInto` は fuel で再帰を打ち切る。呼び出し側（`rangeExtractContents`・`rangeCloneContents`）は
`Tree.size + 1` を渡す。ここでは、range の start が end より後になく、両端が木にあれば、その fuel から
先はいくら fuel を足しても結果が変わらないことを示す（`rangeExtractContents_fuel`・
`rangeCloneContents_fuel`）。fuel が尽きた `outsideModel` は、この範囲では返らない。

## 再帰の深さ

再帰で渡る subrange は、一番上の階を除けば片側だけである。first partially contained child の側は
(start, (child, child の length)) で、end node が start node の inclusive ancestor になる。last の側は
((child, 0), end) で、start node が end node の inclusive ancestor になる。片側の range の common ancestor は
その祖先の側の node で、次の階の subrange はそこから端点へ一段下りる。だから必要な fuel は、端点と common
ancestor の depth の差で抑えられる（`FuelEnough`）。

一番上の階の first の側が start 側の子であることは、range の start が end より後にないことから出る
（`firstPartial_toward_start`）。後ろ向きの range では first partially contained child が end 側の子になり、
同じ subrange で再帰し続けて fuel が尽きる。

## 一番上の階の last の側

last の側の再帰は、first の側の再帰と contained children の移動を経た状態で走る。そこで end node の
inclusive ancestor の parent が、その間に変わらないことを示す（`contentsInto_frame_first`、
`appendEach_frame`）。動くのは、first の側の child の strict descendant と contained children と、
新しく作った node だけである。
-/

namespace Dom.Spec

open Dom

/-! ## parent が変わらない node -/

section Transport

variable {t t' : Tree}

/-- 木にあった node の parent が変わらなければ、新しい木の ancestor 関係は古い木のものである。 -/
theorem ancestor_of_parents_kept (hwf : WellFormed t)
    (hk : ∀ m, InTree t m → parentOf t' m = parentOf t m) {a : NodeId} :
    ∀ {m : NodeId}, Ancestor t' a m → InTree t m → Ancestor t a m := by
  intro m h hm
  induction h with
  | step hp => exact .step (by rw [← hk _ hm]; exact hp)
  | @trans b n hp _ ih =>
    have hp' : parentOf t n = some b := by rw [← hk _ hm]; exact hp
    exact .trans hp' (ih (exists_data_of_parentOf hwf hp'))

/-- `n` の inclusive ancestor の parent が変わらなければ、`n` の ancestor は新しい木でも ancestor である。 -/
theorem ancestor_of_chain_kept {n : NodeId}
    (hk : ∀ x, InclusiveAncestor t x n → parentOf t' x = parentOf t x) {a : NodeId}
    (h : Ancestor t a n) : Ancestor t' a n := by
  induction h with
  | step hp => exact .step (by rw [hk _ (Or.inl rfl)]; exact hp)
  | @trans b n hp hab ih =>
    refine .trans (by rw [hk _ (Or.inl rfl)]; exact hp) (ih fun x hx => hk x ?_)
    rcases hx with rfl | hx
    · exact Or.inr (.step hp)
    · exact Or.inr (.trans hp hx)

theorem inclusiveAncestor_of_chain_kept {n : NodeId}
    (hk : ∀ x, InclusiveAncestor t x n → parentOf t' x = parentOf t x) {a : NodeId}
    (h : InclusiveAncestor t a n) : InclusiveAncestor t' a n := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (ancestor_of_chain_kept hk h)

/-- `n` の inclusive ancestor の parent が変わらなければ、`n` の depth は変わらない。 -/
theorem depth_of_chain_kept (hwf : WellFormed t) (hwf' : WellFormed t') :
    ∀ (k : Nat) {n : NodeId}, depth t n ≤ k →
      (∀ x, InclusiveAncestor t x n → parentOf t' x = parentOf t x) → depth t' n = depth t n := by
  intro k
  induction k with
  | zero =>
    intro n hd hk
    have hp : parentOf t n = none := parentOf_eq_none_of_depth_zero hwf (by omega)
    have hp' : parentOf t' n = none := by rw [hk _ (Or.inl rfl)]; exact hp
    rw [depth_eq_zero_of_parent_none hp', depth_eq_zero_of_parent_none hp]
  | succ k ih =>
    intro n hd hk
    cases hp : parentOf t n with
    | none =>
      have hp' : parentOf t' n = none := by rw [hk _ (Or.inl rfl)]; exact hp
      rw [depth_eq_zero_of_parent_none hp', depth_eq_zero_of_parent_none hp]
    | some p =>
      have hp' : parentOf t' n = some p := by rw [hk _ (Or.inl rfl)]; exact hp
      rw [depth_parent hwf' hp', depth_parent hwf hp]
      rw [depth_parent hwf hp] at hd
      rw [ih (by omega) fun x hx => hk x ?_]
      rcases hx with rfl | hx
      · exact Or.inr (.step hp)
      · exact Or.inr (.trans hp hx)

end Transport

/-- common ancestor は一つに決まる。 -/
theorem commonAncestor_unique {t : Tree} {r : RangeState} {a b : NodeId}
    (ha : CommonAncestor t r a) (hb : CommonAncestor t r b) : a = b := by
  rcases inclusive_ancestor_linear ha.1 hb.1 with h | h
  · rcases h with h | h
    · exact h
    · exact absurd hb.2.1 (ha.2.2 b hb.1 h)
  · rcases h with h | h
    · exact h.symm
    · exact absurd ha.2.1 (hb.2.2 a ha.1 h)

/-! ## 部品は、木にあった node の parent を動かさない -/

/-- fragment でない node の `append` が parent を動かすのは、その node だけである。 -/
theorem parentOf_append_ne {s s' : DOMState} {c p : NodeId} {cd : NodeData}
    (hcd : s.tree.get? c = some cd) (hk : cd.kind ≠ .documentFragment)
    (h : append s c p = .ok s') {m : NodeId} (hm : m ≠ c) :
    parentOf s'.tree m = parentOf s.tree m := by
  obtain ⟨-, hi⟩ := preInsert_cases h
  obtain ⟨pd, s₁, -, ha, hia, -⟩ := insert_single hcd (by simpa using hk) hi
  rw [parentOf_insertAt_other hia hm, parentOf_adopt_ne ha hm, liveRangeInsertAdjust_tree]

/-- 入れる node の列に無い node の parent は、`insertEach` で動かない。 -/
theorem parentOf_insertEach_of_not_mem :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId} {doc : NodeId},
      insertEach s parent child doc ns = .ok s' →
      ∀ m, m ∉ ns → parentOf s'.tree m = parentOf s.tree m
  | [], s, s', _, _, _, h, m, _ => by rw [insertEach] at h; cases h; rfl
  | n :: ns, s, s', parent, child, doc, h, m, hm => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      split at h
      · simp at h
      · next s₂ hi =>
        have hmn : m ≠ n := fun he => hm (by simp [he])
        obtain ⟨hi₁, -⟩ := DOMState.mapTree_eq_ok hi
        rw [parentOf_insertEach_of_not_mem ns h m (fun h' => hm (by simp [h'])),
          parentOf_insertAt_other hi₁ hmn, parentOf_adopt_ne ha hmn]

theorem parentOf_insertNodesAt_of_not_mem {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
    {ns : List NodeId} {b : Bool} (h : insertNodesAt s parent child ns b = .ok s') {m : NodeId}
    (hm : m ∉ ns) : parentOf s'.tree m = parentOf s.tree m := by
  obtain ⟨sx, hx, hstep⟩ := insertNodesAt_cases h
  obtain ⟨pd, -, hie⟩ := insertEachAt_cases hx
  have hsx := parentOf_insertEach_of_not_mem ns hie m hm
  rw [liveRangeInsertAdjust_tree] at hsx
  rcases hstep with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hsx
  · rw [queueTreeMutationRecord_tree]; exact hsx

/-- `append` が parent を動かすのは、入れる node と、それが fragment ならその子だけである。 -/
theorem parentOf_append_of_not_mem {s s' : DOMState} {c p : NodeId} (h : append s c p = .ok s')
    {m : NodeId} (hmc : m ≠ c) (hm : m ∉ childrenOf s.tree c) :
    parentOf s'.tree m = parentOf s.tree m := by
  obtain ⟨-, hi⟩ := preInsert_cases h
  obtain ⟨nd, hnd, hcase⟩ := insert_cases hi
  rw [childrenOf_eq hnd] at hm
  rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, s₁, hr, hins⟩ | ⟨-, hins⟩
  · rfl
  · rw [parentOf_insertNodesAt_of_not_mem hins hm, queueTreeMutationRecord_tree,
      parentOf_removeEach_of_not_mem _ hr hm]
  · exact parentOf_insertNodesAt_of_not_mem hins (by simpa using hmc)

/-- `append` は node の kind を変えない。 -/
theorem kind_append {s s' : DOMState} {c p m : NodeId} {md : NodeData}
    (h : append s c p = .ok s') (hmd : s.tree.get? m = some md) :
    ∃ md', s'.tree.get? m = some md' ∧ md'.kind = md.kind :=
  keeps_of_shapePreserving (shapePreserving_append h) hmd

/-- clone は新しい node を一つ足すだけで、木にあった node の data を変えない。 -/
theorem cloneSingle_get? {s : DOMState} {x : NodeData} {doc m : NodeId} {md : NodeData}
    (hmd : s.tree.get? m = some md) : (cloneSingle s x doc).2.tree.get? m = some md :=
  withFresh_get?_of_some hmd _

theorem cloneSingle_fresh (s : DOMState) (x : NodeData) (doc : NodeId) :
    s.tree.get? (cloneSingle s x doc).1 = none :=
  freshId_get?_eq_none s.tree

theorem cloneSingle_created (s : DOMState) (x : NodeData) (doc : NodeId) :
    ∃ cd, (cloneSingle s x doc).2.tree.get? (cloneSingle s x doc).1 = some cd ∧ cd.kind = x.kind :=
  ⟨_, get?_insertNode_self _ _ _, rfl⟩

/-- 木にあった node の parent が変わらず、木にあった node は残る。 -/
def ParentsKept (s s' : DOMState) : Prop :=
  ∀ m md, s.tree.get? m = some md →
    (∃ md', s'.tree.get? m = some md' ∧ md'.kind = md.kind) ∧ parentOf s'.tree m = parentOf s.tree m

theorem ParentsKept.refl (s : DOMState) : ParentsKept s s :=
  fun _ md hmd => ⟨⟨md, hmd, rfl⟩, rfl⟩

theorem ParentsKept.trans {s₁ s₂ s₃ : DOMState} (h₁ : ParentsKept s₁ s₂) (h₂ : ParentsKept s₂ s₃) :
    ParentsKept s₁ s₃ := fun m md hmd => by
  obtain ⟨⟨md', hmd', hk⟩, hp⟩ := h₁ m md hmd
  obtain ⟨⟨md'', hmd'', hk'⟩, hp'⟩ := h₂ m md' hmd'
  exact ⟨⟨md'', hmd'', hk'.trans hk⟩, hp'.trans hp⟩

theorem ParentsKept.parentOf {s s' : DOMState} (h : ParentsKept s s') {m : NodeId}
    (hm : InTree s.tree m) : Dom.parentOf s'.tree m = Dom.parentOf s.tree m := by
  obtain ⟨md, hmd⟩ := hm
  exact (h m md hmd).2

theorem ParentsKept.inTree {s s' : DOMState} (h : ParentsKept s s') {m : NodeId}
    (hm : InTree s.tree m) : InTree s'.tree m := by
  obtain ⟨md, hmd⟩ := hm
  obtain ⟨⟨md', hmd', -⟩, -⟩ := h m md hmd
  exact ⟨md', hmd'⟩

/-- clone を作って append する。clone は新しい node なので、木にあった node の parent は動かない。 -/
theorem parentsKept_cloneAppend {s s₁ s' : DOMState} {x : NodeData} {doc into c : NodeId}
    (hk : x.kind ≠ .documentFragment) (hcs : cloneSingle s x doc = (c, s₁))
    (h : append s₁ c into = .ok s') : ParentsKept s s' := by
  intro m md hmd
  have h₁ : s₁.tree.get? m = some md := by
    have := cloneSingle_get? (x := x) (doc := doc) hmd; rw [hcs] at this; exact this
  obtain ⟨cd, hcd, hck⟩ : ∃ cd, s₁.tree.get? c = some cd ∧ cd.kind = x.kind := by
    have := cloneSingle_created s x doc; rw [hcs] at this; exact this
  have hne : m ≠ c := by
    intro he
    have := cloneSingle_fresh s x doc
    rw [hcs] at this
    rw [he, this] at hmd; cases hmd
  refine ⟨kind_append h h₁, ?_⟩
  rw [parentOf_append_ne hcd (by rw [hck]; exact hk) h hne]
  exact parentOf_congr (h₁.trans hmd.symm)

theorem parentsKept_appendShallowClone {s s' : DOMState} {d : NodeData} {into c : NodeId}
    (hk : d.kind ≠ .documentFragment) (h : appendShallowClone s d into = .ok (c, s')) :
    ParentsKept s s' := by
  unfold appendShallowClone at h
  rcases hcs : cloneSingle s d d.ownerDocument with ⟨c₀, s₁⟩
  simp only [hcs] at h
  split at h
  · simp at h
  · next s₂ ha => cases h; exact parentsKept_cloneAppend hk hcs ha

theorem parentsKept_appendDataClone {s s' : DOMState} {d : NodeData} {x : String} {into : NodeId}
    (hk : d.kind ≠ .documentFragment) (h : appendDataClone s d x into = .ok s') :
    ParentsKept s s' := by
  unfold appendDataClone at h
  rcases hcs : cloneSingle s { d with data := x } d.ownerDocument with ⟨c₀, s₁⟩
  simp only [hcs] at h
  split at h
  · simp at h
  · next s₂ ha => cases h; exact parentsKept_cloneAppend (x := { d with data := x }) hk hcs ha

theorem parentsKept_replaceData {s s' : DOMState} {n : NodeId} {o c : Nat} {x : String}
    (h : replaceData s n o c x = .ok s') : ParentsKept s s' := by
  obtain ⟨d, _, hd, _, _, _, htree, _, _⟩ := replaceData_ok h
  intro m md hmd
  refine ⟨keeps_of_shapePreserving (shapePreserving_replaceData h) hmd, ?_⟩
  rw [htree, parentOf_withData hd]

/-- CharacterData の一部を写す。写す node は CharacterData なので fragment でない。 -/
theorem parentsKept_dataPart {cut : Bool} {s s' : DOMState} {n into : NodeId} {o c : Nat}
    (h : dataPart cut s n o c into = .ok s') : ParentsKept s s' := by
  unfold dataPart at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · next hcd =>
      have hk : d.kind ≠ .documentFragment := by
        intro he; rw [he] at hcd; exact absurd hcd (by decide)
      split at h
      · simp at h
      · split at h
        · simp at h
        · next s₁ ha =>
          have h₁ := parentsKept_appendDataClone hk ha
          split at h
          · exact h₁.trans (parentsKept_replaceData (failWith_ok.mp h))
          · cases h; exact h₁

/-- contained children を順に append する。動くのは contained children の parent だけである。 -/
theorem appendEach_frame {into : NodeId} :
    ∀ (cs : List NodeId) {s s' : DOMState},
      (∀ c ∈ cs, ∃ cd, s.tree.get? c = some cd ∧ cd.kind ≠ .documentFragment) →
      appendEach s into cs = .ok s' →
      ∀ m md, s.tree.get? m = some md →
        (∃ md', s'.tree.get? m = some md' ∧ md'.kind = md.kind) ∧
          (m ∉ cs → parentOf s'.tree m = parentOf s.tree m)
  | [], s, s', _, h, m, md, hmd => by cases h; exact ⟨⟨md, hmd, rfl⟩, fun _ => rfl⟩
  | c :: cs, s, s', hk, h, m, md, hmd => by
    unfold appendEach at h
    split at h
    · simp at h
    · next s₁ ha =>
      obtain ⟨cd, hcd, hck⟩ := hk c (by simp)
      have hk₁ : ∀ c' ∈ cs, ∃ cd, s₁.tree.get? c' = some cd ∧ cd.kind ≠ .documentFragment := by
        intro c' hc'
        obtain ⟨cd', hcd', hk'⟩ := hk c' (by simp [hc'])
        obtain ⟨cd'', hcd'', he⟩ := kind_append ha hcd'
        exact ⟨cd'', hcd'', by rw [he]; exact hk'⟩
      obtain ⟨md₁, hmd₁, hk₁m⟩ := kind_append ha hmd
      obtain ⟨⟨md', hmd', hkm⟩, hp⟩ := appendEach_frame cs hk₁ h m md₁ hmd₁
      refine ⟨⟨md', hmd', hkm.trans hk₁m⟩, fun hm => ?_⟩
      rw [hp (fun h' => hm (by simp [h'])),
        parentOf_append_ne hcd hck ha (fun h' => hm (by simp [h']))]

/-- contained children を subtree ごと clone して append する。動くのは新しい node だけである。 -/
theorem cloneEach_frame {into : NodeId} :
    ∀ (cs : List NodeId) {s s' : DOMState}, AdmissibleDOMState s →
      (∀ c ∈ cs, ∃ cd, s.tree.get? c = some cd ∧ cd.kind ≠ .documentFragment) →
      cloneEach s into cs = .ok s' → ParentsKept s s'
  | [], s, s', _, _, h => by cases h; exact ParentsKept.refl s
  | c :: cs, s, s', hv, hk, h => by
    unfold cloneEach at h
    split at h
    · simp at h
    · next cd hcd =>
      split at h
      · simp at h
      · next copy s₁ hc =>
        split at h
        · simp at h
        · next s₂ ha =>
          have hdoc := hv.wellFormed.ownerDocument_is_document c cd hcd
          obtain ⟨d, hd, hkeep, hfresh, hclone, -, -⟩ := cloneNodeIn_deep_spec hv hdoc hc
          rw [hcd] at hd; cases hd
          obtain ⟨R, hR, hstep⟩ := hclone
          obtain ⟨cpd, cd', hcpd, hcd', hshape, -⟩ := hstep _ _ hR
          rw [hkeep c cd hcd] at hcd'; cases hcd'
          have hck : cpd.kind ≠ .documentFragment := by
            rw [← NodeData.shapeAnon_kind, hshape, NodeData.shapeAnon_kind]
            obtain ⟨cd₀, hcd₀, hk₀⟩ := hk c (by simp)
            rw [hcd] at hcd₀; cases hcd₀; exact hk₀
          have h₁₂ : ParentsKept s s₂ := by
            intro m md hmd
            have hm₁ := hkeep m md hmd
            have hne : m ≠ copy := by intro he; rw [he, hfresh] at hmd; cases hmd
            exact ⟨kind_append ha hm₁, by
              rw [parentOf_append_ne hcpd hck ha hne]; exact parentOf_congr (hm₁.trans hmd.symm)⟩
          have hv₂ : AdmissibleDOMState s₂ :=
            admissible_append (admissible_cloneNodeIn hv hdoc hc) ha
          refine h₁₂.trans (cloneEach_frame cs hv₂ (fun c' hc' => ?_) h)
          obtain ⟨cd', hcd', hk'⟩ := hk c' (by simp [hc'])
          obtain ⟨⟨cd'', hcd'', he⟩, -⟩ := h₁₂ c' cd' hcd'
          exact ⟨cd'', hcd'', by rw [he]; exact hk'⟩

/-! ## 片側の range -/

/-- end node が start node の inclusive ancestor なら、end node が common ancestor である。 -/
theorem commonAncestor_of_end_above {t : Tree} {r : RangeState} (hwf : WellFormed t)
    (h : InclusiveAncestor t r.«end».node r.start.node) : CommonAncestor t r r.«end».node := by
  refine ⟨h, Or.inl rfl, fun x _ hax hx => ?_⟩
  rcases hx with rfl | hx
  · exact hwf.acyclic _ hax
  · exact hwf.acyclic _ (hax.trans_ancestor hx)

/-- start node が end node の inclusive ancestor なら、start node が common ancestor である。 -/
theorem commonAncestor_of_start_above {t : Tree} {r : RangeState} (hwf : WellFormed t)
    (h : InclusiveAncestor t r.start.node r.«end».node) : CommonAncestor t r r.start.node := by
  refine ⟨Or.inl rfl, h, fun x hx hax _ => ?_⟩
  rcases hx with rfl | hx
  · exact hwf.acyclic _ hax
  · exact hwf.acyclic _ (hax.trans_ancestor hx)

/-- 木の中で parent を持つ node は DocumentFragment でない。 -/
theorem not_fragment_of_parent {s : DOMState} (h : AdmissibleDOMState s) {n p : NodeId}
    {d : NodeData} (hd : s.tree.get? n = some d) (hp : parentOf s.tree n = some p) :
    d.kind ≠ .documentFragment := by
  intro hk
  have := h.structural.fragmentHasNoParent n d hd hk
  rw [parentOf_of_get? hd, this] at hp
  cases hp

/-- common ancestor の子は木にあって DocumentFragment でない。 -/
theorem child_not_fragment {s : DOMState} (h : AdmissibleDOMState s) {ca x : NodeId}
    (hx : x ∈ childrenOf s.tree ca) : ∃ xd, s.tree.get? x = some xd ∧ xd.kind ≠ .documentFragment := by
  have hp := (mem_childrenOf_iff h.wellFormed x ca).mpr hx
  obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hp
  exact ⟨xd, hxd, not_fragment_of_parent h hxd hp⟩

/-- 再帰が、木にあって `a` の strict descendant でない node の parent を動かさないこと。 -/
def RecurFrame (recur : Recur) : Prop :=
  ∀ s r c s', AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node →
    InclusiveAncestor s.tree r.«end».node r.start.node → recur s r c = .ok s' →
    ∀ m, InTree s.tree m → ¬ Ancestor s.tree r.«end».node m → parentOf s'.tree m = parentOf s.tree m

/-- step 1 の fragment は新しい node で、木にあった node の parent を動かさない。 -/
theorem rangeFragment_fresh {s s₁ : DOMState} {r : RangeState} {sub : NodeId}
    (h : rangeFragment s r = .ok (sub, s₁)) : s.tree.get? sub = none := by
  unfold rangeFragment at h
  split at h
  · simp at h
  · unfold createDocumentFragment at h
    split at h
    · simp at h
    · cases h
      exact freshId_get?_eq_none s.tree

theorem parentsKept_rangeFragment {s s₁ : DOMState} {r : RangeState} {sub : NodeId}
    (h : rangeFragment s r = .ok (sub, s₁)) : ParentsKept s s₁ := fun m md hmd => by
  have h₁ := rangeFragment_get? h hmd
  exact ⟨⟨md, h₁, rfl⟩, parentOf_congr (h₁.trans hmd.symm)⟩

/--
subrange を subfragment へ extract して clone に append する部分の frame。subrange の end node が start node の
inclusive ancestor なら、動くのは新しい node と、end node の strict descendant だけである。subfragment に入る木の
node は再帰で parent が変わったものなので、clone への append もそれ以外を動かさない。
-/
theorem subContents_frame {recur : Recur} {s s' : DOMState} {r : RangeState} {c : NodeId}
    (hrec : RecurFrame recur) (hrk : ∀ s₀, RecurClosed (Keeps s₀) recur) (h : AdmissibleDOMState s)
    (hs : InTree s.tree r.start.node) (he : InTree s.tree r.«end».node)
    (hab : InclusiveAncestor s.tree r.«end».node r.start.node)
    (hr : subContents recur s r c = .ok s') :
    ∀ m, InTree s.tree m → ¬ Ancestor s.tree r.«end».node m → parentOf s'.tree m = parentOf s.tree m := by
  have hwf := h.wellFormed
  intro m hm hnm
  unfold subContents at hr
  split at hr
  · simp at hr
  · next sub s₁ hf =>
    have hk₁ := parentsKept_rangeFragment hf
    have hkeep₁ : Keeps s s₁ := (keeps_contentsClosed s).fragment (keeps_refl h) hf
    have hfresh := rangeFragment_fresh hf
    split at hr
    · simp at hr
    · next s₂ hs₂ =>
      have hab₁ : InclusiveAncestor s₁.tree r.«end».node r.start.node :=
        inclusiveAncestor_of_chain_kept (fun y hy => hk₁.parentOf (inTree_of_inclusiveAncestor hwf hs hy)) hab
      have hm₁ := hk₁.inTree hm
      have hnm₁ : ¬ Ancestor s₁.tree r.«end».node m := fun ha =>
        hnm (ancestor_of_parents_kept hwf (fun _ hy => hk₁.parentOf hy) ha hm)
      have e₂ := hrec s₁ r sub s₂ hkeep₁.1 (hkeep₁.inTree hs) (hkeep₁.inTree he) hab₁ hs₂ m hm₁ hnm₁
      have hwf₂ := (hrk s₁ _ _ _ _ (keeps_refl hkeep₁.1) hs₂).1.wellFormed
      have hmsub : m ≠ sub := by
        intro he'; obtain ⟨md, hmd⟩ := hm; rw [he', hfresh] at hmd; cases hmd
      have hnc : m ∉ childrenOf s₂.tree sub := by
        intro hmc
        have hp₂ := (mem_childrenOf_iff hwf₂ m sub).mpr hmc
        rw [e₂, hk₁.parentOf hm] at hp₂
        obtain ⟨sd, hsd⟩ := exists_data_of_parentOf hwf hp₂
        rw [hfresh] at hsd; cases hsd
      rw [parentOf_append_of_not_mem (failWith_ok.mp hr) hmsub hnc, e₂, hk₁.parentOf hm]

/--
first partially contained child の側の frame。child が `ca` の子で start node の inclusive ancestor なら、
動くのは child の clone（新しい node）と、再帰が動かす child の strict descendant だけである。
-/
theorem partialFirst_frame {cut : Bool} {recur : Recur} {s s' : DOMState} {r : RangeState}
    {fp : Option NodeId} {ca into : NodeId} (hrec : RecurFrame recur)
    (hrk : ∀ s₀, RecurClosed (Keeps s₀) recur) (h : AdmissibleDOMState s)
    (hstart : InTree s.tree r.start.node)
    (hfp : ∀ x, fp = some x → parentOf s.tree x = some ca ∧ InclusiveAncestor s.tree x r.start.node)
    (hr : partialFirst cut recur s r fp into = .ok s') :
    ∀ m, InTree s.tree m → (∀ x, fp = some x → ¬ Ancestor s.tree x m) →
      parentOf s'.tree m = parentOf s.tree m := by
  have hwf := h.wellFormed
  intro m hm hnm
  unfold partialFirst at hr
  split at hr
  · cases hr; rfl
  · next x =>
    obtain ⟨hxp, hxs⟩ := hfp x rfl
    split at hr
    · simp at hr
    · next fd hfd =>
      split at hr
      · exact (parentsKept_dataPart hr).parentOf hm
      · split at hr
        · simp at hr
        · next c s₁ ha =>
          have hk₁ := parentsKept_appendShallowClone (not_fragment_of_parent h hfd hxp) ha
          have hkeep₁ : Keeps s s₁ := closed_appendShallowClone (keeps_contentsClosed s)
            (keeps_refl h) hfd ha
          have hchain : ∀ y, InclusiveAncestor s.tree y r.start.node →
              parentOf s₁.tree y = parentOf s.tree y := fun y hy =>
            hk₁.parentOf (inTree_of_inclusiveAncestor hwf hstart hy)
          have hxs₁ : InclusiveAncestor s₁.tree x r.start.node :=
            inclusiveAncestor_of_chain_kept hchain hxs
          have hx₁ : InTree s₁.tree x := hkeep₁.inTree (exists_data_of_parentOf hwf hxp |>.elim
            fun _ _ => ⟨fd, hfd⟩)
          have hrm := subContents_frame (r := { start := r.start, «end» := ⟨x, lengthOf s₁.tree x⟩ })
            hrec hrk hkeep₁.1 (hkeep₁.inTree hstart) hx₁ hxs₁ hr m (hk₁.inTree hm)
            (fun ha₁ => hnm x rfl (ancestor_of_parents_kept hwf (fun _ hy => hk₁.parentOf hy) ha₁ hm))
          rw [hrm, hk₁.parentOf hm]

/--
**片側の range の frame。** end node が start node の inclusive ancestor なら、extract（clone the contents）が
parent を動かす木の node は、end node の strict descendant だけである。
-/
theorem contentsInto_frame_first (cut : Bool) :
    ∀ (fuel : Nat) {s s' : DOMState} {r : RangeState} {into : NodeId},
      AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node →
      InclusiveAncestor s.tree r.«end».node r.start.node →
      contentsInto cut fuel s r none into = .ok s' →
      ∀ m, InTree s.tree m → ¬ Ancestor s.tree r.«end».node m → parentOf s'.tree m = parentOf s.tree m
  | 0, s, s', r, into, _, _, _, _, hr => by simp [contentsInto] at hr
  | fuel + 1, s, s', r, into, h, hs, he, hab, hr => by
    have hwf := h.wellFormed
    have hrec : RecurFrame (fun s' r' c => contentsInto cut fuel s' r' none c) :=
      fun _ _ _ _ h' hs' he' hab' hc => contentsInto_frame_first cut fuel h' hs' he' hab' hc
    have hrk : ∀ s₀, RecurClosed (Keeps s₀) (fun s' r' c => contentsInto cut fuel s' r' none c) :=
      fun s₀ _ _ _ _ hk hc => closed_contentsInto (keeps_contentsClosed s₀) cut fuel hk hc
    intro m hm hnm
    unfold contentsInto at hr
    split at hr
    · cases hr; rfl
    · split at hr
      · simp at hr
      · split at hr
        · exact (parentsKept_dataPart hr).parentOf hm
        · split at hr
          · simp at hr
          · next ca hca =>
            have hcae : ca = r.«end».node :=
              commonAncestor_unique (commonAncestor_spec hwf hca) (commonAncestor_of_end_above hwf hab)
            subst hcae
            dsimp only at hr
            split at hr
            · simp at hr
            · split at hr
              · simp at hr
              · next s₁ hs₁ =>
                have hs₁e : s₁ = s := by unfold setSelf at hs₁; cases hs₁; rfl
                subst hs₁e
                split at hr
                · simp at hr
                · next s₂ hs₂ =>
                  have hfpx : ∀ x, firstPartiallyContainedChild s₁.tree r r.«end».node = some x →
                      parentOf s₁.tree x = some r.«end».node ∧
                        InclusiveAncestor s₁.tree x r.start.node := fun x hx => by
                    have hpc := firstPartial_spec (r := r) hwf r.«end».node
                    rw [hx] at hpc
                    obtain ⟨-, A, B, hl, hpc, -⟩ := hpc
                    have hxc : x ∈ childrenOf s₁.tree r.«end».node := by rw [hl]; simp
                    refine ⟨(mem_childrenOf_iff hwf x _).mpr hxc, ?_⟩
                    rcases hpc with ⟨hxs, -⟩ | ⟨-, hxe⟩
                    · exact hxs
                    · exfalso
                      have hxp := (mem_childrenOf_iff hwf x _).mpr hxc
                      rcases hxe with he' | he'
                      · rw [he'] at hxp; exact hwf.acyclic _ (.step hxp)
                      · exact hwf.acyclic _ (.trans hxp he')
                  have hp₂ := partialFirst_frame hrec hrk h hs hfpx hs₂
                  have hk₂ : Keeps s₁ s₂ :=
                    closed_partialFirst (keeps_contentsClosed s₁) (hrk s₁) (keeps_refl h) hs₂
                  split at hr
                  · simp at hr
                  · next s₃ hs₃ =>
                    have hcs : ∀ c ∈ containedChildren s₁.tree r r.«end».node,
                        ∃ cd, s₂.tree.get? c = some cd ∧ cd.kind ≠ .documentFragment := by
                      intro c hc
                      obtain ⟨cd, hcd, hk⟩ := child_not_fragment h ((List.mem_filter.mp hc).1)
                      obtain ⟨cd', hcd', he'⟩ := hk₂.2 c cd hcd
                      exact ⟨cd', hcd', by rw [he']; exact hk⟩
                    have hm₂ : InTree s₂.tree m := hk₂.inTree hm
                    have hp₃ : parentOf s₃.tree m = parentOf s₂.tree m := by
                      split at hs₃
                      · obtain ⟨md, hmd⟩ := hm₂
                        refine (appendEach_frame _ hcs hs₃ m md hmd).2 fun hmc => hnm ?_
                        exact .step ((mem_childrenOf_iff hwf m _).mpr ((List.mem_filter.mp hmc).1))
                      · exact (cloneEach_frame _ hk₂.1 hcs hs₃).parentOf hm₂
                    have hlp : lastPartiallyContainedChild s₁.tree r r.«end».node = none := by
                      unfold lastPartiallyContainedChild
                      rw [if_pos ((isInclusiveAncestorOf_iff hwf _ _).mpr hab)]
                    rw [hlp] at hr
                    unfold partialLast at hr
                    cases hr
                    rw [hp₃, hp₂ m hm fun x hx hax => hnm ((Ancestor.step (hfpx x hx).1).trans_ancestor hax)]

/-! ## 一番上の階：first は start 側、last は end 側の子 -/

section Order

variable {t : Tree} {r : RangeState}

/--
start node の側の子 `c` と end node の側の子 `d` が common ancestor の別の子なら、range の start が end より
後にないとき、`c` は `d` より前にある。
-/
theorem index_lt_of_boundaryLE (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hle : BoundaryLE t r.start r.«end») {ca c d : NodeId}
    (hc : parentOf t c = some ca) (hcs : InclusiveAncestor t c r.start.node)
    (hd : parentOf t d = some ca) (hde : InclusiveAncestor t d r.«end».node) (hne : c ≠ d) :
    (index t c).getD 0 < (index t d).getD 0 := by
  have hpos := hle.2
  rw [bpPosition_eq_lexCmp hwf hs he hle.1] at hpos
  obtain ⟨r1, hr1⟩ := pathIndices_split hwf hc hcs
  obtain ⟨r2, hr2⟩ := pathIndices_split hwf hd hde
  unfold bpKey at hpos
  rw [hr1, hr2] at hpos
  simp only [List.append_assoc, List.cons_append, lexCmp_append_left] at hpos
  rcases Nat.lt_trichotomy ((index t c).getD 0) ((index t d).getD 0) with h | h | h
  · exact h
  · exact absurd (eq_of_index_eq hwf hc hd h) hne
  · exact absurd (lexCmp_cons_gt h _ _) hpos

/-- children が `A ++ x :: B` に分かれ、`x` が `A` に無ければ、`x` の index は `A` の長さである。 -/
theorem index_of_split {x p : NodeId} {A B : List NodeId} (hx : parentOf t x = some p)
    (hl : childrenOf t p = A ++ x :: B) (hxA : x ∉ A) : index t x = some A.length :=
  (index_eq_some_iff_split hx).mpr ⟨A, B, hl, rfl, hxA⟩

/-- index が `A` の長さより小さい兄弟は `A` にある。 -/
theorem mem_of_index_lt {c x p : NodeId} {A B : List NodeId} (hc : parentOf t c = some p)
    (hl : childrenOf t p = A ++ x :: B) {j : Nat} (hj : index t c = some j) (hlt : j < A.length) :
    c ∈ A := by
  obtain ⟨u, v, hsplit, hlen, -⟩ := (index_eq_some_iff_split hc).mp hj
  have h1 : (childrenOf t p)[j]? = some c := by
    rw [hsplit, ← hlen]; simp
  rw [hl, List.getElem?_append_left hlt] at h1
  exact List.mem_of_getElem? h1

/-- index が `A` と `x` の長さより大きい兄弟は `B` にある。 -/
theorem mem_of_index_gt {c x p : NodeId} {A B : List NodeId} (hc : parentOf t c = some p)
    (hl : childrenOf t p = A ++ x :: B) {j : Nat} (hj : index t c = some j) (hgt : A.length < j) :
    c ∈ B := by
  obtain ⟨u, v, hsplit, hlen, -⟩ := (index_eq_some_iff_split hc).mp hj
  have h1 : (childrenOf t p)[j]? = some c := by
    rw [hsplit, ← hlen]; simp
  rw [hl, List.getElem?_append_right (by omega)] at h1
  obtain ⟨k, hk⟩ : ∃ k, j - A.length = k + 1 := ⟨j - A.length - 1, by omega⟩
  rw [hk, List.getElem?_cons_succ] at h1
  exact List.mem_of_getElem? h1

/-- 二つの端点のどちらも他方の inclusive ancestor でないとき、common ancestor は start node の strict ancestor。 -/
theorem ancestor_start_of_two_sided {ca : NodeId} (hca : CommonAncestor t r ca)
    (hns : ¬ InclusiveAncestor t r.start.node r.«end».node) : Ancestor t ca r.start.node := by
  rcases hca.1 with he | h
  · exact absurd (he ▸ hca.2.1) hns
  · exact h

theorem ancestor_end_of_two_sided {ca : NodeId} (hca : CommonAncestor t r ca)
    (hne : ¬ InclusiveAncestor t r.«end».node r.start.node) : Ancestor t ca r.«end».node := by
  rcases hca.2.1 with he | h
  · exact absurd (he ▸ hca.1) hne
  · exact h

/-- common ancestor の子で start node の inclusive ancestor なものは、end node の inclusive ancestor でない。 -/
theorem not_end_of_start_child {ca c : NodeId} (hca : CommonAncestor t r ca)
    (hc : parentOf t c = some ca) (hcs : InclusiveAncestor t c r.start.node) :
    ¬ InclusiveAncestor t c r.«end».node :=
  hca.2.2 c hcs (.step hc)

theorem not_start_of_end_child {ca c : NodeId} (hca : CommonAncestor t r ca)
    (hc : parentOf t c = some ca) (hce : InclusiveAncestor t c r.«end».node) :
    ¬ InclusiveAncestor t c r.start.node := fun hcs =>
  not_end_of_start_child hca hc hcs hce |>.elim

/--
**first partially contained child は start node の側の子である。** range の start が end より後になく、
どちらの端点も他方の inclusive ancestor でないとき。
-/
theorem firstPartial_toward_start (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hle : BoundaryLE t r.start r.«end») {ca x : NodeId} (hca : CommonAncestor t r ca)
    (hns : ¬ InclusiveAncestor t r.start.node r.«end».node)
    (hx : firstPartiallyContainedChild t r ca = some x) :
    parentOf t x = some ca ∧ InclusiveAncestor t x r.start.node := by
  have hfp := firstPartial_spec (r := r) hwf ca
  rw [hx] at hfp
  obtain ⟨-, A, B, hl, hpc, hA⟩ := hfp
  have hxp : parentOf t x = some ca := (mem_childrenOf_iff hwf x ca).mpr (by rw [hl]; simp)
  refine ⟨hxp, ?_⟩
  rcases hpc with ⟨hxs, -⟩ | ⟨hxs, hxe⟩
  · exact hxs
  exfalso
  obtain ⟨c, hcp, hcs⟩ := (ancestor_start_of_two_sided hca hns).exists_child
  have hcne : c ≠ x := fun h => hxs (h ▸ hcs)
  have hlt := index_lt_of_boundaryLE hwf hs he hle hcp hcs hxp hxe hcne
  have hxA : x ∉ A := fun h => hA x h (Or.inr ⟨hxs, hxe⟩)
  rw [index_of_split hxp hl hxA] at hlt
  obtain ⟨j, hj⟩ := index_isSome hwf hcp
  rw [hj] at hlt
  exact hA c (mem_of_index_lt hcp hl hj hlt) (Or.inl ⟨hcs, not_end_of_start_child hca hcp hcs⟩)

/-- **last partially contained child は end node の側の子である。** -/
theorem lastPartial_toward_end (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed)
    (hle : BoundaryLE t r.start r.«end») {ca x : NodeId} (hca : CommonAncestor t r ca)
    (hne : ¬ InclusiveAncestor t r.«end».node r.start.node)
    (hx : lastPartiallyContainedChild t r ca = some x) :
    parentOf t x = some ca ∧ InclusiveAncestor t x r.«end».node := by
  have hlp := lastPartial_spec (r := r) hwf ca
  rw [hx] at hlp
  obtain ⟨-, A, B, hl, hpc, hB⟩ := hlp
  have hxp : parentOf t x = some ca := (mem_childrenOf_iff hwf x ca).mpr (by rw [hl]; simp)
  refine ⟨hxp, ?_⟩
  rcases hpc with ⟨hxs, hxe⟩ | ⟨-, hxe⟩
  · exfalso
    obtain ⟨d, hdp, hde⟩ := (ancestor_end_of_two_sided hca hne).exists_child
    have hdne : x ≠ d := fun h => hxe (h ▸ hde)
    have hlt := index_lt_of_boundaryLE hwf hs he hle hxp hxs hdp hde hdne
    have hxA : x ∉ A := by
      intro hxA
      obtain ⟨pd, hpd⟩ := exists_data_of_parentOf hwf hxp
      have hnd : (childrenOf t ca).Nodup := by
        rw [childrenOf_eq hpd]; exact hwf.children_nodup ca pd hpd
      rw [hl, List.nodup_append] at hnd
      exact hnd.2.2 x hxA x (by simp) rfl
    rw [index_of_split hxp hl hxA] at hlt
    obtain ⟨j, hj⟩ := index_isSome hwf hdp
    rw [hj] at hlt
    exact hB d (mem_of_index_gt hdp hl hj hlt) (Or.inr ⟨not_start_of_end_child hca hdp hde, hde⟩)
  · exact hxe

end Order

/-! ## depth の差 -/

theorem depth_lt_of_ancestor {t : Tree} (hwf : WellFormed t) {a n : NodeId} (h : Ancestor t a n) :
    depth t a < depth t n := by
  induction h with
  | step hp => rw [depth_parent hwf hp]; omega
  | trans hp _ ih => rw [depth_parent hwf hp]; omega

theorem depth_le_of_inclusiveAncestor {t : Tree} (hwf : WellFormed t) {a n : NodeId}
    (h : InclusiveAncestor t a n) : depth t a ≤ depth t n := by
  rcases h with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (depth_lt_of_ancestor hwf h)

/--
`a` より下にある `n` の inclusive ancestor の parent が変わらなければ、`a` は新しい木でも `n` の ancestor で、
`n` と `a` の depth の差は変わらない。
-/
theorem depth_below_kept {t t' : Tree} (hwf : WellFormed t) (hwf' : WellFormed t') {a n : NodeId}
    (h : Ancestor t a n)
    (hk : ∀ y, InclusiveAncestor t y n → Ancestor t a y → parentOf t' y = parentOf t y) :
    Ancestor t' a n ∧ depth t' n + depth t a = depth t n + depth t' a := by
  induction h with
  | @step n hp =>
    have hp' : parentOf t' n = some a := by rw [hk n (Or.inl rfl) (.step hp)]; exact hp
    refine ⟨.step hp', ?_⟩
    rw [depth_parent hwf' hp', depth_parent hwf hp]
    omega
  | @trans b n hp hab ih =>
    have hp' : parentOf t' n = some b := by rw [hk n (Or.inl rfl) (.trans hp hab)]; exact hp
    obtain ⟨hab', hd⟩ := ih fun y hy hay => hk y (by
      rcases hy with rfl | hy
      · exact Or.inr (.step hp)
      · exact Or.inr (.trans hp hy)) hay
    refine ⟨.trans hp' hab', ?_⟩
    rw [depth_parent hwf' hp', depth_parent hwf hp]
    omega

/-! ## fuel が足りる条件 -/

/--
**fuel が足りる条件。** fuel は正で、common ancestor から両端点までの depth の差が fuel より小さい。

再帰した subrange では common ancestor が一段下りるので、差は一つずつ減る。
-/
def FuelEnough (t : Tree) (r : RangeState) (f : Nat) : Prop :=
  0 < f ∧ ∀ ca, CommonAncestor t r ca →
    depth t r.start.node - depth t ca < f ∧ depth t r.«end».node - depth t ca < f

/--
range の向き。片側の range か、start が end より後にない。

後ろ向きの range では first partially contained child が end 側の子になり、再帰が止まらない。
-/
def Ordered (t : Tree) (r : RangeState) : Prop :=
  InclusiveAncestor t r.«end».node r.start.node ∨ InclusiveAncestor t r.start.node r.«end».node ∨
    BoundaryLE t r.start r.«end»

/-- end node の子で partially contained なものは、start 側にある。 -/
theorem firstPartial_of_end_above {t : Tree} {r : RangeState} (hwf : WellFormed t) {x : NodeId}
    (hx : firstPartiallyContainedChild t r r.«end».node = some x) :
    parentOf t x = some r.«end».node ∧ InclusiveAncestor t x r.start.node := by
  have hpc := firstPartial_spec (r := r) hwf r.«end».node
  rw [hx] at hpc
  obtain ⟨-, A, B, hl, hpc, -⟩ := hpc
  have hxp : parentOf t x = some r.«end».node := (mem_childrenOf_iff hwf x _).mpr (by rw [hl]; simp)
  refine ⟨hxp, ?_⟩
  rcases hpc with ⟨hxs, -⟩ | ⟨-, hxe⟩
  · exact hxs
  · exfalso
    rcases hxe with he' | he'
    · rw [he'] at hxp; exact hwf.acyclic _ (.step hxp)
    · exact hwf.acyclic _ (.trans hxp he')

/-- start node の子で partially contained なものは、end 側にある。 -/
theorem lastPartial_of_start_above {t : Tree} {r : RangeState} (hwf : WellFormed t) {x : NodeId}
    (hx : lastPartiallyContainedChild t r r.start.node = some x) :
    parentOf t x = some r.start.node ∧ InclusiveAncestor t x r.«end».node := by
  have hpc := lastPartial_spec (r := r) hwf r.start.node
  rw [hx] at hpc
  obtain ⟨-, A, B, hl, hpc, -⟩ := hpc
  have hxp : parentOf t x = some r.start.node := (mem_childrenOf_iff hwf x _).mpr (by rw [hl]; simp)
  refine ⟨hxp, ?_⟩
  rcases hpc with ⟨hxs, -⟩ | ⟨-, hxe⟩
  · exfalso
    rcases hxs with he' | he'
    · rw [he'] at hxp; exact hwf.acyclic _ (.step hxp)
    · exact hwf.acyclic _ (.trans hxp he')
  · exact hxe

/-- first partially contained child は common ancestor の子で、start node の側にある。 -/
theorem firstPartial_side {t : Tree} {r : RangeState} (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed) (hord : Ordered t r)
    {ca x : NodeId} (hca : CommonAncestor t r ca) (hx : firstPartiallyContainedChild t r ca = some x) :
    parentOf t x = some ca ∧ InclusiveAncestor t x r.start.node := by
  by_cases hns : InclusiveAncestor t r.start.node r.«end».node
  · unfold firstPartiallyContainedChild at hx
    rw [if_pos ((isInclusiveAncestorOf_iff hwf _ _).mpr hns)] at hx
    cases hx
  by_cases hne : InclusiveAncestor t r.«end».node r.start.node
  · have := commonAncestor_unique hca (commonAncestor_of_end_above hwf hne)
    subst this
    exact firstPartial_of_end_above hwf hx
  rcases hord with h | h | h
  · exact absurd h hne
  · exact absurd h hns
  · exact firstPartial_toward_start hwf hs he h hca hns hx

/-- last partially contained child は common ancestor の子で、end node の側にある。 -/
theorem lastPartial_side {t : Tree} {r : RangeState} (hwf : WellFormed t) {sd ed : NodeData}
    (hs : t.get? r.start.node = some sd) (he : t.get? r.«end».node = some ed) (hord : Ordered t r)
    {ca x : NodeId} (hca : CommonAncestor t r ca) (hx : lastPartiallyContainedChild t r ca = some x) :
    parentOf t x = some ca ∧ InclusiveAncestor t x r.«end».node := by
  by_cases hne : InclusiveAncestor t r.«end».node r.start.node
  · unfold lastPartiallyContainedChild at hx
    rw [if_pos ((isInclusiveAncestorOf_iff hwf _ _).mpr hne)] at hx
    cases hx
  by_cases hns : InclusiveAncestor t r.start.node r.«end».node
  · have := commonAncestor_unique hca (commonAncestor_of_start_above hwf hns)
    subst this
    exact lastPartial_of_start_above hwf hx
  rcases hord with h | h | h
  · exact absurd h hne
  · exact absurd h hns
  · exact lastPartial_toward_end hwf hs he h hca hne hx

/-! ## 再帰の取り替え -/

/-- 再帰が同じ値を返せば、subfragment を経る部分も同じ値を返す。 -/
theorem subContents_congr {recur₁ recur₂ : Recur} {s : DOMState} {r : RangeState} {c : NodeId}
    (h : ∀ sub s₁, rangeFragment s r = .ok (sub, s₁) → recur₁ s₁ r sub = recur₂ s₁ r sub) :
    subContents recur₁ s r c = subContents recur₂ s r c := by
  unfold subContents
  cases hf : rangeFragment s r with
  | error e => rfl
  | ok v =>
    obtain ⟨sub, s₁⟩ := v
    simp only []
    rw [h sub s₁ hf]

/-- 再帰が同じ値を返せば、first partially contained child の扱いも同じ値を返す。 -/
theorem partialFirst_congr {cut : Bool} {recur₁ recur₂ : Recur} {s : DOMState} {r : RangeState}
    {fp : Option NodeId} {into : NodeId}
    (h : ∀ x fd c s₁, fp = some x → s.tree.get? x = some fd → fd.kind.isCharacterData = false →
      appendShallowClone s fd into = .ok (c, s₁) →
      subContents recur₁ s₁ { start := r.start, «end» := ⟨x, lengthOf s₁.tree x⟩ } c =
        subContents recur₂ s₁ { start := r.start, «end» := ⟨x, lengthOf s₁.tree x⟩ } c) :
    partialFirst cut recur₁ s r fp into = partialFirst cut recur₂ s r fp into := by
  unfold partialFirst
  cases fp with
  | none => rfl
  | some x =>
    simp only []
    cases hfd : s.tree.get? x with
    | none => rfl
    | some fd =>
      simp only []
      by_cases hcd : fd.kind.isCharacterData = true
      · rw [if_pos hcd, if_pos hcd]
      · rw [if_neg hcd, if_neg hcd]
        cases ha : appendShallowClone s fd into with
        | error p => rfl
        | ok cs =>
          obtain ⟨c, s₁⟩ := cs
          exact h x fd c s₁ rfl hfd (by simpa using hcd) ha

/-- 再帰が同じ値を返せば、last partially contained child の扱いも同じ値を返す。 -/
theorem partialLast_congr {cut : Bool} {recur₁ recur₂ : Recur} {s : DOMState} {r : RangeState}
    {lp : Option NodeId} {into : NodeId}
    (h : ∀ x ld c s₁, lp = some x → s.tree.get? x = some ld → ld.kind.isCharacterData = false →
      appendShallowClone s ld into = .ok (c, s₁) →
      subContents recur₁ s₁ { start := ⟨x, 0⟩, «end» := r.«end» } c =
        subContents recur₂ s₁ { start := ⟨x, 0⟩, «end» := r.«end» } c) :
    partialLast cut recur₁ s r lp into = partialLast cut recur₂ s r lp into := by
  unfold partialLast
  cases lp with
  | none => rfl
  | some x =>
    simp only []
    cases hld : s.tree.get? x with
    | none => rfl
    | some ld =>
      simp only []
      by_cases hcd : ld.kind.isCharacterData = true
      · rw [if_pos hcd, if_pos hcd]
      · rw [if_neg hcd, if_neg hcd]
        cases ha : appendShallowClone s ld into with
        | error p => rfl
        | ok cs =>
          obtain ⟨c, s₁⟩ := cs
          exact h x ld c s₁ rfl hld (by simpa using hcd) ha

/-! ## fuel は足りる -/

theorem ancestor_of_ancestor_inclusive {t : Tree} {a y n : NodeId} (hay : Ancestor t a y)
    (hy : InclusiveAncestor t y n) : Ancestor t a n := by
  rcases hy with rfl | hy
  · exact hay
  · exact hay.trans_ancestor hy

/--
**fuel が足りれば、それより多い fuel でも結果は同じである。**

range は片側か、start が end より後になく、両端は木にある。fuel は `FuelEnough` を満たす。
-/
theorem contentsInto_fuel (cut : Bool) :
    ∀ (f g : Nat) {s : DOMState} {r : RangeState} {self : Option Nat} {into : NodeId},
      AdmissibleDOMState s → InTree s.tree r.start.node → InTree s.tree r.«end».node →
      Ordered s.tree r → FuelEnough s.tree r f → f ≤ g →
      contentsInto cut g s r self into = contentsInto cut f s r self into
  | 0, _, _, _, _, _, _, _, _, _, hf, _ => absurd hf.1 (Nat.lt_irrefl 0)
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, hfg => absurd hfg (by omega)
  | f + 1, g + 1, s, r, self, into, h, hs, he, hord, hf, hfg => by
    have hwf := h.wellFormed
    have hfg' : f ≤ g := by omega
    obtain ⟨sd, hsd⟩ := hs
    obtain ⟨ed, hed⟩ := he
    have hrk : ∀ s₀, RecurClosed (Keeps s₀) (fun s' r' c => contentsInto cut f s' r' none c) :=
      fun s₀ _ _ _ _ hk hc => closed_contentsInto (keeps_contentsClosed s₀) cut f hk hc
    have hrec : RecurFrame (fun s' r' c => contentsInto cut f s' r' none c) :=
      fun _ _ _ _ h' hs' he' hab' hc => contentsInto_frame_first cut f h' hs' he' hab' hc
    unfold contentsInto
    -- step 2
    by_cases hcol : r.start = r.«end»
    · rw [if_pos (by simp [hcol]), if_pos (by simp [hcol])]
    rw [if_neg (by simpa using hcol), if_neg (by simpa using hcol), hsd]
    simp only []
    -- step 4
    by_cases hsingle : (r.start.node == r.«end».node && sd.kind.isCharacterData) = true
    · rw [if_pos hsingle, if_pos hsingle]
    rw [if_neg hsingle, if_neg hsingle]
    -- step 5
    cases hca : commonAncestor s.tree r with
    | none => rfl
    | some ca =>
    simp only []
    have hCA := commonAncestor_spec hwf hca
    have hdepth := hf.2 ca hCA
    -- step 11
    by_cases hdt : ((containedChildren s.tree r ca).any
        fun c => kindOf s.tree c == some .documentType) = true
    · rw [if_pos hdt, if_pos hdt]
    rw [if_neg hdt, if_neg hdt]
    -- step 12-15
    cases hss : setSelf s self (deleteContentsNewBP s.tree r) with
    | error p => rfl
    | ok s₁ =>
    simp only []
    have htree₁ : s₁.tree = s.tree := by
      rcases setSelf_spec hss with ⟨-, rfl⟩ | ⟨i, -, rfl⟩ <;> rfl
    have hk₁ : Keeps s s₁ := closed_setSelf (keeps_contentsClosed s) (keeps_refl h) hss
    have hfpx : ∀ x, firstPartiallyContainedChild s.tree r ca = some x →
        parentOf s₁.tree x = some ca ∧ InclusiveAncestor s₁.tree x r.start.node := by
      intro x hx; rw [htree₁]; exact firstPartial_side hwf hsd hed hord hCA hx
    -- step 16-17：再帰は start 側の片側の range
    have hpfe : partialFirst cut (fun s' r' c => contentsInto cut g s' r' none c) s₁ r
        (firstPartiallyContainedChild s.tree r ca) into =
        partialFirst cut (fun s' r' c => contentsInto cut f s' r' none c) s₁ r
          (firstPartiallyContainedChild s.tree r ca) into := by
      refine partialFirst_congr fun x fd c s₁' hx hfd _ ha => ?_
      refine subContents_congr fun sub s₂' hf => ?_
      obtain ⟨hxp, hxs⟩ := hfpx x hx
      rw [htree₁] at hxp hxs
      have hpk := (parentsKept_appendShallowClone
        (not_fragment_of_parent hk₁.1 hfd (by rw [htree₁]; exact hxp)) ha).trans (parentsKept_rangeFragment hf)
      have hk' : Keeps s₁ s₂' :=
        (closed_appendShallowClone (keeps_contentsClosed s₁) (keeps_refl hk₁.1) hfd ha).trans
          ((keeps_contentsClosed s₁').fragment (keeps_refl (closed_appendShallowClone
            (keeps_contentsClosed s₁) (keeps_refl hk₁.1) hfd ha).1) hf)
      have hwf' := hk'.1.wellFormed
      have hchain : ∀ y, InclusiveAncestor s.tree y r.start.node →
          parentOf s₂'.tree y = parentOf s.tree y := fun y hy => by
        rw [hpk.parentOf (by rw [htree₁]; exact inTree_of_inclusiveAncestor hwf ⟨sd, hsd⟩ hy), htree₁]
      have hxs' : InclusiveAncestor s₂'.tree x r.start.node := inclusiveAncestor_of_chain_kept hchain hxs
      have hdx := depth_parent hwf hxp
      have hdsx := depth_le_of_inclusiveAncestor hwf hxs
      have hdiff : depth s₂'.tree r.start.node - depth s₂'.tree x =
          depth s.tree r.start.node - depth s.tree x := by
        rcases hxs with he' | hanc
        · rw [he']; simp
        · obtain ⟨-, hdd⟩ := depth_below_kept hwf hwf' hanc fun y hy _ => hchain y hy
          omega
      refine contentsInto_fuel cut f g (r := { start := r.start, «end» := ⟨x, lengthOf s₁'.tree x⟩ })
        hk'.1 (hk'.inTree (by rw [htree₁]; exact ⟨sd, hsd⟩)) (hk'.inTree ⟨fd, hfd⟩) (Or.inl hxs')
        ⟨by omega, fun ca' hca' => ?_⟩ hfg'
      have := commonAncestor_unique hca'
        (commonAncestor_of_end_above (r := { start := r.start, «end» := ⟨x, lengthOf s₁'.tree x⟩ })
          hwf' hxs')
      rw [show ca' = x from this]
      show depth s₂'.tree r.start.node - depth s₂'.tree x < f ∧ depth s₂'.tree x - depth s₂'.tree x < f
      omega
    rw [hpfe]
    cases hpf : partialFirst cut (fun s' r' c => contentsInto cut f s' r' none c) s₁ r
        (firstPartiallyContainedChild s.tree r ca) into with
    | error p => rfl
    | ok s₂ =>
    simp only []
    have hk₂ : Keeps s₁ s₂ := closed_partialFirst (keeps_contentsClosed s₁) (hrk s₁) (keeps_refl hk₁.1) hpf
    have hp₂ := partialFirst_frame hrec hrk hk₁.1 (by rw [htree₁]; exact ⟨sd, hsd⟩) hfpx hpf
    -- step 18
    cases hcr : (if cut then appendEach s₂ into (containedChildren s.tree r ca)
        else cloneEach s₂ into (containedChildren s.tree r ca)) with
    | error p => rfl
    | ok s₃ =>
    simp only []
    have hcs : ∀ c ∈ containedChildren s.tree r ca,
        ∃ cd, s₂.tree.get? c = some cd ∧ cd.kind ≠ .documentFragment := by
      intro c hc
      obtain ⟨cd, hcd, hk⟩ := child_not_fragment h (List.mem_filter.mp hc).1
      obtain ⟨cd', hcd', he'⟩ := (hk₁.trans hk₂).2 c cd hcd
      exact ⟨cd', hcd', by rw [he']; exact hk⟩
    have hk₃ : Keeps s₂ s₃ := by
      split at hcr
      · exact closed_appendEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
      · exact closed_cloneEach (keeps_contentsClosed s₂) _ (keeps_refl hk₂.1) hcr
    -- step 19-20：再帰は end 側の片側の range で、first の側と contained children の後の状態で走る
    refine partialLast_congr fun x ld c s₄' hx hld _ ha => ?_
    refine subContents_congr fun sub s₄ hf => ?_
    obtain ⟨hxp, hxe⟩ := lastPartial_side hwf hsd hed hord hCA hx
    have hk₃' : Keeps s s₃ := (hk₁.trans hk₂).trans hk₃
    have hxnf : ld.kind ≠ .documentFragment := by
      obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hxp
      obtain ⟨ld', hld', hke⟩ := hk₃'.2 x xd hxd
      rw [hld] at hld'; cases hld'
      rw [hke]; exact not_fragment_of_parent h hxd hxp
    have hpk₄ := (parentsKept_appendShallowClone hxnf ha).trans (parentsKept_rangeFragment hf)
    have hk₄' : Keeps s₃ s₄' := closed_appendShallowClone (keeps_contentsClosed s₃) (keeps_refl hk₃.1) hld ha
    have hk₄ : Keeps s₃ s₄ := hk₄'.trans ((keeps_contentsClosed s₄').fragment (keeps_refl hk₄'.1) hf)
    have hwf₄ := hk₄.1.wellFormed
    -- x より下の end node の inclusive ancestor は、s から s₄ まで parent を変えない
    have hchain : ∀ y, InclusiveAncestor s.tree y r.«end».node → Ancestor s.tree x y →
        parentOf s₄.tree y = parentOf s.tree y := by
      intro y hy hxy
      have hyt : InTree s.tree y := inTree_of_inclusiveAncestor hwf ⟨ed, hed⟩ hy
      have hyt₁ : InTree s₁.tree y := by rw [htree₁]; exact hyt
      have e₂ : parentOf s₂.tree y = parentOf s₁.tree y := by
        refine hp₂ y hyt₁ fun x' hx' hx'y => ?_
        obtain ⟨hx'p, hx's⟩ := hfpx x' hx'
        rw [htree₁] at hx'p hx's hx'y
        exact not_end_of_start_child hCA hx'p hx's (Or.inr (ancestor_of_ancestor_inclusive hx'y hy))
      have e₃ : parentOf s₃.tree y = parentOf s₂.tree y := by
        obtain ⟨yd, hyd⟩ := hk₂.inTree hyt₁
        split at hcr
        · refine (appendEach_frame _ hcs hcr y yd hyd).2 fun hyc => ?_
          have hyp : parentOf s.tree y = some ca :=
            (mem_childrenOf_iff hwf y ca).mpr (List.mem_filter.mp hyc).1
          refine sibling_subtrees_disjoint hwf hxp hyp ?_ (Or.inr hxy) (Or.inl rfl)
          intro hxy'; subst hxy'; exact hwf.acyclic _ hxy
        · exact (cloneEach_frame _ hk₂.1 hcs hcr).parentOf ⟨yd, hyd⟩
      rw [hpk₄.parentOf (hk₃'.inTree hyt), e₃, e₂, htree₁]
    have hxe₄ : InclusiveAncestor s₄.tree x r.«end».node := by
      rcases hxe with he' | hanc
      · exact Or.inl he'
      · exact Or.inr (depth_below_kept hwf hwf₄ hanc hchain).1
    have hdx := depth_parent hwf hxp
    have hdex := depth_le_of_inclusiveAncestor hwf hxe
    have hdiff : depth s₄.tree r.«end».node - depth s₄.tree x =
        depth s.tree r.«end».node - depth s.tree x := by
      rcases hxe with he' | hanc
      · rw [he']; simp
      · obtain ⟨-, hdd⟩ := depth_below_kept hwf hwf₄ hanc hchain
        omega
    refine contentsInto_fuel cut f g (r := { start := ⟨x, 0⟩, «end» := r.«end» })
      hk₄.1 (hk₄.inTree (hk₃'.inTree (exists_data_of_parentOf hwf hxp |>.elim fun _ _ => by
        obtain ⟨xd, hxd, -⟩ := parentOf_eq_some hxp; exact ⟨xd, hxd⟩)))
      (hk₄.inTree (hk₃'.inTree ⟨ed, hed⟩)) (Or.inr (Or.inl hxe₄))
      ⟨by omega, fun ca' hca' => ?_⟩ hfg'
    have := commonAncestor_unique hca'
      (commonAncestor_of_start_above (r := { start := ⟨x, 0⟩, «end» := r.«end» }) hwf₄ hxe₄)
    rw [show ca' = x from this]
    show depth s₄.tree x - depth s₄.tree x < f ∧ depth s₄.tree r.«end».node - depth s₄.tree x < f
    omega

/-- **`Tree.size + 1` の fuel は足りる。** 両端が木にあり、range が片側か、start が end より後にないとき。 -/
theorem contentsInto_size_fuel (cut : Bool) {s : DOMState} {r : RangeState} {self : Option Nat}
    {into : NodeId} (h : AdmissibleDOMState s) (hs : InTree s.tree r.start.node)
    (he : InTree s.tree r.«end».node) (hord : Ordered s.tree r) {g : Nat} (hg : s.tree.size + 1 ≤ g) :
    contentsInto cut g s r self into = contentsInto cut (s.tree.size + 1) s r self into := by
  refine contentsInto_fuel cut _ g h hs he hord ⟨by omega, fun ca _ => ?_⟩ hg
  obtain ⟨sd, hsd⟩ := hs
  obtain ⟨ed, hed⟩ := he
  have := depth_lt_size h.wellFormed hsd
  have := depth_lt_size h.wellFormed hed
  omega

/-! ## node を足しても boundary point の順は変わらない -/

section Extend

variable {t t' : Tree}

/-- `t'` は `t` に node を足しただけである。`t` にあった node の data は変わらない。 -/
def Extends (t t' : Tree) : Prop := ∀ m d, t.get? m = some d → t'.get? m = some d

theorem Extends.parentOf (hx : Extends t t') {m : NodeId} (hm : InTree t m) :
    Dom.parentOf t' m = Dom.parentOf t m := by
  obtain ⟨md, hmd⟩ := hm
  exact parentOf_congr ((hx m md hmd).trans hmd.symm)

theorem Extends.childrenOf (hx : Extends t t') {m : NodeId} (hm : InTree t m) :
    Dom.childrenOf t' m = Dom.childrenOf t m := by
  obtain ⟨md, hmd⟩ := hm
  rw [childrenOf_eq (hx m md hmd), childrenOf_eq hmd]

variable (hwf : WellFormed t) (hwf' : WellFormed t') (hx : Extends t t')
include hwf hwf' hx

omit hwf' in
theorem Extends.ancestorChain : ∀ (f : Nat) {n : NodeId}, InTree t n →
    Dom.ancestorChain t' f n = Dom.ancestorChain t f n
  | 0, _, _ => rfl
  | f + 1, n, hn => by
    simp only [Dom.ancestorChain]
    rw [Extends.parentOf hx hn]
    cases hp : Dom.parentOf t n with
    | none => rfl
    | some p =>
      simp only []
      rw [Extends.ancestorChain f (exists_data_of_parentOf hwf hp)]

theorem Extends.ancestors {n : NodeId} (hn : InTree t n) : Dom.ancestors t' n = Dom.ancestors t n := by
  obtain ⟨nd, hnd⟩ := hn
  have hnd' := hx n nd hnd
  unfold Dom.ancestors
  have e : Dom.ancestorChain t' (max t.size t'.size) n = Dom.ancestorChain t' t'.size n :=
    ancestorChain_eq_of_length_lt (ancestorChain_length_lt_size hwf' hnd' t'.size) _ (Nat.le_max_right _ _)
  have e' : Dom.ancestorChain t (max t.size t'.size) n = Dom.ancestorChain t t.size n :=
    ancestorChain_eq_of_length_lt (ancestorChain_length_lt_size hwf hnd t.size) _ (Nat.le_max_left _ _)
  rw [← e, ← e', Extends.ancestorChain hwf hx _ ⟨nd, hnd⟩]

omit hwf' in
theorem Extends.index {m : NodeId} (hm : InTree t m) : Dom.index t' m = Dom.index t m := by
  unfold Dom.index
  rw [Extends.parentOf hx hm]
  cases hp : Dom.parentOf t m with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    rw [Extends.childrenOf hx (exists_data_of_parentOf hwf hp)]

theorem Extends.pathIndices {n : NodeId} (hn : InTree t n) :
    Dom.pathIndices t' n = Dom.pathIndices t n := by
  unfold Dom.pathIndices Dom.pathNodes
  rw [Extends.ancestors hwf hwf' hx hn]
  refine List.map_congr_left fun y hy => ?_
  have hy' : y ∈ n :: Dom.ancestors t n := List.mem_reverse.mp (List.mem_of_mem_drop hy)
  rw [Extends.index hwf hx
    (inTree_of_inclusiveAncestor hwf hn ((mem_inclusiveAncestors_iff hwf n y).mp hy'))]

theorem Extends.root {n : NodeId} (hn : InTree t n) : Dom.root t' n = Dom.root t n := by
  refine root_unique hwf' ?_ ?_
  · have hk : ∀ y, InclusiveAncestor t y n → Dom.parentOf t' y = Dom.parentOf t y :=
      fun y hy => Extends.parentOf hx (inTree_of_inclusiveAncestor hwf hn hy)
    exact inclusiveAncestor_of_chain_kept hk (root_inclusive_ancestor t n)
  · rw [Extends.parentOf hx
      (inTree_of_inclusiveAncestor hwf hn (root_inclusive_ancestor t n))]
    exact root_parent_eq_none hwf n

/-- 両端が木にあれば、node を足しても boundary point の順は変わらない。 -/
theorem Extends.boundaryLE {a b : BoundaryPoint} (ha : InTree t a.node) (hb : InTree t b.node)
    (h : BoundaryLE t a b) : BoundaryLE t' a b := by
  obtain ⟨ad, had⟩ := ha
  obtain ⟨bd, hbd⟩ := hb
  have hroot : Dom.root t' a.node = Dom.root t' b.node := by
    rw [Extends.root hwf hwf' hx ⟨ad, had⟩, Extends.root hwf hwf' hx ⟨bd, hbd⟩]; exact h.1
  refine ⟨hroot, ?_⟩
  rw [bpPosition_eq_lexCmp hwf' (hx _ _ had) (hx _ _ hbd) hroot]
  have hpos := h.2
  rw [bpPosition_eq_lexCmp hwf had hbd h.1] at hpos
  unfold bpKey at hpos ⊢
  rw [Extends.pathIndices hwf hwf' hx ⟨ad, had⟩, Extends.pathIndices hwf hwf' hx ⟨bd, hbd⟩]
  exact hpos

end Extend

/-- step 1 の fragment を作っても、木にあった node はそのまま残る。 -/
theorem extends_rangeFragment {s s₁ : DOMState} {r : RangeState} {frag : NodeId}
    (h : rangeFragment s r = .ok (frag, s₁)) : Extends s.tree s₁.tree := by
  unfold rangeFragment at h
  split at h
  · simp at h
  · unfold createDocumentFragment at h
    split at h
    · simp at h
    · cases h
      intro m md hmd
      exact withFresh_get?_of_some hmd _

/--
**`extractContents()` と `cloneContents()` に渡す fuel は足りる。** live range が妥当なら
（両端が木にあり、start が end より後にない）、`contentsInto` に渡す `Tree.size + 1` から先は、fuel を
いくら足しても結果が変わらない。
-/
theorem rangeFragment_fuel (cut : Bool) {s s₁ : DOMState} {r : RangeState} {self : Option Nat}
    {frag : NodeId} (h : AdmissibleDOMState s) (hrv : RangeValid s.tree r)
    (hf : rangeFragment s r = .ok (frag, s₁)) {g : Nat} (hg : s₁.tree.size + 1 ≤ g) :
    contentsInto cut g s₁ r self frag = contentsInto cut (s₁.tree.size + 1) s₁ r self frag := by
  have h₁ : AdmissibleDOMState s₁ := admissible_rangeClosed.fragment h hf
  have hx := extends_rangeFragment hf
  obtain ⟨⟨sd, hsd, -⟩, ⟨ed, hed, -⟩, hle⟩ := hrv
  refine contentsInto_size_fuel cut h₁ ⟨sd, hx _ _ hsd⟩ ⟨ed, hx _ _ hed⟩
    (Or.inr (Or.inr (Extends.boundaryLE h.wellFormed h₁.wellFormed hx ⟨sd, hsd⟩ ⟨ed, hed⟩ hle))) hg

end Dom.Spec
