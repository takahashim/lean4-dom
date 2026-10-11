import Dom.Validity.Iterators

/-!
# observer registration の妥当性の保存

`docs/status.md` の「admissibility」のうち、
`AdmissibleDOMState.observerRegistrations` の成分。

registration が増えるのは `remove` の step 20（transient registered observer）だけである。
足される registration は既存の registration の observer index を受け継ぎ、
指す node は外した node そのものなので、どちらの条件も保たれる。

木から node が消えることは無い（`detach` も `insertAt` も store から entry を消さない）ので、
「registration が指す node が木の中にある」は kind の保存から出る。
-/

namespace Dom

/-- `ObserverRegistrationsValid` を保つこと。合成できるように関係として書く。 -/
def PreservesRegs (s s' : DOMState) : Prop :=
  ObserverRegistrationsValid s → ObserverRegistrationsValid s'

theorem PreservesRegs.refl (s : DOMState) : PreservesRegs s s := id

theorem PreservesRegs.trans {s₁ s₂ s₃ : DOMState}
    (h₁ : PreservesRegs s₁ s₂) (h₂ : PreservesRegs s₂ s₃) : PreservesRegs s₁ s₃ :=
  fun h => h₂ (h₁ h)

/-- observer の node list が伸びるだけであること。 -/
def NodeListsGrow (obs obs' : List ObserverState) : Prop :=
  ∀ (i : Nat) (o : ObserverState), obs[i]? = some o →
    ∃ o' : ObserverState, obs'[i]? = some o' ∧ ∀ x ∈ o.nodeList, x ∈ o'.nodeList

/-- observer の node list が伸びるだけなら、node list に載っていることは保たれる。 -/
theorem ListedIn.mono {s s' : DOMState} {r : Registration} (h : ListedIn s r)
    (hg : NodeListsGrow s.observers s'.observers) : ListedIn s' r := by
  obtain ⟨o, ho, hm⟩ := h
  obtain ⟨o', ho', hs⟩ := hg _ o ho
  exact ⟨o', ho', hs _ hm⟩

/-- node list の列が同じなら、node list は伸びている。 -/
theorem grow_of_nodeLists {obs obs' : List ObserverState}
    (h : obs'.map (·.nodeList) = obs.map (·.nodeList)) : NodeListsGrow obs obs' := by
  intro i o ho
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, ho, Option.map_some] at this
  cases ho' : obs'[i]? with
  | none => rw [ho'] at this; cases this
  | some o' =>
    rw [ho'] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨o', rfl, fun x hx => this ▸ hx⟩

/-- registration も observer の node list も変わらず、node も消えないなら保たれる。 -/
theorem preservesRegs_congr {s s' : DOMState} (hkp : ShapePreserving s.tree s'.tree)
    (hreg : s'.registrations = s.registrations)
    (hobs : s'.observers.map (·.nodeList) = s.observers.map (·.nodeList)) : PreservesRegs s s' := by
  intro h r hr
  rw [hreg] at hr
  obtain ⟨h1, h2, h3⟩ := h r hr
  have hlen : s'.observers.length = s.observers.length := by
    have := congrArg List.length hobs; simpa using this
  refine ⟨by rw [hlen]; exact h1, ?_, h3.mono (grow_of_nodeLists hobs)⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h2
  have hk := hkp r.node
  rw [hd] at hk
  cases hd' : s'.tree.get? r.node with
  | none => rw [hd'] at hk; simp at hk
  | some _ => simp

theorem preservesRegs_detach {s : DOMState} {t' : Tree} {n : NodeId}
    (hd : detach s.tree n = .ok t') : PreservesRegs s (s.withTree t') :=
  preservesRegs_congr (shapePreserving_detach hd) rfl rfl

theorem preservesRegs_insertAt {s : DOMState} {t' : Tree} {parent node : NodeId}
    {child : Option NodeId} (hi : insertAt s.tree parent node child = .ok t') :
    PreservesRegs s (s.withTree t') :=
  preservesRegs_congr (shapePreserving_insertAt hi) rfl rfl

/-! ## remove -/

/-- `remove` は transient registration を足すが、どちらの条件も保つ。 -/
theorem preservesRegs_remove {s s' : DOMState} {n : NodeId} {b : Bool}
    (hr : remove s n b = .ok s') : PreservesRegs s s' := by
  intro h
  obtain ⟨p, s₁, hp, hd, hrec⟩ := remove_cases hr
  -- detach までは registration も observer 列も変わらない
  have hkp : ShapePreserving s.tree s₁.tree :=
    shapePreserving_detach (detachWithLiveAdjust_tree hd)
  obtain ⟨_, _, hs₁⟩ := detachWithLiveAdjust_cases hd
  have hreg₁ : s₁.registrations = s.registrations := by rw [hs₁]; simp
  have hobs₁ : s₁.observers.map (·.nodeList) = s.observers.map (·.nodeList) := by rw [hs₁]; simp
  have h₁ : ObserverRegistrationsValid s₁ := preservesRegs_congr hkp hreg₁ hobs₁ h
  -- transient registration を足す
  have hnode : (s₁.tree.get? n).isSome := by
    obtain ⟨nd, hnd⟩ : ∃ nd, s.tree.get? n = some nd := by
      cases hq : s.tree.get? n with
      | none => rw [parentOf_eq, hq] at hp; simp at hp
      | some q => exact ⟨q, rfl⟩
    have hk := hkp n
    rw [hnd] at hk
    cases hq : s₁.tree.get? n with
    | none => rw [hq] at hk; simp at hk
    | some _ => simp
  have hgrow : NodeListsGrow s₁.observers (addTransientObservers s₁ n p).observers := by
    intro i o ho
    rw [addTransientObservers_observers]
    exact foldl_transientStep_grow n _ _ ho
  have h₂ : ObserverRegistrationsValid (addTransientObservers s₁ n p) := by
    intro r hr'
    have hobs : r.observer < s₁.observers.length :=
      addTransientObservers_observer_lt s₁ n p hr' (fun r' hr'' => (h₁ r' hr'').1)
    refine ⟨by simpa using hobs, ?_⟩
    have hr'' := hr'
    unfold addTransientObservers at hr''
    simp only [List.mem_append] at hr''
    rcases hr'' with hx | hx
    · obtain ⟨-, g2, g3⟩ := h₁ r hx
      exact ⟨by simpa using g2, g3.mono hgrow⟩
    · refine ⟨?_, ?_⟩
      · obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hx
        obtain ⟨r₀, _, hr₀⟩ := List.mem_map.mp hy
        rw [← hr₀]
        simpa using hnode
      · have hn : r.node = n := by
          obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hx
          obtain ⟨r₀, _, hr₀⟩ := List.mem_map.mp hy
          rw [← hr₀]
        have := foldl_transientStep_listed n _ s₁.observers r hx hobs
        rw [← addTransientObservers_observers] at this
        obtain ⟨o', ho', hm⟩ := this
        exact ⟨o', ho', by rw [hn]; exact hm⟩
  rcases hrec with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact h₂
  · exact preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp) h₂

theorem preservesRegs_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool},
      removeEach s ns b = .ok s' → PreservesRegs s s'
  | [], _, _, _, hr => by rw [← Except.ok.inj hr]; exact PreservesRegs.refl _
  | n :: ns, s, s', b, hr => by
    simp only [removeEach] at hr
    split at hr
    · simp at hr
    · next s₁ h₁ =>
      exact (preservesRegs_remove h₁).trans (preservesRegs_removeEach ns hr)

theorem preservesRegs_adopt {s s' : DOMState} {node doc : NodeId}
    (ha : adopt s node doc = .ok s') : PreservesRegs s s' := by
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases ha
  have h₁ : PreservesRegs s s₁ := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · exact PreservesRegs.refl _
    · exact preservesRegs_remove hr
  rcases hfinal with rfl | rfl
  · exact h₁
  · exact h₁.trans (preservesRegs_congr (shapePreserving_setOwnerDocument _ _ _) rfl rfl)

theorem preservesRegs_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId}, insertEach s parent child doc ns = .ok s' → PreservesRegs s s'
  | [], _, _, _, _, _, hi => by rw [insertEach] at hi; rw [← Except.ok.inj hi]; exact id
  | n :: ns, s, s', parent, child, doc, hi => by
    rw [insertEach] at hi
    split at hi
    · simp at hi
    · next s₁ ha =>
      split at hi
      · simp at hi
      · next s₂ hins =>
        refine ((preservesRegs_adopt ha).trans ?_).trans (preservesRegs_insertEach ns hi)
        have hs₂ := (DOMState.mapTree_eq_ok hins).2
        rw [hs₂]
        exact preservesRegs_insertAt (DOMState.mapTree_eq_ok hins).1

theorem preservesRegs_insertNodesAt {s s' : DOMState} {parent : NodeId}
    {child : Option NodeId} {nodes : List NodeId} {b : Bool}
    (hi : insertNodesAt s parent child nodes b = .ok s') : PreservesRegs s s' := by
  obtain ⟨sx, hx, hrec⟩ := insertNodesAt_cases hi
  have hstep : PreservesRegs s sx := by
    obtain ⟨_, _, hx⟩ := insertEachAt_cases hx
    refine PreservesRegs.trans ?_ (preservesRegs_insertEach nodes hx)
    exact preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp)
  rcases hrec with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact hstep
  · exact hstep.trans
      (preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp))

theorem preservesRegs_insert {s s' : DOMState} {node parent : NodeId}
    {child : Option NodeId} {b : Bool} (hi : insert s node parent child b = .ok s') :
    PreservesRegs s s' := by
  obtain ⟨_, _, hcase⟩ := insert_cases hi
  rcases hcase with ⟨_, _, hs⟩ | ⟨_, _, _, hre, hins⟩ | ⟨_, hins⟩
  · rw [hs]; exact PreservesRegs.refl _
  · refine (preservesRegs_removeEach _ hre).trans (PreservesRegs.trans ?_
      (preservesRegs_insertNodesAt hins))
    exact preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp)
  · exact preservesRegs_insertNodesAt hins

theorem preservesRegs_move {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hm : move s node newParent child = .ok s') :
    PreservesRegs s s' := by
  unfold move at hm
  split at hm
  · simp at hm
  · split at hm
    · simp at hm
    · next p hp =>
      split at hm
      · simp at hm
      · next sd hd =>
        have h₁ : PreservesRegs s sd := by
          obtain ⟨t', hdt, hs⟩ := detachWithLiveAdjust_cases hd
          subst hs
          exact preservesRegs_congr (by simpa using shapePreserving_detach hdt)
            (by simp) (by simp)
        simp only at hm
        split at hm
        · simp at hm
        · next s₂ hi =>
          have h₂ : PreservesRegs sd s₂ := by
            rw [(DOMState.mapTree_eq_ok hi).2]
            exact preservesRegs_congr
              (shapePreserving_insertAt (by simpa using (DOMState.mapTree_eq_ok hi).1))
              (by simp) (by simp)
          rw [← Except.ok.inj hm]
          -- step 23-24 の二つの record は木も registration も observer 列も変えない
          refine (h₁.trans h₂).trans (preservesRegs_congr ?_ ?_ ?_)
          · refine shapePreserving_of_tree_eq ?_
            simp only [queueTreeMutationRecord_tree]
            split <;> simp
          · simp only [queueTreeMutationRecord_registrations]
            split <;> simp
          · simp only [queueTreeMutationRecord_nodeLists]
            split <;> simp

theorem preservesRegs_replace {s s' : DOMState} {child node parent : NodeId}
    (hr : replace s child node parent = .ok s') : PreservesRegs s s' := by
  obtain ⟨_, s₁, s₂, s₃, _, _, ha, hrm, hi, hs⟩ := replace_cases hr
  have h₂ : PreservesRegs s₁ s₂ := by
    rcases hrm with ⟨_, rfl⟩ | ⟨_, hrm⟩
    · exact PreservesRegs.refl _
    · exact preservesRegs_remove hrm
  rw [hs]
  refine (((preservesRegs_adopt ha).trans h₂).trans (preservesRegs_insert hi)).trans ?_
  exact preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp)

theorem preservesRegs_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (hr : replaceAll s node parent = .ok s') : PreservesRegs s s' := by
  obtain ⟨s₁, s₂, hre, hstep, hs⟩ := replaceAll_cases hr
  have h₂ : PreservesRegs s₁ s₂ := by
    rcases hstep with ⟨-, rfl⟩ | ⟨_, -, hins⟩
    · exact PreservesRegs.refl _
    · exact preservesRegs_insert hins
  rw [hs]
  refine ((preservesRegs_removeEach _ hre).trans h₂).trans ?_
  exact preservesRegs_congr (shapePreserving_of_tree_eq (by simp)) (by simp) (by simp)

end Dom
