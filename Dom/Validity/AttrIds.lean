import Dom.Properties.Algorithms
import Dom.Properties.CharacterData
import Dom.Mutation.Api
import Dom.Mutation.Import

/-!
# attribute の id は一意である

model は `Attr` の同一性を `AttrId` で表す（`Dom/Basic/NodeId.lean`）。
それが同一性の表現として働くには、**同じ id の `Attr` が二つ無い**ことが要る。
ここでは「木のどの element の attribute list と、detach された `Attr` の list を合わせて、
id が重複しない」を `AttrIdsUnique` として置き、全操作が保つことを示す。

木の構造を変える操作は attribute list に触れない（`ShapePreserving`）し、
detach された `Attr` の list にも触れない。この二つを合わせて `AttrFrame` と呼び、
primitive から順に積み上げる。attribute を作る・動かす操作は個別に示す。
-/

namespace Dom

/-! ## 定義 -/

/-- node `m` の attribute の id と namespace の組の列（node が無ければ空）。 -/
def attrSigAt (t : Tree) (m : NodeId) : List (AttrId × Option String) :=
  match t.get? m with
  | some d => d.attributes.map fun a => (a.id, a.namespace)
  | none => []

/-- node `m` の attribute の id の列（node が無ければ空）。 -/
def attrIdsAt (t : Tree) (m : NodeId) : List AttrId := (attrSigAt t m).map Prod.fst

/-- detach された `Attr` の id・namespace・prefix。 -/
def detachedSig (a : Attr) : AttrId × Option String × Option String := (a.id, a.namespace, a.prefix)

/--
`Attr` が model の正規形にあること：namespace は空文字列でなく、prefix があれば namespace もある。
仕様の algorithm が作る `Attr` はどれもこの形である（`Attr.normalized` を参照）。
-/
def AttrNormalForm (p : Option String × Option String) : Prop :=
  normalizeNamespace p.1 = p.1 ∧ (p.2.isSome → p.1.isSome)

/-- **attribute の id は一意である。** -/
structure AttrIdsUnique (s : DOMState) : Prop where
  /-- 一つの element の中で重複しない。 -/
  within : ∀ m, (attrIdsAt s.tree m).Nodup
  /-- 別の element どうしで重複しない。 -/
  across : ∀ m m', m ≠ m' → ∀ i ∈ attrIdsAt s.tree m, i ∉ attrIdsAt s.tree m'
  /-- detach された `Attr` の中で重複しない。 -/
  detached : (s.detachedAttrs.map (·.id)).Nodup
  /-- element に付いたものと detach されたもので重複しない。 -/
  attachedDetached : ∀ m, ∀ i ∈ attrIdsAt s.tree m, i ∉ s.detachedAttrs.map (·.id)
  /--
  element に付いた attribute の namespace は正規化されている（空文字列でない）。
  `setAttributeNode` は渡された `Attr` を正規化した鍵で引き直すので、これが無いと
  同じ element の別の attribute を引いてしまう。
  -/
  normalized : ∀ m, ∀ p ∈ attrSigAt s.tree m, normalizeNamespace p.2 = p.2
  /--
  detach された `Attr` は正規形にある。`setAttributeNode` が正規化してから付けても
  同じ `Attr` のままであるために要る。
  -/
  detachedNormal : ∀ p ∈ s.detachedAttrs.map detachedSig, AttrNormalForm p.2

/-- attribute の id の配置が変わらないこと。 -/
structure AttrFrame (s s' : DOMState) : Prop where
  ids : ∀ m, attrSigAt s'.tree m = attrSigAt s.tree m
  detached : s'.detachedAttrs.map detachedSig = s.detachedAttrs.map detachedSig

theorem map_id_eq_detachedSig (l : List Attr) :
    l.map (·.id) = (l.map detachedSig).map Prod.fst := by
  rw [List.map_map]; rfl

namespace AttrFrame

theorem detachedIds {s s' : DOMState} (h : AttrFrame s s') :
    s'.detachedAttrs.map (·.id) = s.detachedAttrs.map (·.id) := by
  rw [map_id_eq_detachedSig, h.detached, ← map_id_eq_detachedSig]

theorem refl (s : DOMState) : AttrFrame s s := ⟨fun _ => rfl, rfl⟩

theorem trans {s s₁ s₂ : DOMState} (h₁ : AttrFrame s s₁) (h₂ : AttrFrame s₁ s₂) : AttrFrame s s₂ :=
  ⟨fun m => (h₂.ids m).trans (h₁.ids m), h₂.detached.trans h₁.detached⟩

theorem idsAt {s s' : DOMState} (h : AttrFrame s s') (m : NodeId) :
    attrIdsAt s'.tree m = attrIdsAt s.tree m := by
  unfold attrIdsAt; rw [h.ids]

theorem unique {s s' : DOMState} (h : AttrFrame s s') (hu : AttrIdsUnique s) : AttrIdsUnique s' :=
  ⟨fun m => by rw [h.idsAt]; exact hu.within m,
    fun m m' hne i hi => by rw [h.idsAt] at hi ⊢; exact hu.across m m' hne i hi,
    by rw [h.detachedIds]; exact hu.detached,
    fun m i hi => by rw [h.idsAt] at hi; rw [h.detachedIds]; exact hu.attachedDetached m i hi,
    fun m p hp => by rw [h.ids] at hp; exact hu.normalized m p hp,
    fun p hp => by rw [h.detached] at hp; exact hu.detachedNormal p hp⟩

end AttrFrame

theorem attrSigAt_of_shape {t t' : Tree} (h : ShapePreserving t t') (m : NodeId) :
    attrSigAt t' m = attrSigAt t m := by
  have ha := h.attributes m
  unfold attrSigAt
  have hid : ∀ l : List Attr, l.map (fun a => (a.id, a.namespace)) =
      (l.map Attr.dropDoc).map (fun a => (a.id, a.namespace)) := by
    intro l; rw [List.map_map]; rfl
  cases h' : t'.get? m <;> cases h₀ : t.get? m <;> rw [h', h₀] at ha <;> simp at ha
  all_goals first
    | rfl
    | (show List.map _ _ = List.map _ _; rw [hid, ha, ← hid])

/-- 木が `ShapePreserving` に変わり、detach された list が変わらなければ枠は保たれる。 -/
theorem AttrFrame.of_shape {s s' : DOMState} (h : ShapePreserving s.tree s'.tree)
    (hd : s'.detachedAttrs = s.detachedAttrs) : AttrFrame s s' :=
  ⟨attrSigAt_of_shape h, by rw [hd]⟩

/-- 木が変わらず、detach された list も変わらなければ枠は保たれる。 -/
theorem AttrFrame.of_eq {s s' : DOMState} (ht : s'.tree = s.tree)
    (hd : s'.detachedAttrs = s.detachedAttrs) : AttrFrame s s' :=
  ⟨fun m => by rw [ht], by rw [hd]⟩

/-! ## 実行時の検査 -/

/--
`AttrIdsUnique` の実行時の検査。木の node は store の鍵を順に見る
（木にある node は必ず鍵に現れる）。
-/
def checkAttrIdsUnique (s : DOMState) : Bool :=
  let ks := s.tree.nodes.keys
  let det := s.detachedAttrs.map (·.id)
  ks.all (fun k => ListUtil.nodupB (attrIdsAt s.tree k) &&
      (attrIdsAt s.tree k).all (fun i => !det.contains i) &&
      (attrSigAt s.tree k).all (fun p => normalizeNamespace p.2 == p.2)) &&
    ks.all (fun k₁ => ks.all (fun k₂ => k₁ == k₂ ||
      (attrIdsAt s.tree k₁).all (fun i => !(attrIdsAt s.tree k₂).contains i))) &&
    ListUtil.nodupB det &&
    s.detachedAttrs.all (fun a => normalizeNamespace a.namespace == a.namespace &&
      (!a.prefix.isSome || a.namespace.isSome))

theorem attrSigAt_eq_nil_of_not_key {t : Tree} {m : NodeId} (h : m ∉ t.nodes.keys) :
    attrSigAt t m = [] := by
  unfold attrSigAt
  cases hd : t.get? m with
  | none => rfl
  | some d => exact absurd (NodeStore.mem_keys_of_get?_eq_some hd) h

theorem attrIdsAt_eq_nil_of_not_key {t : Tree} {m : NodeId} (h : m ∉ t.nodes.keys) :
    attrIdsAt t m = [] := by
  unfold attrIdsAt; rw [attrSigAt_eq_nil_of_not_key h]; rfl

theorem key_of_mem_attrSigAt {t : Tree} {m : NodeId} {p} (h : p ∈ attrSigAt t m) :
    m ∈ t.nodes.keys := by
  by_cases hk : m ∈ t.nodes.keys
  · exact hk
  · rw [attrSigAt_eq_nil_of_not_key hk] at h; simp at h

theorem key_of_mem_attrIdsAt {t : Tree} {m : NodeId} {i} (h : i ∈ attrIdsAt t m) :
    m ∈ t.nodes.keys := by
  by_cases hk : m ∈ t.nodes.keys
  · exact hk
  · rw [attrIdsAt_eq_nil_of_not_key hk] at h; simp at h

/-- **検査が通れば、attribute の id は一意である。** -/
theorem attrIdsUnique_of_check {s : DOMState} (h : checkAttrIdsUnique s = true) :
    AttrIdsUnique s := by
  unfold checkAttrIdsUnique at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  refine ⟨fun m => ?_, fun m m' hne i hi hi' => ?_, (ListUtil.nodupB_iff _).mp h₃,
    fun m i hi hd => ?_, fun m p hp => ?_, fun p hp => ?_⟩
  · by_cases hk : m ∈ s.tree.nodes.keys
    · exact (ListUtil.nodupB_iff _).mp (h₁ m hk).1.1
    · rw [attrIdsAt_eq_nil_of_not_key hk]; exact List.nodup_nil
  · have := h₂ m (key_of_mem_attrIdsAt hi) m' (key_of_mem_attrIdsAt hi')
    simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at this
    rcases this with he | hall
    · exact hne he
    · have := hall i hi; simp [hi'] at this
  · have := (h₁ m (key_of_mem_attrIdsAt hi)).1.2 i hi
    simp [hd] at this
  · simpa using (h₁ m (key_of_mem_attrSigAt hp)).2 p hp
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    have := h₄ a ha
    simp only [beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
    refine ⟨this.1, fun hp => ?_⟩
    rcases this.2 with h | h
    · exact absurd hp (by simp [detachedSig, h])
    · exact h

/-! ## 木の構造を変える primitive -/

theorem detachWithLiveAdjust_detachedAttrs {s s' : DOMState} {n : NodeId}
    (h : detachWithLiveAdjust s n = .ok s') : s'.detachedAttrs = s.detachedAttrs := by
  obtain ⟨t', -, hs⟩ := detachWithLiveAdjust_cases h
  rw [hs]
  simp

theorem remove_detachedAttrs {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : remove s n b = .ok s') : s'.detachedAttrs = s.detachedAttrs := by
  obtain ⟨p, s₁, -, hd, hrec⟩ := remove_cases h
  have := detachWithLiveAdjust_detachedAttrs hd
  rcases hrec with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [this]

theorem attrFrame_remove {s s' : DOMState} {n : NodeId} {b : Bool} (h : remove s n b = .ok s') :
    AttrFrame s s' :=
  AttrFrame.of_shape (shapePreserving_remove h) (remove_detachedAttrs h)

theorem attrFrame_removeEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {b : Bool}, removeEach s ns b = .ok s' → AttrFrame s s'
  | [], _, _, _, h => by
    simp only [removeEach] at h; rw [← Except.ok.inj h]; exact AttrFrame.refl _
  | n :: ns, s, s', b, h => by
    simp only [removeEach] at h
    split at h
    · simp at h
    · next s₁ hr => exact (attrFrame_remove hr).trans (attrFrame_removeEach ns h)

theorem attrFrame_adopt {s s' : DOMState} {node doc : NodeId} (h : adopt s node doc = .ok s') :
    AttrFrame s s' := by
  refine AttrFrame.of_shape (shapePreserving_adopt h) ?_
  obtain ⟨s₁, hstep, hfinal⟩ := adopt_ok_cases h
  have h₁ : s₁.detachedAttrs = s.detachedAttrs := by
    rcases hstep with ⟨_, rfl⟩ | hr
    · rfl
    · exact remove_detachedAttrs hr
  rcases hfinal with rfl | rfl
  · exact h₁
  · simpa using h₁

theorem attrFrame_insertEach :
    ∀ (ns : List NodeId) {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
      {doc : NodeId}, insertEach s parent child doc ns = .ok s' → AttrFrame s s'
  | [], _, _, _, _, _, h => by
    rw [insertEach] at h; rw [← Except.ok.inj h]; exact AttrFrame.refl _
  | n :: ns, s, s', parent, child, doc, h => by
    rw [insertEach] at h
    split at h
    · simp at h
    · next s₁ ha =>
      split at h
      · simp at h
      · next s₂ hi =>
        obtain ⟨hi', hs₂⟩ := DOMState.mapTree_eq_ok hi
        have h₂ : AttrFrame s₁ s₂ :=
          AttrFrame.of_shape (shapePreserving_insertAt hi') (by rw [hs₂]; simp)
        exact ((attrFrame_adopt ha).trans h₂).trans (attrFrame_insertEach ns h)

theorem attrFrame_insertNodesAt {s s' : DOMState} {parent : NodeId} {child : Option NodeId}
    {nodes : List NodeId} {b : Bool} (h : insertNodesAt s parent child nodes b = .ok s') :
    AttrFrame s s' := by
  obtain ⟨s₁, hi, hstep⟩ := insertNodesAt_cases h
  obtain ⟨pd, -, hie⟩ := insertEachAt_cases hi
  have h₀ : AttrFrame s (liveRangeInsertAdjust s parent child nodes.length) :=
    AttrFrame.of_eq (by simp) (by simp)
  have h₁ := h₀.trans (attrFrame_insertEach _ hie)
  rcases hstep with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact h₁
  · exact h₁.trans (AttrFrame.of_eq (by simp) (by simp))

theorem attrFrame_insert {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    {b : Bool} (h : insert s node parent child b = .ok s') : AttrFrame s s' := by
  obtain ⟨_, _, hcase⟩ := insert_cases h
  rcases hcase with ⟨_, _, hs⟩ | ⟨_, _, _, hr, hi⟩ | ⟨_, hi⟩
  · rw [hs]; exact AttrFrame.refl _
  · exact ((attrFrame_removeEach _ hr).trans (AttrFrame.of_eq (by simp) (by simp))).trans
      (attrFrame_insertNodesAt hi)
  · exact attrFrame_insertNodesAt hi

theorem attrFrame_preInsert {s s' : DOMState} {node parent : NodeId} {child : Option NodeId}
    (h : preInsert s node parent child = .ok s') : AttrFrame s s' :=
  attrFrame_insert (preInsert_cases h).2

theorem attrFrame_replace {s s' : DOMState} {child node parent : NodeId}
    (h : replace s child node parent = .ok s') : AttrFrame s s' := by
  obtain ⟨_, s₁, s₂, s₃, _, _, ha, hrm, hi, hs⟩ := replace_cases h
  have h₂ : AttrFrame s₁ s₂ := by
    rcases hrm with ⟨_, rfl⟩ | ⟨_, hrm⟩
    · exact AttrFrame.refl _
    · exact attrFrame_remove hrm
  rw [hs]
  exact (((attrFrame_adopt ha).trans h₂).trans (attrFrame_insert hi)).trans
    (AttrFrame.of_eq (by simp) (by simp))

theorem attrFrame_replaceAll {s s' : DOMState} {node : Option NodeId} {parent : NodeId}
    (h : replaceAll s node parent = .ok s') : AttrFrame s s' := by
  obtain ⟨s₁, s₂, hre, hstep, hs⟩ := replaceAll_cases h
  have h₂ : AttrFrame s₁ s₂ := by
    rcases hstep with ⟨-, rfl⟩ | ⟨_, -, hins⟩
    · exact AttrFrame.refl _
    · exact attrFrame_insert hins
  rw [hs]
  exact ((attrFrame_removeEach _ hre).trans h₂).trans (AttrFrame.of_eq (by simp) (by simp))

theorem attrFrame_move {s s' : DOMState} {node newParent : NodeId} {child : Option NodeId}
    (h : move s node newParent child = .ok s') : AttrFrame s s' := by
  refine AttrFrame.of_shape (shapePreserving_move h) ?_
  unfold move at h
  cases hv : moveValidity s.tree node newParent child with
  | error e => rw [hv] at h; cases h
  | ok u =>
    rw [hv] at h
    cases hp : parentOf s.tree node with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      cases hd : detachWithLiveAdjust s node with
      | error e => rw [hd] at h; cases h
      | ok s₁ =>
        rw [hd] at h
        simp only [] at h
        generalize hm : (liveRangeInsertAdjust s₁ newParent child 1).mapTree
          (fun t => insertAt t newParent node child) = r at h
        cases r with
        | error e => cases h
        | ok s₂ =>
          obtain ⟨-, hs₂⟩ := DOMState.mapTree_eq_ok hm
          have h₂ : s₂.detachedAttrs = s.detachedAttrs := by
            rw [hs₂]; simp [detachWithLiveAdjust_detachedAttrs hd]
          cases h
          simp [h₂]

theorem attrFrame_moveBefore {s s' : DOMState} {parent node : NodeId} {child : Option NodeId}
    (h : moveBefore s parent node child = .ok s') : AttrFrame s s' := by
  obtain ⟨_, _, _, _, hm⟩ := moveBefore_ok h
  exact attrFrame_move hm

/-! ## API -/

theorem attrFrame_appendChild {s s' : DOMState} {parent node : NodeId}
    (h : appendChild s parent node = .ok s') : AttrFrame s s' := attrFrame_preInsert h

theorem attrFrame_insertBefore {s s' : DOMState} {parent node : NodeId} {child : Option NodeId}
    (h : insertBefore s parent node child = .ok s') : AttrFrame s s' := attrFrame_preInsert h

theorem attrFrame_replaceChild {s s' : DOMState} {parent node child : NodeId}
    (h : replaceChild s parent node child = .ok s') : AttrFrame s s' := attrFrame_replace h

theorem attrFrame_removeChild {s s' : DOMState} {parent child : NodeId}
    (h : removeChild s parent child = .ok s') : AttrFrame s s' :=
  attrFrame_remove (preRemove_cases h).2

theorem attrFrame_replaceChildren {s s' : DOMState} {parent : NodeId} {node : Option NodeId}
    (h : replaceChildren s parent node = .ok s') : AttrFrame s s' := by
  unfold replaceChildren at h
  split at h
  · exact attrFrame_replaceAll h
  · split at h
    · cases h
    · exact attrFrame_replaceAll h

theorem attrFrame_before {s s' : DOMState} {this node : NodeId}
    (h : before s this node = .ok s') : AttrFrame s s' := by
  unfold before at h
  split at h
  · cases h; exact AttrFrame.refl _
  · exact attrFrame_preInsert h

theorem attrFrame_after {s s' : DOMState} {this node : NodeId}
    (h : after s this node = .ok s') : AttrFrame s s' := by
  unfold after at h
  split at h
  · cases h; exact AttrFrame.refl _
  · exact attrFrame_preInsert h

theorem attrFrame_replaceWith {s s' : DOMState} {this node : NodeId}
    (h : replaceWith s this node = .ok s') : AttrFrame s s' := by
  unfold replaceWith at h
  split at h
  · cases h; exact AttrFrame.refl _
  · next parent hp =>
    rw [if_pos hp] at h
    exact attrFrame_replace h

theorem attrFrame_nodeRemove {s s' : DOMState} {this : NodeId}
    (h : nodeRemove s this = .ok s') : AttrFrame s s' := by
  rcases nodeRemove_cases h with ⟨-, rfl⟩ | ⟨-, hr⟩
  · exact AttrFrame.refl _
  · exact attrFrame_remove hr

theorem attrFrame_adoptNode {s s' : DOMState} {doc n c : NodeId}
    (h : adoptNode s doc n = .ok (c, s')) : AttrFrame s s' := by
  unfold adoptNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next s₁ ha =>
          cases h
          exact attrFrame_adopt ha

/-! ## replace data -/

theorem attrFrame_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat} {data : String}
    (h : replaceData s n offset count data = .ok s') : AttrFrame s s' := by
  refine AttrFrame.of_shape (shapePreserving_replaceData h) ?_
  unfold replaceData at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; simp [queueCharacterDataRecord]

theorem attrFrame_appendData {s s' : DOMState} {n : NodeId} {data : String}
    (h : appendData s n data = .ok s') : AttrFrame s s' := by
  unfold appendData at h
  split at h
  · cases h
  · exact attrFrame_replaceData h

theorem attrFrame_setData {s s' : DOMState} {n : NodeId} {data : String}
    (h : setData s n data = .ok s') : AttrFrame s s' := by
  unfold setData at h
  split at h
  · cases h
  · exact attrFrame_replaceData h

end Dom
