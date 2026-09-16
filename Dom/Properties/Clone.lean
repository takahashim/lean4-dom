import Dom.Validity.Clone
import Dom.Properties.Create

/-!
# clone した subtree の性質

roadmap §8.4 が求める二つを示す。

* **identity は違う。** copy は原本と別の `NodeId` を持つ（`cloneNode_ne`）。
* **観測できる形は同じ。** copy の subtree は原本の subtree と、kind・data・
  attribute・名前・children の並びまで一致する（`cloneNode_cloneOf`）。

この二つを分けて書けること自体が、node を id で表した model の効き目である。
実装では「同じ object か」と「同じ内容か」が同じ `==` の裏に隠れやすい。
-/

namespace Dom

/-! ## 「copy である」関係 -/

/--
一段ぶんの観測の一致。`R` は children どうしを結ぶ関係である。

見るのは `NodeData.shapeAnon`（parent・children・node document を落とし、
attribute の id も落とした残り）と `data`、そして children の並びである。
`NodeId` も `AttrId` も見ない。copy の `Attr` は原本とは別のものなので、
attribute の id は違ってよい（違わなければならない）。
-/
def CloneStep (t : Tree) (R : NodeId → NodeId → Prop) (c n : NodeId) : Prop :=
  ∃ cd d, t.get? c = some cd ∧ t.get? n = some d ∧
    cd.shapeAnon = d.shapeAnon ∧ cd.data = d.data ∧
    cd.children.length = d.children.length ∧
    ∀ (i : Nat) (a b : NodeId), cd.children[i]? = some a → d.children[i]? = some b → R a b

/--
`CloneOf t c n`：`t` の中で `c` を根とする subtree が `n` を根とする subtree の copy である。

「どの観測でも区別できない」を bisimulation として述べる。関係 `R` を一つ挙げて、
`R` で結ばれた組はどれも一段ぶんの観測が一致し、children どうしもまた `R` で
結ばれている、と言えばよい。有限の木では最大不動点と最小不動点は一致するので、
これは「対応する位置の node の内容がすべて等しい」と同じことである。

`NodeId` を見ないので `CloneOf t n n` も成り立つ。
identity が違うことは `cloneNode_ne` が別に言う。
-/
def CloneOf (t : Tree) (c n : NodeId) : Prop :=
  ∃ R : NodeId → NodeId → Prop, R c n ∧ ∀ a b, R a b → CloneStep t R a b

/-! ## append の frame -/

/-- children を持たない node に descendant は無い。 -/
theorem not_ancestor_of_children_nil {t : Tree} (hwf : WellFormed t) {n : NodeId} {nd : NodeData}
    (hnd : t.get? n = some nd) (hch : nd.children = []) (m : NodeId) : ¬ Ancestor t n m := by
  intro h
  induction h with
  | step hp =>
    obtain ⟨cd, hcd, hcdp⟩ := parentOf_eq_some hp
    obtain ⟨pd, hpd, hmem⟩ := hwf.child_parent _ cd _ hcd hcdp
    rw [hnd] at hpd
    cases hpd
    rw [hch] at hmem
    simp at hmem
  | trans _ _ ih => exact ih

/--
作ったばかりの node を append したときの効果と frame。

`node` は parent も children も持たないので、adopt の中の remove は走らず、
node document の付け替えも `node` 自身で終わる。
-/
theorem append_fresh {s s' : DOMState} {node parent : NodeId} {nd : NodeData}
    (hwf : WellFormed s.tree)
    (hnd : s.tree.get? node = some nd) (hch : nd.children = []) (hp : nd.parent = none)
    (hk : nd.kind ≠ .documentFragment)
    (h : append s node parent = .ok s') :
    (∀ m md, s.tree.get? m = some md → m ≠ node → m ≠ parent → s'.tree.get? m = some md) ∧
    (∃ nd', s'.tree.get? node = some nd' ∧ nd'.shape = nd.shape ∧ nd'.data = nd.data ∧
      nd'.children = []) ∧
    (∀ pd, s.tree.get? parent = some pd → ∃ pd', s'.tree.get? parent = some pd' ∧
      pd'.children = pd.children ++ [node] ∧ pd'.shape = pd.shape ∧ pd'.data = pd.data ∧
      pd'.ownerDocument = pd.ownerDocument) ∧
    s'.ranges = s.ranges := by
  -- append = pre-insert（child は null）
  unfold append at h
  obtain ⟨-, h⟩ := preInsert_cases h
  -- step 2-3 の reference child は null のまま
  rw [preInsertReferenceChild_none] at h
  obtain ⟨pd, s₁, hpd, ha, hi, hr⟩ := insert_single hnd (by simpa using hk) h
  -- adopt は node の node document を変えるだけである。
  have hpn : parentOf (liveRangeInsertAdjust s parent none 1).tree node = none := by
    simp [liveRangeInsertAdjust_tree, parentOf_eq, hnd, hp]
  obtain ⟨hr₁, hs₁⟩ := adopt_of_no_parent hpn ha
  have hother : ∀ m, m ≠ node → s₁.tree.get? m = s.tree.get? m := by
    intro m hm
    rcases hs₁ with he | he
    · rw [he]; simp [liveRangeInsertAdjust_tree]
    · rw [he]
      have : m ∉ preorder (liveRangeInsertAdjust s parent none 1).tree node := by
        rw [liveRangeInsertAdjust_tree]
        rw [mem_preorder_iff hwf hnd]
        rintro (rfl | hanc)
        · exact hm rfl
        · exact not_ancestor_of_children_nil hwf hnd hch m hanc
      rw [get?_setOwnerDocument_of_not_mem this]
      simp [liveRangeInsertAdjust_tree]
  have hnode₁ : ∃ nd₁, s₁.tree.get? node = some nd₁ ∧ nd₁.shape = nd.shape ∧
      nd₁.data = nd.data ∧ nd₁.children = [] ∧ nd₁.parent = none := by
    rcases hs₁ with he | he
    · exact ⟨nd, by rw [he]; simpa [liveRangeInsertAdjust_tree] using hnd, rfl, rfl, hch, hp⟩
    · refine ⟨{ nd with ownerDocument := pd.ownerDocument }, ?_, rfl, rfl, hch, hp⟩
      rw [he, get?_setOwnerDocument_of_mem ?_ (by simpa [liveRangeInsertAdjust_tree] using hnd)]
      rw [liveRangeInsertAdjust_tree, mem_preorder_iff hwf hnd]
      exact Or.inl rfl
  obtain ⟨nd₁, hnd₁, hsh₁, hda₁, hch₁, hp₁⟩ := hnode₁
  -- insertAt は parent と node だけを変える。
  obtain ⟨pd₁, nd₁', hpd₁, hnd₁', -, hanc, -, htree⟩ := insertAt_ok_cases hi
  rw [hnd₁] at hnd₁'
  cases hnd₁'
  -- insertAt は node が parent の inclusive ancestor でないことを確かめている。
  have hnp : node ≠ parent := by
    intro he
    rw [he] at hanc
    rw [isInclusiveAncestorOf_self] at hanc
    simp at hanc
  refine ⟨?_, ?_, ?_, by rw [hr, hr₁]; rfl⟩
  · intro m md hm h1 h2
    rw [htree, get?_insertAtIn_other h1 h2, hother m h1]
    exact hm
  · exact ⟨{ nd₁ with parent := some parent }, by rw [htree]; simp, hsh₁, hda₁, hch₁⟩
  · intro pd₀ hpd₀
    have hpe : pd₁ = pd₀ := by
      rw [hother parent (Ne.symm hnp)] at hpd₁
      rw [hpd₀] at hpd₁
      exact (Option.some.inj hpd₁).symm
    subst hpe
    refine ⟨{ pd₁ with children := ListUtil.insertBefore pd₁.children none node }, ?_, ?_,
      rfl, rfl, rfl⟩
    · rw [htree, get?_insertAtIn_parent hnp]
    · simp


/-! ## `cloneMany` の仕様 -/

/--
clone した node と原本の対応。

原本の側を **`t₀`**（この `cloneNode` 呼び出しの入口の木）で見るのが要点である。
clone は木を伸ばしていくので、途中の状態で原本を見ると、外側の copy が
children を足される分だけ動いてしまう。`t₀` は動かないので、
対応を後の状態へ持ち上げるときに原本側の持ち上げが要らない。
-/
structure CloneCorr (t₀ : Tree) (s s' : DOMState) (C : NodeId → NodeId → Prop) : Prop where
  /-- 対応が付くのは、この呼び出しが作った node だけである。 -/
  new : ∀ a b, C a b → s.tree.get? a = none
  /-- 一段ぶんの観測が一致し、children どうしもまた対応する。 -/
  step : ∀ a b, C a b → ∃ ad bd, s'.tree.get? a = some ad ∧ t₀.get? b = some bd ∧
    ad.shapeAnon = bd.shapeAnon ∧ ad.data = bd.data ∧
    ad.children.length = bd.children.length ∧
    ∀ (i : Nat) (x y : NodeId), ad.children[i]? = some x → bd.children[i]? = some y → C x y

/-- `cloneMany` を呼ぶ側が満たすこと。 -/
structure CloneManyPre (t₀ : Tree) (s : DOMState) (l : List NodeId) (doc : NodeId)
    (parent : Option NodeId) : Prop where
  wf0 : WellFormed t₀
  admissible : AdmissibleDOMState s
  isDoc : IsDocument s.tree doc
  /-- 原本は動いていない。 -/
  sub : ∀ m md, t₀.get? m = some md → s.tree.get? m = some md
  /-- append 先は copy であって原本ではない。 -/
  parentNew : ∀ p, parent = some p → t₀.get? p = none ∧ s.tree.get? p ≠ none
  /-- clone する node は原本にある。 -/
  srcIn : ∀ x ∈ l, t₀.get? x ≠ none
  /-- append するなら fragment ではない（fragment は誰の子でもない）。 -/
  notFragment : ∀ p, parent = some p → ∀ x ∈ l, ∀ xd, t₀.get? x = some xd →
    xd.kind ≠ .documentFragment

/-- `cloneMany` の結果が満たすこと。 -/
structure CloneManySpec (t₀ : Tree) (s : DOMState) (l : List NodeId) (doc : NodeId)
    (parent : Option NodeId) (kids : List NodeId) (s' : DOMState) : Prop where
  /-- append 先以外の node は動かない。 -/
  keep : ∀ m md, s.tree.get? m = some md → (∀ p, parent = some p → m ≠ p) →
    s'.tree.get? m = some md
  /-- append 先の children には copy が順に並ぶ。 -/
  parentGrows : ∀ p pd, parent = some p → s.tree.get? p = some pd →
    ∃ pd', s'.tree.get? p = some pd' ∧ pd'.children = pd.children ++ kids ∧
      pd'.shape = pd.shape ∧ pd'.data = pd.data ∧ pd'.ownerDocument = pd.ownerDocument
  len : kids.length = l.length
  kidsNew : ∀ c ∈ kids, s.tree.get? c = none
  /-- live range は動かない。 -/
  ranges : s'.ranges = s.ranges
  /--
  parent が null なら、copy の node document は引数の document である。
  Document を clone した場合だけは copy 自身になるので、そこは除く。
  -/
  kidsDoc : parent = none → ∀ (i : Nat) (a b : NodeId), kids[i]? = some a → l[i]? = some b →
    ∀ ad bd, s'.tree.get? a = some ad → t₀.get? b = some bd →
      bd.kind ≠ NodeKind.document → ad.ownerDocument = doc
  corr : ∃ C, CloneCorr t₀ s s' C ∧
    ∀ (i : Nat) (a b : NodeId), kids[i]? = some a → l[i]? = some b → C a b

theorem cloneManySpec_nil (t₀ : Tree) (s : DOMState) (doc : NodeId)
    (parent : Option NodeId) : CloneManySpec t₀ s [] doc parent [] s where
  keep := fun _ _ h _ => h
  parentGrows := fun p pd _ hpd => ⟨pd, hpd, by simp, rfl, rfl, rfl⟩
  len := rfl
  kidsNew := by intro c hc; simp at hc
  ranges := rfl
  kidsDoc := by intro _ i a b ha; simp at ha
  corr := ⟨fun _ _ => False, ⟨fun _ _ h => h.elim, fun _ _ h => h.elim⟩, by
    intro i a b ha; simp at ha⟩


/-- `cloneMany` の一段。copy 一つと、その children・兄弟の結果をつなぐ。 -/
theorem cloneManySpec_cons {t₀ : Tree} {s s₂ s₃ s₄ : DOMState} {n copy doc : NodeId}
    {d : NodeData} {rest kids₀ siblings : List NodeId} {parent : Option NodeId}
    (hd : s.tree.get? n = some d) (ht0n : t₀.get? n = some d)
    (hcopyFresh : s.tree.get? copy = none)
    (hpn : ∀ p, parent = some p → s.tree.get? p ≠ none)
    (hkeep₂ : ∀ m md, s.tree.get? m = some md → (∀ p, parent = some p → m ≠ p) →
      s₂.tree.get? m = some md)
    (hcopy₂ : ∃ cd', s₂.tree.get? copy = some cd' ∧ cd'.shapeAnon = d.shapeAnon ∧
      cd'.data = d.data ∧ cd'.children = [])
    (hparent₂ : ∀ p pd, parent = some p → s.tree.get? p = some pd →
      ∃ pd', s₂.tree.get? p = some pd' ∧ pd'.children = pd.children ++ [copy] ∧
        pd'.shape = pd.shape ∧ pd'.data = pd.data ∧ pd'.ownerDocument = pd.ownerDocument)
    (hranges₂ : s₂.ranges = s.ranges)
    (hcopyDoc : parent = none → d.kind ≠ NodeKind.document →
      ∀ cd', s₂.tree.get? copy = some cd' → cd'.ownerDocument = doc)
    (h₁ : CloneManySpec t₀ s₂ d.children doc (some copy) kids₀ s₃)
    (h₂ : CloneManySpec t₀ s₃ rest doc parent siblings s₄) :
    CloneManySpec t₀ s (n :: rest) doc parent (copy :: siblings) s₄ := by
  obtain ⟨cd', hcd'₂, hsh', hda', hch'⟩ := hcopy₂
  have hcopyNe : ∀ p, parent = some p → copy ≠ p := by
    intro p hp he
    exact hpn p hp (by rw [← he]; exact hcopyFresh)
  have hkeep₃ : ∀ m md, s₂.tree.get? m = some md → m ≠ copy → s₃.tree.get? m = some md := by
    intro m md hm hmc
    exact h₁.keep m md hm (by intro q hq; cases hq; exact hmc)
  obtain ⟨cd'', hcd''₃, hch'', hsh'', hda'', hdo''⟩ := h₁.parentGrows copy cd' rfl hcd'₂
  -- 戻り向き：後の状態に無い node は前の状態にも無い。
  have hback₂ : ∀ a, s₂.tree.get? a = none → s.tree.get? a = none := by
    intro a ha
    cases hx : s.tree.get? a with
    | none => rfl
    | some x =>
      exfalso
      cases hpar : parent with
      | none => rw [hkeep₂ a x hx (by simp [hpar])] at ha; simp at ha
      | some p =>
        by_cases hap : a = p
        · subst hap
          obtain ⟨pd', hpd', -⟩ := hparent₂ a x hpar hx
          rw [hpd'] at ha; simp at ha
        · rw [hkeep₂ a x hx (by intro q hq; rw [hpar] at hq; cases hq; exact hap)] at ha
          simp at ha
  have hback₃ : ∀ a, s₃.tree.get? a = none → s₂.tree.get? a = none := by
    intro a ha
    cases hx : s₂.tree.get? a with
    | none => rfl
    | some x =>
      exfalso
      by_cases hac : a = copy
      · subst hac; rw [hcd''₃] at ha; simp at ha
      · rw [hkeep₃ a x hx hac] at ha; simp at ha
  -- append 先は s₂ にある。
  have hparentIn₂ : ∀ p, parent = some p → s₂.tree.get? p ≠ none := by
    intro p hp
    cases hx : s.tree.get? p with
    | none => exact absurd hx (hpn p hp)
    | some pd => obtain ⟨pd', hpd', -⟩ := hparent₂ p pd hp hx; rw [hpd']; simp
  obtain ⟨C₁, hC₁, hC₁k⟩ := h₁.corr
  obtain ⟨C₂, hC₂, hC₂k⟩ := h₂.corr
  refine ⟨?_, ?_, by simp [h₂.len], ?_, by rw [h₂.ranges, h₁.ranges, hranges₂], ?_, ?_⟩
  · -- keep
    intro m md hm hmp
    have hmc : m ≠ copy := by intro he; rw [he, hcopyFresh] at hm; simp at hm
    exact h₂.keep m md (hkeep₃ m md (hkeep₂ m md hm hmp) hmc) hmp
  · -- parentGrows
    intro p pd hp hpd
    obtain ⟨pd', hpd'₂, hchp, hshp, hdap, hdop⟩ := hparent₂ p pd hp hpd
    have hpc : p ≠ copy := by intro he; rw [← he, hpd] at hcopyFresh; simp at hcopyFresh
    obtain ⟨pd'', hpd''₄, hchp', hshp', hdap', hdop'⟩ :=
      h₂.parentGrows p pd' hp (hkeep₃ p pd' hpd'₂ hpc)
    refine ⟨pd'', hpd''₄, ?_, by rw [hshp', hshp], by rw [hdap', hdap],
      by rw [hdop', hdop]⟩
    rw [hchp', hchp]
    simp
  · -- kidsNew
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hcopyFresh
    · exact hback₂ c (hback₃ c (h₂.kidsNew c hc'))
  · -- kidsDoc
    intro hpar i a b ha hb ad bd had hbd hk
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha
      subst hb
      rw [ht0n] at hbd
      cases hbd
      have hc4 : s₄.tree.get? copy = some cd'' := h₂.keep copy cd'' hcd''₃ hcopyNe
      rw [hc4] at had
      cases had
      rw [hdo'']
      exact hcopyDoc hpar hk cd' hcd'₂
    | succ j =>
      simp only [List.getElem?_cons_succ] at ha hb
      exact h₂.kidsDoc hpar j a b ha hb ad bd had hbd hk
  · -- corr
    refine ⟨fun a b => C₁ a b ∨ C₂ a b ∨ (a = copy ∧ b = n), ⟨?_, ?_⟩, ?_⟩
    · rintro a b (hab | hab | ⟨hac, hbn⟩)
      · exact hback₂ a (hC₁.new a b hab)
      · exact hback₂ a (hback₃ a (hC₂.new a b hab))
      · subst hac; exact hcopyFresh
    · rintro a b (hab | hab | ⟨hac, hbn⟩)
      · obtain ⟨ad, bd, had, hbd, hsh, hda, hlen, hch⟩ := hC₁.step a b hab
        refine ⟨ad, bd, h₂.keep a ad had ?_, hbd, hsh, hda, hlen,
          fun i x y hx hy => Or.inl (hch i x y hx hy)⟩
        intro p hp he
        subst he
        exact hparentIn₂ a hp (hC₁.new a b hab)
      · obtain ⟨ad, bd, had, hbd, hsh, hda, hlen, hch⟩ := hC₂.step a b hab
        exact ⟨ad, bd, had, hbd, hsh, hda, hlen,
          fun i x y hx hy => Or.inr (Or.inl (hch i x y hx hy))⟩
      · subst hac
        subst hbn
        refine ⟨cd'', d, h₂.keep _ cd'' hcd''₃ hcopyNe, ht0n,
          (NodeData.shapeAnon_congr hsh'').trans hsh', by rw [hda'', hda'], ?_, ?_⟩
        · rw [hch'', hch']; simpa using h₁.len
        · intro i x y hx hy
          rw [hch'', hch'] at hx
          simp only [List.nil_append] at hx
          exact Or.inl (hC₁k i x y hx hy)
    · intro i a b ha hb
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
        exact Or.inr (Or.inr ⟨ha.symm, hb.symm⟩)
      | succ j =>
        simp only [List.getElem?_cons_succ] at ha hb
        exact Or.inr (Or.inl (hC₂k j a b ha hb))


/-- **`cloneMany` の仕様。** -/
theorem cloneMany_spec (fuel : Nat) : ∀ (t₀ : Tree) (s : DOMState) (l : List NodeId)
    (doc : NodeId) (parent : Option NodeId) (kids : List NodeId) (s' : DOMState),
    CloneManyPre t₀ s l doc parent → cloneMany fuel s l doc parent = .ok (kids, s') →
    CloneManySpec t₀ s l doc parent kids s' := by
  induction fuel with
  | zero =>
    intro t₀ s l doc parent kids s' hpre h
    cases l with
    | nil =>
      simp only [cloneMany, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact cloneManySpec_nil t₀ s doc parent
    | cons n rest => simp [cloneMany] at h
  | succ fuel ih =>
    intro t₀ s l doc parent kids s' hpre h
    cases l with
    | nil =>
      simp only [cloneMany, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact cloneManySpec_nil t₀ s doc parent
    | cons n rest =>
      simp only [cloneMany] at h
      split at h
      · simp at h
      · next d hd =>
        split at h
        · simp at h
        · next s₂ happ =>
          split at h
          · simp at h
          · next kids₀ s₃ hkids =>
            split at h
            · simp at h
            · next siblings s₄ hsib =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              -- 原本の側は動いていないので、`t₀` でも `s` でも同じ data である。
              have ht0n : t₀.get? n = some d := by
                cases hx : t₀.get? n with
                | none => exact absurd hx (hpre.srcIn n (List.mem_cons_self ..))
                | some d₀ =>
                  have hs := hpre.sub n d₀ hx
                  rw [hd] at hs
                  rw [Option.some.inj hs]
              -- step 2
              have hA : AddsNode s.tree (cloneSingle s d doc).2.tree (cloneSingle s d doc).1
                  (cloneData d (cloneDocumentOf d doc (freshId s.tree)) (stateMaxAttrId s + 1)) :=
                withFresh_addsNode s _
              have hcopyFresh : s.tree.get? (cloneSingle s d doc).1 = none := hA.fresh
              have hv₁ : AdmissibleDOMState (cloneSingle s d doc).2 :=
                admissible_createsNode hpre.admissible
                  (createsNode_withFresh (freshNodeData_cloneData hpre.admissible hd hpre.isDoc))
              have hdoc₁ : IsDocument (cloneSingle s d doc).2.tree doc := by
                obtain ⟨dd, hdd, hk⟩ := hpre.isDoc
                exact ⟨dd, hA.get?_of hdd, hk⟩
              have hpn : ∀ p, parent = some p → s.tree.get? p ≠ none :=
                fun p hp => (hpre.parentNew p hp).2
              -- step 4
              have hfacts :
                  (∀ m md, s.tree.get? m = some md → (∀ p, parent = some p → m ≠ p) →
                    s₂.tree.get? m = some md) ∧
                  (∃ cd', s₂.tree.get? (cloneSingle s d doc).1 = some cd' ∧
                    cd'.shapeAnon = d.shapeAnon ∧ cd'.data = d.data ∧ cd'.children = []) ∧
                  (∀ p pd, parent = some p → s.tree.get? p = some pd →
                    ∃ pd', s₂.tree.get? p = some pd' ∧
                      pd'.children = pd.children ++ [(cloneSingle s d doc).1] ∧
                      pd'.shape = pd.shape ∧ pd'.data = pd.data ∧
                      pd'.ownerDocument = pd.ownerDocument) ∧
                  s₂.ranges = s.ranges := by
                cases hpar : parent with
                | none =>
                  rw [hpar] at happ
                  simp only [cloneAppend] at happ
                  have he : (cloneSingle s d doc).2 = s₂ := Except.ok.inj happ
                  refine ⟨?_, ?_, ?_, by rw [← he]; rfl⟩
                  · intro m md hm _
                    rw [← he, hA.others m (hA.ne_of_mem hm)]
                    exact hm
                  · exact ⟨cloneData d (cloneDocumentOf d doc (freshId s.tree))
                      (stateMaxAttrId s + 1), by rw [← he]; exact hA.created,
                      cloneData_shapeAnon .., rfl, rfl⟩
                  · intro p pd hp _; simp at hp
                | some p =>
                  rw [hpar] at happ
                  simp only [cloneAppend] at happ
                  have hkf : (cloneData d (cloneDocumentOf d doc (freshId s.tree)) (stateMaxAttrId s + 1)).kind
                      ≠ NodeKind.documentFragment := by
                    simpa using hpre.notFragment p hpar n (List.mem_cons_self ..) d ht0n
                  obtain ⟨hfr, hnode, hpp, hrg⟩ :=
                    append_fresh hv₁.wellFormed hA.created rfl rfl hkf happ
                  refine ⟨?_, ?_, ?_, by rw [hrg]; rfl⟩
                  · intro m md hm hmp
                    have hmc : m ≠ (cloneSingle s d doc).1 := hA.ne_of_mem hm
                    refine hfr m md ?_ hmc (hmp p rfl)
                    rw [hA.others m hmc]; exact hm
                  · obtain ⟨nd', hnd', hsh, hda, hch⟩ := hnode
                    exact ⟨nd', hnd', (NodeData.shapeAnon_congr hsh).trans (cloneData_shapeAnon ..),
                      by simpa using hda, hch⟩
                  · intro q pd hq hpd
                    cases Option.some.inj hq
                    refine hpp pd ?_
                    rw [hA.others p (hA.ne_of_mem hpd)]
                    exact hpd
              obtain ⟨hkeep₂, hcopy₂, hparent₂, hranges₂⟩ := hfacts
              have hv₂ : AdmissibleDOMState s₂ := (admissible_cloneAppend hv₁ happ).1
              have hdoc₂ : IsDocument s₂.tree doc :=
                hdoc₁.map (admissible_cloneAppend hv₁ happ).2
              have hsub₂ : ∀ m md, t₀.get? m = some md → s₂.tree.get? m = some md := by
                intro m md hm
                refine hkeep₂ m md (hpre.sub m md hm) ?_
                intro p hp he
                rw [he, (hpre.parentNew p hp).1] at hm
                simp at hm
              have ht0copy : t₀.get? (cloneSingle s d doc).1 = none := by
                cases hx : t₀.get? (cloneSingle s d doc).1 with
                | none => rfl
                | some x => exfalso; rw [hpre.sub _ x hx] at hcopyFresh; simp at hcopyFresh
              -- step 5：children
              have hpre₁ : CloneManyPre t₀ s₂ d.children doc (some (cloneSingle s d doc).1) := by
                refine ⟨hpre.wf0, hv₂, hdoc₂, hsub₂, ?_, ?_, ?_⟩
                · intro p hp
                  cases Option.some.inj hp
                  refine ⟨ht0copy, ?_⟩
                  obtain ⟨cd', hcd', -⟩ := hcopy₂
                  rw [hcd']; simp
                · intro x hx
                  obtain ⟨xd, hxd, -⟩ := hpre.wf0.parent_child n d ht0n x hx
                  rw [hxd]; simp
                · intro q _ x hx xd hxd hk
                  obtain ⟨xd', hxd', hxp⟩ := hpre.admissible.wellFormed.parent_child n d hd x hx
                  have hxe : xd' = xd := by
                    rw [hpre.sub x xd hxd] at hxd'; exact (Option.some.inj hxd').symm
                  subst hxe
                  rw [hpre.admissible.structural.fragmentHasNoParent x _ hxd' hk] at hxp
                  simp at hxp
              have h₁ := ih t₀ s₂ d.children doc (some (cloneSingle s d doc).1) kids₀ s₃ hpre₁ hkids
              obtain ⟨hv₃, hdoc₃⟩ :=
                admissible_cloneMany fuel s₂ d.children doc _ kids₀ s₃ hv₂ hdoc₂ hkids
              -- 兄弟
              have hkeep₃ : ∀ m md, s₂.tree.get? m = some md →
                  m ≠ (cloneSingle s d doc).1 → s₃.tree.get? m = some md := by
                intro m md hm hmc
                exact h₁.keep m md hm (by intro q hq; cases Option.some.inj hq; exact hmc)
              have hpre₂ : CloneManyPre t₀ s₃ rest doc parent := by
                refine ⟨hpre.wf0, hv₃, hdoc₃, ?_, ?_, ?_, ?_⟩
                · intro m md hm
                  refine hkeep₃ m md (hsub₂ m md hm) ?_
                  intro he; rw [he, ht0copy] at hm; simp at hm
                · intro p hp
                  refine ⟨(hpre.parentNew p hp).1, ?_⟩
                  cases hx : s.tree.get? p with
                  | none => exact absurd hx (hpn p hp)
                  | some pd =>
                    obtain ⟨pd', hpd', -⟩ := hparent₂ p pd hp hx
                    have hpc : p ≠ (cloneSingle s d doc).1 := by
                      intro he; rw [he, hcopyFresh] at hx; simp at hx
                    rw [hkeep₃ p pd' hpd' hpc]; simp
                · intro x hx; exact hpre.srcIn x (List.mem_cons_of_mem _ hx)
                · intro p hp x hx xd hxd
                  exact hpre.notFragment p hp x (List.mem_cons_of_mem _ hx) xd hxd
              have h₂ := ih t₀ s₃ rest doc parent siblings s₄ hpre₂ hsib
              refine cloneManySpec_cons hd ht0n hcopyFresh hpn hkeep₂ hcopy₂ hparent₂ hranges₂
                ?_ h₁ h₂
              -- parent が null なら append は起きないので、copy の node document はそのままである。
              intro hpar hk cd' hcd'
              rw [hpar] at happ
              simp only [cloneAppend] at happ
              have he : (cloneSingle s d doc).2 = s₂ := Except.ok.inj happ
              rw [← he] at hcd'
              rw [hA.created] at hcd'
              cases hcd'
              simp [cloneDocumentOf, hk]


/-! ## `cloneNode` / `cloneNodeIn` -/

/-- **deep clone がすること。** -/
theorem cloneNodeIn_deep_spec {s s' : DOMState} {n doc c : NodeId}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc true = .ok (c, s')) :
    ∃ d, s.tree.get? n = some d ∧
      (∀ m md, s.tree.get? m = some md → s'.tree.get? m = some md) ∧
      s.tree.get? c = none ∧ CloneOf s'.tree c n ∧ s'.ranges = s.ranges ∧
      (d.kind ≠ NodeKind.document → ∀ cd, s'.tree.get? c = some cd →
        cd.ownerDocument = doc) := by
  simp only [cloneNodeIn] at h
  split at h
  · simp at h
  · next d hd =>
    rw [if_pos True.intro] at h
    split at h
    · simp at h
    · next c₀ kids s₀ hcm =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hpre : CloneManyPre s.tree s [n] doc none := by
        refine ⟨hv.wellFormed, hv, hdoc, fun _ _ hm => hm, by simp, ?_, by simp⟩
        intro x hx
        rcases List.mem_singleton.mp hx with rfl
        rw [hd]; simp
      have hspec := cloneMany_spec (s.tree.size + 1) s.tree s [n] doc none
        (c₀ :: kids) s₀ hpre hcm
      have hkeep : ∀ m md, s.tree.get? m = some md → s₀.tree.get? m = some md :=
        fun m md hm => hspec.keep m md hm (by simp)
      obtain ⟨C, hC, hCk⟩ := hspec.corr
      refine ⟨d, hd, hkeep, hspec.kidsNew c₀ (List.mem_cons_self ..), ⟨C, ?_, ?_⟩,
        hspec.ranges, ?_⟩
      · exact hCk 0 c₀ n (by simp) (by simp)
      · intro a b hab
        obtain ⟨ad, bd, had, hbd, hsh, hda, hlen, hch⟩ := hC.step a b hab
        exact ⟨ad, bd, had, hkeep b bd hbd, hsh, hda, hlen, hch⟩
      · intro hk cd hcd
        exact hspec.kidsDoc rfl 0 c₀ n (by simp) (by simp) cd d hcd hd hk
    · simp at h

/--
**shallow clone がすること。** §4.4 "clone a single node" そのものである。
children を持たない detach された copy が一つ増える。
-/
theorem cloneNodeIn_shallow_spec {s s' : DOMState} {n doc c : NodeId}
    (h : cloneNodeIn s n doc false = .ok (c, s')) :
    ∃ d cd, s.tree.get? n = some d ∧ cd.shapeAnon = d.shapeAnon ∧ cd.data = d.data ∧
      cd.children = [] ∧ cd.parent = none ∧
      cd.ownerDocument = cloneDocumentOf d doc c ∧ AddsNode s.tree s'.tree c cd := by
  simp only [cloneNodeIn] at h
  split at h
  · simp at h
  · next d hd =>
    rw [if_neg (by simp : ¬(false = true))] at h
    have he := Except.ok.inj h
    have hc : (cloneSingle s d doc).1 = c := congrArg Prod.fst he
    have hs : (cloneSingle s d doc).2 = s' := congrArg Prod.snd he
    refine ⟨d, cloneData d (cloneDocumentOf d doc (freshId s.tree)) (stateMaxAttrId s + 1),
      hd, cloneData_shapeAnon .., rfl, rfl, rfl, by rw [← hc]; rfl, ?_⟩
    rw [← hc, ← hs]
    exact withFresh_addsNode s _

/-- **clone の id は木にまだ無い。** -/
theorem cloneNodeIn_fresh {s s' : DOMState} {n doc c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc subtree = .ok (c, s')) : s.tree.get? c = none := by
  cases subtree with
  | false =>
    obtain ⟨d₀, cd, -, -, -, -, -, -, hadd⟩ := cloneNodeIn_shallow_spec h
    exact hadd.fresh
  | true =>
    obtain ⟨-, -, -, hfr, -, -, -⟩ := cloneNodeIn_deep_spec hv hdoc h
    exact hfr

/-- **clone は木にあった node を動かさない。** -/
theorem cloneNodeIn_keep {s s' : DOMState} {n doc c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc subtree = .ok (c, s'))
    {m : NodeId} {md : NodeData} (hm : s.tree.get? m = some md) :
    s'.tree.get? m = some md := by
  cases subtree with
  | false =>
    obtain ⟨d₀, cd, -, -, -, -, -, -, hadd⟩ := cloneNodeIn_shallow_spec h
    rw [hadd.others m (hadd.ne_of_mem hm)]
    exact hm
  | true =>
    obtain ⟨-, -, hk, -, -, -, -⟩ := cloneNodeIn_deep_spec hv hdoc h
    exact hk m md hm

/-- **clone は live range を動かさない。** copy の中を指す range はまだ無いからである。 -/
theorem cloneNodeIn_ranges {s s' : DOMState} {n doc c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc subtree = .ok (c, s')) : s'.ranges = s.ranges := by
  cases subtree with
  | false =>
    simp only [cloneNodeIn] at h
    split at h
    · simp at h
    · next d hd =>
      rw [if_neg (by simp : ¬(false = true))] at h
      have hs : (cloneSingle s d doc).2 = s' := congrArg Prod.snd (Except.ok.inj h)
      rw [← hs]
      rfl
  | true =>
    obtain ⟨-, -, -, -, -, hr, -⟩ := cloneNodeIn_deep_spec hv hdoc h
    exact hr

/-- **copy の node document は引数の document である。** Document の clone だけは別。 -/
theorem cloneNodeIn_ownerDocument {s s' : DOMState} {n doc c : NodeId} {subtree : Bool}
    {d cd : NodeData} (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (hd : s.tree.get? n = some d) (hk : d.kind ≠ NodeKind.document)
    (h : cloneNodeIn s n doc subtree = .ok (c, s')) (hcd : s'.tree.get? c = some cd) :
    cd.ownerDocument = doc := by
  cases subtree with
  | false =>
    obtain ⟨d₀, cd₀, hd₀, -, -, -, -, hdo, hadd⟩ := cloneNodeIn_shallow_spec h
    rw [hd] at hd₀
    cases hd₀
    rw [hadd.created] at hcd
    cases hcd
    rw [hdo]
    simp [cloneDocumentOf, hk]
  | true =>
    obtain ⟨d₀, hd₀, -, -, -, -, hdo⟩ := cloneNodeIn_deep_spec hv hdoc h
    rw [hd] at hd₀
    cases hd₀
    exact hdo hk cd hcd

/--
**clone は原本と同じ形である。**

roadmap §8.4 の「structurally equivalent」。deep clone について、copy の subtree が
原本の subtree と kind・data・attribute・名前・children の並びまで一致する。
-/
theorem cloneNodeIn_cloneOf {s s' : DOMState} {n doc c : NodeId}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc true = .ok (c, s')) : CloneOf s'.tree c n := by
  obtain ⟨-, -, -, -, hcl, -, -⟩ := cloneNodeIn_deep_spec hv hdoc h
  exact hcl

/-- **clone は原本とは別の node である。** roadmap §8.4 の「identity is different」。 -/
theorem cloneNodeIn_ne {s s' : DOMState} {n doc c : NodeId} {subtree : Bool}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (h : cloneNodeIn s n doc subtree = .ok (c, s')) : c ≠ n := by
  intro he
  have hn : s.tree.get? n ≠ none := by
    simp only [cloneNodeIn] at h
    split at h
    · simp at h
    · next d hd => rw [hd]; simp
  exact hn (he ▸ cloneNodeIn_fresh hv hdoc h)

/-! ### `cloneNode` -/

/-- clone する node の node document は Document である。 -/
theorem isDocument_of_get? {s : DOMState} {n : NodeId} {d : NodeData}
    (hv : AdmissibleDOMState s) (hd : s.tree.get? n = some d) :
    IsDocument s.tree d.ownerDocument :=
  hv.wellFormed.ownerDocument_is_document n d hd

theorem cloneNode_cases {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (h : cloneNode s n deep = .ok (c, s')) :
    ∃ d, s.tree.get? n = some d ∧ cloneNodeIn s n d.ownerDocument deep = .ok (c, s') := by
  unfold cloneNode at h
  split at h
  · simp at h
  · next d hd => exact ⟨d, hd, h⟩

/-- **clone は原本と同じ形である。** -/
theorem cloneNode_cloneOf {s s' : DOMState} {n c : NodeId}
    (hv : AdmissibleDOMState s) (h : cloneNode s n true = .ok (c, s')) :
    CloneOf s'.tree c n := by
  obtain ⟨d, hd, h'⟩ := cloneNode_cases h
  exact cloneNodeIn_cloneOf hv (isDocument_of_get? hv hd) h'

/-- **clone は原本とは別の node である。** -/
theorem cloneNode_ne {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (hv : AdmissibleDOMState s) (h : cloneNode s n deep = .ok (c, s')) : c ≠ n := by
  obtain ⟨d, hd, h'⟩ := cloneNode_cases h
  exact cloneNodeIn_ne hv (isDocument_of_get? hv hd) h'

/-- **clone の id は木にまだ無い。** -/
theorem cloneNode_fresh {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (hv : AdmissibleDOMState s) (h : cloneNode s n deep = .ok (c, s')) :
    s.tree.get? c = none := by
  obtain ⟨d, hd, h'⟩ := cloneNode_cases h
  exact cloneNodeIn_fresh hv (isDocument_of_get? hv hd) h'

/-- **clone は木にあった node を動かさない。** -/
theorem cloneNode_keep {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (hv : AdmissibleDOMState s) (h : cloneNode s n deep = .ok (c, s'))
    {m : NodeId} {md : NodeData} (hm : s.tree.get? m = some md) :
    s'.tree.get? m = some md := by
  obtain ⟨d, hd, h'⟩ := cloneNode_cases h
  exact cloneNodeIn_keep hv (isDocument_of_get? hv hd) h' hm

/-- **clone は live range を動かさない。** -/
theorem cloneNode_ranges {s s' : DOMState} {n c : NodeId} {deep : Bool}
    (hv : AdmissibleDOMState s) (h : cloneNode s n deep = .ok (c, s')) :
    s'.ranges = s.ranges := by
  obtain ⟨d, hd, h'⟩ := cloneNode_cases h
  exact cloneNodeIn_ranges hv (isDocument_of_get? hv hd) h'

end Dom
