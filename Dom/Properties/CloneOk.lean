import Dom.Properties.Clone
import Dom.Properties.Import
import Dom.Properties.Contract

/-!
# `cloneNode` は失敗しない

`cloneNode` は §4.2.3 の `append` を呼ぶので、原理的には pre-insert validity の
検査に落ちて `HierarchyRequestError` を返しうる。妥当な木ではそうならないことを示す。

落ちうる場所は三つある。

1. fuel が尽きる。
2. `append` の pre-insert validity。
3. `append` の中の `adopt` と `insertAt`。

三つとも、妥当な木では起きないことをここで示す。
-/

namespace Dom

/-! ## pre-insert validity を組み立てる -/

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


/-! ## `append` は落ちない -/

/-- parent を持たない node の `adopt` は必ず成功し、node document を変えるだけである。 -/
theorem adopt_isOk_of_no_parent {s : DOMState} {node doc : NodeId} {nd : NodeData}
    (hnd : s.tree.get? node = some nd) (hp : nd.parent = none) :
    ∃ s₁, adopt s node doc = .ok s₁ ∧
      (s₁ = s ∨ s₁ = s.withTree (setOwnerDocument s.tree node doc)) := by
  have hown : ownerDocumentOf s.tree node = some nd.ownerDocument := by
    simp [ownerDocumentOf, hnd]
  have hpn : parentOf s.tree node = none := by simp [parentOf, hnd, hp]
  unfold adopt
  rw [hown]
  simp only [hpn]
  by_cases hd : doc = nd.ownerDocument
  · exact ⟨s, by simp [hd], Or.inl rfl⟩
  · exact ⟨_, by simp [hd], Or.inr rfl⟩

/--
**作ったばかりの node を append すると必ず成功する。**

pre-insert validity を通っていれば、そのあとの `adopt` も `insertAt` も落ちない。
`adopt` は node が parent を持たないので `remove` を呼ばず、node document を
付け替えるだけである。`insertAt` の前提条件は validity から出る。
-/
theorem append_fresh_isOk {s : DOMState} {node parent : NodeId} {nd : NodeData}
    (hwf : WellFormed s.tree) (hnd : s.tree.get? node = some nd)
    (hp : nd.parent = none) (hch : nd.children = [])
    (hnf : nd.kind ≠ NodeKind.documentFragment)
    (hv : ensurePreInsertionValidity s.tree node parent none [] = .ok ()) :
    ∃ s', append s node parent = .ok s' := by
  obtain ⟨⟨pd, hpd⟩, -, hanc, -⟩ := ensurePreInsertionValidity_ok hv
  have hnp : node ≠ parent := by
    intro he
    rw [(isInclusiveAncestorOf_iff hwf node parent).mpr (Or.inl he)] at hanc
    simp at hanc
  obtain ⟨s₁, hadopt, hcase⟩ := adopt_isOk_of_no_parent (doc := pd.ownerDocument) hnd hp
  -- adopt の後も、node は parent も children も持たず、parent は木にある。
  have hkey : ∃ nd₁ pd₁, s₁.tree.get? node = some nd₁ ∧ s₁.tree.get? parent = some pd₁ ∧
      nd₁.parent = none ∧ nd₁.children = [] ∧ WellFormed s₁.tree ∧
      (∀ a m, Ancestor s₁.tree a m → Ancestor s.tree a m) := by
    have hpmem : parent ∉ preorder s.tree node := by
      rw [mem_preorder_iff hwf hnd]
      intro h
      rw [(isInclusiveAncestorOf_iff hwf node parent).mpr h] at hanc
      simp at hanc
    rcases hcase with rfl | rfl
    · exact ⟨nd, pd, hnd, hpd, hp, hch, hwf, fun _ _ h => h⟩
    · refine ⟨{ nd with ownerDocument := pd.ownerDocument }, pd, ?_, ?_, hp, hch, ?_, ?_⟩
      · exact get?_setOwnerDocument_of_mem (mem_preorder_self hwf hnd) hnd
      · rw [DOMState.withTree_tree, get?_setOwnerDocument_of_not_mem hpmem]
        exact hpd
      · obtain ⟨dd, hdd, hk⟩ := isDocument_ownerDocument hwf hpd
        exact setOwnerDocument_preserves_wellformed hwf hdd hk
      · intro a m h; exact ancestor_setOwnerDocument.mp h
  obtain ⟨nd₁, pd₁, hnd₁, hpd₁, hp₁, hch₁, hwf₁, hanc₁⟩ := hkey
  have hanc' : isInclusiveAncestorOf s₁.tree node parent = false := by
    cases hb : isInclusiveAncestorOf s₁.tree node parent with
    | false => rfl
    | true =>
      exfalso
      rcases (isInclusiveAncestorOf_iff hwf₁ node parent).mp hb with he | ha
      · exact hnp he
      · exact not_ancestor_of_children_nil hwf₁ hnd₁ hch₁ parent ha
  have hins := insertAt_eq_ok (child := (none : Option NodeId)) hpd₁ hnd₁ hp₁ hanc' (by simp)
  unfold append preInsert
  rw [hv]
  show ∃ s', insert s node parent none = .ok s'
  rw [insert_of_not_fragment hnd hnf]
  unfold insertNodesAt
  simp only [liveRangeInsertAdjust]
  unfold insertEachAt
  rw [hpd]
  simp only [insertEach, hadopt, DOMState.mapTree, hins]
  exact ⟨_, rfl⟩


/-! ## fuel は足りる -/

/-- 要素ごとの大小から和の大小へ。 -/
theorem sum_le_sum {α : Type _} : ∀ (l : List α) (f g : α → Nat), (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _, _, _ => Nat.le_refl _
  | x :: rest, f, g, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (sum_le_sum rest f g fun y hy => h y (List.mem_cons_of_mem _ hy))

/--
`l` を根とする forest の node 数。fuel `f` までで数える。

`cloneMany` に要る fuel の上界である。**`preorderFuel` をそのまま使う**のが要点で、
`preorderFuel t (f+1) n = n :: children.flatMap (preorderFuel t f)` が定義から出るので、
「一段降りると fuel も一つ減る」という形がそのまま measure になる。
fuel を揃えた `preorder` を使うと、fuel の差を埋める補題が要る。
-/
def forestSize (t : Tree) (f : Nat) (l : List NodeId) : Nat :=
  (l.map (fun n => (preorderFuel t f n).length)).sum

@[simp] theorem forestSize_nil (t : Tree) (f : Nat) : forestSize t f [] = 0 := rfl

theorem forestSize_cons (t : Tree) (f : Nat) (n : NodeId) (l : List NodeId) :
    forestSize t f (n :: l) = (preorderFuel t f n).length + forestSize t f l := by
  simp [forestSize]

/-- fuel を増やしても `preorderFuel` は短くならない。 -/
theorem length_preorderFuel_mono (t : Tree) :
    ∀ (f : Nat) (n : NodeId), (preorderFuel t f n).length ≤ (preorderFuel t (f + 1) n).length := by
  intro f
  induction f with
  | zero => intro n; simp
  | succ f ih =>
    intro n
    cases hn : t.get? n with
    | none => rw [preorderFuel_succ_neg hn, preorderFuel_succ_neg hn]; exact Nat.le_refl _
    | some d =>
      rw [preorderFuel_succ_pos hn, preorderFuel_succ_pos hn]
      simp only [List.length_cons, List.length_flatMap]
      exact Nat.add_le_add_right (sum_le_sum _ _ _ fun c _ => ih c) 1

theorem forestSize_mono (t : Tree) (f : Nat) (l : List NodeId) :
    forestSize t f l ≤ forestSize t (f + 1) l :=
  sum_le_sum l _ _ fun n _ => length_preorderFuel_mono t f n

/-- 一段降りると、node 数は children の forest の分だけになる。 -/
theorem length_preorderFuel_succ {t : Tree} {n : NodeId} {d : NodeData}
    (h : t.get? n = some d) (f : Nat) :
    (preorderFuel t (f + 1) n).length = 1 + forestSize t f (childrenOf t n) := by
  rw [preorderFuel_succ_pos h]
  simp [forestSize, List.length_flatMap, Nat.add_comm]

/-- 木の node を重複なく並べた列は、store の要素数より長くならない。 -/
theorem length_preorderFuel_le_size {t : Tree} (hwf : WellFormed t) (f : Nat) (n : NodeId) :
    (preorderFuel t f n).length ≤ t.size := by
  have hsub : preorderFuel t f n ⊆ t.nodes.keys := by
    intro x hx
    obtain ⟨d, hd⟩ := exists_data_of_mem_preorderFuel f n x hx
    exact NodeStore.mem_keys_of_get?_eq_some hd
  have hle := Dom.ListUtil.length_le_of_nodup_subset (preorderFuel_nodup hwf f n) hsub
  rw [NodeStore.length_keys] at hle
  exact hle


/-! ## Document の children の kind 列 -/

/-- `l` の kind を並べたもの。 -/
def kindsOf (t : Tree) (l : List NodeId) : List (Option NodeKind) := l.map (kindOf t)

theorem length_filter_map {α β : Type _} (f : α → β) (p : β → Bool) :
    ∀ l : List α, ((l.map f).filter p).length = (l.filter (fun x => p (f x))).length
  | [] => rfl
  | x :: rest => by
    by_cases h : p (f x) <;>
      simp [List.filter_cons, h, length_filter_map f p rest]

theorem exists_split_of_map_eq {α β : Type _} (f : α → β) :
    ∀ (l : List α) (A B : List β), l.map f = A ++ B →
      ∃ CA CB, l = CA ++ CB ∧ CA.map f = A ∧ CB.map f = B
  | l, [], B, h => ⟨[], l, rfl, rfl, by simpa using h⟩
  | [], a :: A, B, h => by simp at h
  | x :: rest, a :: A, B, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨CA, CB, hl, hA, hB⟩ := exists_split_of_map_eq f rest A B h.2
    exact ⟨x :: CA, CB, by simp [hl], by simp [hA, h.1], hB⟩

/-- 左側にある要素で分割すると、右側は丸ごと後半に残る。 -/
theorem splitAt?_append_left {α : Type _} [DecidableEq α] :
    ∀ (A B : List α) (e : α), e ∈ A →
      ∃ u v w, Dom.ListUtil.splitAt? (A ++ B) e = some (u, v) ∧ v = w ++ B
  | [], _, _, h => by simp at h
  | x :: A, B, e, h => by
    by_cases hx : x = e
    · exact ⟨[], A ++ B, A, by simp [Dom.ListUtil.splitAt?, hx], rfl⟩
    · have hmem : e ∈ A := by
        rcases List.mem_cons.mp h with he | hm
        · exact absurd he.symm hx
        · exact hm
      obtain ⟨u, v, w, hs, hv⟩ := splitAt?_append_left A B e hmem
      exact ⟨x :: u, v, w, by simp [Dom.ListUtil.splitAt?, hx, hs], hv⟩

/--
Document の children の kind 列が満たすこと。

`DocumentChildrenOk` は「children のうち element であるもの」を数える形で書いてあるが、
clone は children を一つずつ append していくので、**既に入れた分と残りを繋いだ列**の
形で持つほうが扱いやすい。append しても列は変わらないので、不変条件がそのまま保たれる。
-/
structure DocKindsOk (ks : List (Option NodeKind)) : Prop where
  /-- element の子は高々一つ。 -/
  element : ((ks.filter (· == some NodeKind.element)).length) ≤ 1
  /-- doctype の子は高々一つ。 -/
  doctype : ((ks.filter (· == some NodeKind.documentType)).length) ≤ 1
  /-- Text の子は無い。 -/
  text : ∀ k ∈ ks, ∀ kk, k = some kk → kk.isText = false
  /-- doctype は element より前にある。 -/
  order : ∀ A B, ks = A ++ B → some NodeKind.element ∈ A →
    some NodeKind.documentType ∉ B

theorem docKindsOk_of_documentChildrenOk {t : Tree} {doc : NodeId}
    (h : DocumentChildrenOk t doc) : DocKindsOk (kindsOf t (childrenOf t doc)) := by
  obtain ⟨he, hdt, htx, hord⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kindsOf, length_filter_map]
    exact he
  · rw [kindsOf, length_filter_map]
    exact hdt
  · intro k hk kk hkk
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp hk
    have : c ∈ textChildren t doc → False := by rw [htx]; simp
    by_cases hkt : kk.isText = true
    · exact absurd (this (by
        refine List.mem_filter.mpr ⟨hc, ?_⟩
        rw [← hce] at hkk
        rw [hkk]
        exact hkt)) (by simp)
    · simpa using hkt
  · intro A B hks helem hdoc
    obtain ⟨CA, CB, hsplit, hA, hB⟩ := exists_split_of_map_eq (kindOf t) _ A B hks
    obtain ⟨e, hemem, hek⟩ := List.mem_map.mp (hA ▸ helem : some NodeKind.element ∈ CA.map (kindOf t))
    obtain ⟨dt, hdmem, hdk⟩ :=
      List.mem_map.mp (hB ▸ hdoc : some NodeKind.documentType ∈ CB.map (kindOf t))
    have hein : e ∈ elementChildren t doc := by
      refine List.mem_filter.mpr ⟨?_, by simp [hek]⟩
      rw [hsplit]
      exact List.mem_append_left _ hemem
    have hfalse := hord e hein
    obtain ⟨u, v, w, hs, hv⟩ := splitAt?_append_left CA CB e hemem
    unfold doctypeFollows at hfalse
    rw [hsplit, hs] at hfalse
    simp only at hfalse
    have : v.any (fun x => kindOf t x == some NodeKind.documentType) = true := by
      refine List.any_eq_true.mpr ⟨dt, ?_, by simp [hdk]⟩
      rw [hv]
      exact List.mem_append_right _ hdmem
    rw [this] at hfalse
    simp at hfalse


/-! ## append 先の不変条件 -/

/--
`p` に `l` の copy を順に append していけること。

要点は `docKinds` である。**`p` に既に入れた children の kind 列と、これから入れる
`l` の kind 列を繋いだもの**が Document の制約を満たす、という形にしてある。
一つ append すると前半が一つ伸びて後半が一つ縮むだけなので、繋いだ列は変わらない。
つまりこの条件は自分で自分を保つ。
-/
structure AppendableInto (t₀ t : Tree) (l : List NodeId) (p : NodeId) : Prop where
  /-- append 先は木にある。 -/
  present : ∃ pd, t.get? p = some pd
  /-- 入れるものがあるなら、append 先は children を持てる kind である。 -/
  canHaveChildren : ∀ n ∈ l, ∀ pd, t.get? p = some pd → pd.kind.canHaveChildren = true
  /-- 入れるものは Document でも DocumentFragment でもない（どちらも子になれない）。 -/
  kinds : ∀ n ∈ l, ∀ nd, t₀.get? n = some nd →
    nd.kind ≠ NodeKind.document ∧ nd.kind ≠ NodeKind.documentFragment
  /-- doctype を入れるなら append 先は Document である。 -/
  doctype : ∀ n ∈ l, ∀ nd, t₀.get? n = some nd → nd.kind = NodeKind.documentType →
    ∀ pd, t.get? p = some pd → pd.kind = NodeKind.document
  /-- append 先が Document なら、繋いだ kind 列が制約を満たす。 -/
  docKinds : ∀ pd, t.get? p = some pd → pd.kind = NodeKind.document →
    DocKindsOk (kindsOf t (childrenOf t p) ++ kindsOf t₀ l)

theorem AppendableInto.mono {t₀ t t' : Tree} {l : List NodeId} {p : NodeId}
    (hwf : WellFormed t) (hk : ∀ m md, t.get? m = some md → t'.get? m = some md)
    (h : AppendableInto t₀ t l p) : AppendableInto t₀ t' l p := by
  obtain ⟨pd₀, hpd₀⟩ := h.present
  have hpd₀' : t'.get? p = some pd₀ := hk p pd₀ hpd₀
  have hsame : ∀ pd, t'.get? p = some pd → pd = pd₀ := by
    intro pd hpd; rw [hpd₀'] at hpd; exact (Option.some.inj hpd).symm
  have hchild : kindsOf t' (childrenOf t' p) = kindsOf t (childrenOf t p) := by
    have hch : childrenOf t' p = childrenOf t p := by
      rw [childrenOf_eq hpd₀', childrenOf_eq hpd₀]
    rw [hch, kindsOf, kindsOf]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨cd, hcd, -⟩ := hwf.parent_child p pd₀ hpd₀ c (by rwa [← childrenOf_eq hpd₀])
    simp [kindOf, hcd, hk c cd hcd]
  refine ⟨⟨pd₀, hpd₀'⟩, ?_, h.kinds, ?_, ?_⟩
  · intro n hn pd hpd
    rw [hsame pd hpd]
    exact h.canHaveChildren n hn pd₀ hpd₀
  · intro n hn nd hnd hdt pd hpd
    rw [hsame pd hpd]
    exact h.doctype n hn nd hnd hdt pd₀ hpd₀
  · intro pd hpd hdoc
    rw [hchild]
    exact h.docKinds pd₀ hpd₀ (by rw [← hsame pd hpd]; exact hdoc)


/-! ## append する一つ分の validity -/

theorem length_filter_left {α : Type _} (p : α → Bool) (A B : List α) (x : α)
    (hx : p x = true) (h : ((A ++ x :: B).filter p).length ≤ 1) :
    (A.filter p).length = 0 := by
  rw [List.filter_append, List.length_append, List.filter_cons_of_pos hx,
    List.length_cons] at h
  omega

theorem filter_kinds_nil {t : Tree} {p : NodeId} {k : NodeKind}
    (h : ((kindsOf t (childrenOf t p)).filter (· == some k)).length = 0) :
    (childrenOf t p).filter (fun c => kindOf t c == some k) = [] := by
  refine List.eq_nil_of_length_eq_zero ?_
  rw [← length_filter_map (kindOf t) (· == some k)]
  exact h

/--
clone した copy を append するときの pre-insert validity。

`AppendableInto` が持っている「繋いだ kind 列」から、Document の children の
制約（step 9 と step 11）が出る。
-/
theorem cloneAppend_validity {t₀ t : Tree} {p n copy : NodeId} {rest : List NodeId}
    {d cd : NodeData}
    (hwf : WellFormed t) (h : AppendableInto t₀ t (n :: rest) p)
    (ht0n : t₀.get? n = some d)
    (hcd : t.get? copy = some cd) (hck : cd.kind = d.kind)
    (hcp : cd.parent = none) (hcch : cd.children = []) (hcnep : copy ≠ p)
    (hnk : d.kind ≠ NodeKind.document) (hnf : d.kind ≠ NodeKind.documentFragment) :
    ensurePreInsertionValidity t copy p none [] = .ok () := by
  obtain ⟨pd, hpd⟩ := h.present
  have hanc : isInclusiveAncestorOf t copy p = false := by
    cases hb : isInclusiveAncestorOf t copy p with
    | false => rfl
    | true =>
      exfalso
      rcases (isInclusiveAncestorOf_iff hwf copy p).mp hb with he | ha
      · exact hcnep he
      · exact not_ancestor_of_children_nil hwf hcd hcch p ha
  have hkl : kindsOf t₀ (n :: rest) = some d.kind :: kindsOf t₀ rest := by
    simp [kindsOf, kindOf, ht0n]
  refine ensurePreInsertionValidity_fresh hpd hcd
    (h.canHaveChildren n (List.mem_cons_self ..) pd hpd) hanc
    (by rw [hck]; exact hnk) (by rw [hck]; exact hnf) ?_ ?_ ?_ ?_
  · intro hdt
    exact h.doctype n (List.mem_cons_self ..) d ht0n (by rw [← hck]; exact hdt) pd hpd
  · intro hpdoc
    have hd := h.docKinds pd hpd hpdoc
    refine hd.text (some cd.kind) ?_ cd.kind rfl
    refine List.mem_append_right _ ?_
    rw [hkl, hck]
    exact List.mem_cons_self ..
  · intro hpdoc helem
    have hd := h.docKinds pd hpd hpdoc
    have hx : ((some d.kind : Option NodeKind) == some NodeKind.element) = true := by
      rw [← hck, helem]; simp
    refine filter_kinds_nil (length_filter_left _ _ _ _ hx (by rw [← hkl]; exact hd.element))
  · intro hpdoc hdoctype
    have hd := h.docKinds pd hpd hpdoc
    have hx : ((some d.kind : Option NodeKind) == some NodeKind.documentType) = true := by
      rw [← hck, hdoctype]; simp
    refine ⟨filter_kinds_nil (length_filter_left _ _ _ _ hx (by rw [← hkl]; exact hd.doctype)), ?_⟩
    -- doctype より前に element があってはならない（order）。
    refine filter_kinds_nil ?_
    have hno : (some NodeKind.element) ∉ kindsOf t (childrenOf t p) := by
      intro hmem
      have := hd.order (kindsOf t (childrenOf t p)) (kindsOf t₀ (n :: rest)) rfl hmem
      rw [hkl, ← hck, hdoctype] at this
      exact this (List.mem_cons_self ..)
    have : (kindsOf t (childrenOf t p)).filter (· == some NodeKind.element) = [] := by
      refine List.filter_eq_nil_iff.mpr fun a ha hp' => ?_
      have : a = some NodeKind.element := by simpa using hp'
      exact hno (this ▸ ha)
    rw [this]
    rfl


/-! ## `cloneMany` は落ちない -/

/-- **`cloneMany` は妥当な木の上では必ず成功する。** -/
theorem cloneMany_isOk (fuel : Nat) : ∀ (t₀ : Tree) (s : DOMState) (l : List NodeId)
    (doc : NodeId) (parent : Option NodeId),
    StructurallyValid t₀ → DocumentTreesValid t₀ →
    CloneManyPre t₀ s l doc parent →
    (∀ p, parent = some p → AppendableInto t₀ s.tree l p) →
    forestSize t₀ fuel l < fuel →
    ∃ kids s', cloneMany fuel s l doc parent = .ok (kids, s') := by
  induction fuel with
  | zero =>
    intro t₀ s l doc parent hsv0 hdt0 hpre happ hf
    cases l with
    | nil => exact ⟨[], s, rfl⟩
    | cons n rest => exact absurd hf (by omega)
  | succ fuel ih =>
    intro t₀ s l doc parent hsv0 hdt0 hpre happ hf
    cases l with
    | nil => exact ⟨[], s, rfl⟩
    | cons n rest =>
      -- source の data。原本は動いていないので `t₀` でも `s` でも同じである。
      obtain ⟨d, ht0n⟩ : ∃ d, t₀.get? n = some d := by
        cases hx : t₀.get? n with
        | none => exact absurd hx (hpre.srcIn n (List.mem_cons_self ..))
        | some d => exact ⟨d, rfl⟩
      have hd : s.tree.get? n = some d := hpre.sub n d ht0n
      -- step 2
      have hA : AddsNode s.tree (cloneSingle s d doc).2.tree (cloneSingle s d doc).1
          (cloneData d (cloneDocumentOf d doc (freshId s.tree)) (stateMaxAttrId s + 1)) := withFresh_addsNode s _
      have hv₁ : AdmissibleDOMState (cloneSingle s d doc).2 :=
        admissible_createsNode hpre.admissible
          (createsNode_withFresh (freshNodeData_cloneData hpre.admissible hd hpre.isDoc))
      have hdoc₁ : IsDocument (cloneSingle s d doc).2.tree doc := by
        obtain ⟨dd, hdd, hk⟩ := hpre.isDoc
        exact ⟨dd, hA.get?_of hdd, hk⟩
      have hcopyFresh : s.tree.get? (cloneSingle s d doc).1 = none := hA.fresh
      -- step 4。append する場合は pre-insert validity が通る。
      have hstep : ∃ s₂,
          cloneAppend (cloneSingle s d doc).2 (cloneSingle s d doc).1 parent = .ok s₂ ∧
          (∀ m md, s.tree.get? m = some md →
            (∀ p, parent = some p → m ≠ p) → s₂.tree.get? m = some md) ∧
          (∃ cd₂, s₂.tree.get? (cloneSingle s d doc).1 = some cd₂ ∧ cd₂.kind = d.kind ∧
            cd₂.children = []) ∧
          (∀ p, parent = some p → ∀ pd, s.tree.get? p = some pd →
            ∃ pd', s₂.tree.get? p = some pd' ∧
              pd'.children = pd.children ++ [(cloneSingle s d doc).1] ∧
              pd'.kind = pd.kind) := by
        cases hpar : parent with
        | none =>
          refine ⟨(cloneSingle s d doc).2, by simp [cloneAppend, hpar],
            fun m md hm _ => hA.get?_of hm, ⟨_, hA.created, rfl, rfl⟩, ?_⟩
          intro p hp; simp at hp
        | some p =>
          have hA' := happ p hpar
          have hA₁ : AppendableInto t₀ (cloneSingle s d doc).2.tree (n :: rest) p :=
            hA'.mono hpre.admissible.wellFormed (fun m md hm => hA.get?_of hm)
          have hcnep : (cloneSingle s d doc).1 ≠ p := by
            intro he
            obtain ⟨pd, hpd⟩ := hA'.present
            rw [← he, hcopyFresh] at hpd
            simp at hpd
          obtain ⟨hnkd, hnfd⟩ := hA'.kinds n (List.mem_cons_self ..) d ht0n
          have hvalid := cloneAppend_validity hv₁.wellFormed hA₁ ht0n hA.created rfl rfl rfl
            hcnep hnkd hnfd
          obtain ⟨s₂, h2⟩ :=
            append_fresh_isOk hv₁.wellFormed hA.created rfl rfl hnfd hvalid
          obtain ⟨hfr, hnode, hpp, -⟩ :=
            append_fresh hv₁.wellFormed hA.created rfl rfl hnfd h2
          refine ⟨s₂, by simp [cloneAppend, hpar, h2], ?_, ?_, ?_⟩
          · intro m md hm hmp
            exact hfr m md (hA.get?_of hm) (hA.ne_of_mem hm) (hmp p rfl)
          · obtain ⟨nd', hnd', hsh, -, hch'⟩ := hnode
            exact ⟨nd', hnd', by simpa using congrArg NodeData.kind hsh, hch'⟩
          · intro q hq pd hpd
            cases Option.some.inj hq
            obtain ⟨pd', hpd', hchp, hshp, -⟩ := hpp pd (hA.get?_of hpd)
            exact ⟨pd', hpd', hchp, by simpa using congrArg NodeData.kind hshp⟩
      obtain ⟨s₂, happ2, hkeep₂, hcopy₂, hparent₂⟩ := hstep
      obtain ⟨cd₂, hcd₂, hck₂, hcch₂⟩ := hcopy₂
      have hv₂ : AdmissibleDOMState s₂ := (admissible_cloneAppend hv₁ happ2).1
      have hdoc₂ : IsDocument s₂.tree doc := hdoc₁.map (admissible_cloneAppend hv₁ happ2).2
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
      -- source の children は原本にあり、Document でも fragment でもない。
      have hchildData : ∀ c ∈ d.children, ∃ cdd, t₀.get? c = some cdd ∧ cdd.parent = some n := by
        intro c hc
        obtain ⟨cdd, hcdd, hcp⟩ := hsv0.wellFormed.parent_child n d ht0n c hc
        exact ⟨cdd, hcdd, hcp⟩
      -- step 5。children の clone。
      have hpre₁ : CloneManyPre t₀ s₂ d.children doc (some (cloneSingle s d doc).1) := by
        refine ⟨hpre.wf0, hv₂, hdoc₂, hsub₂, ?_, ?_, ?_⟩
        · intro p hp
          cases Option.some.inj hp
          exact ⟨ht0copy, by rw [hcd₂]; simp⟩
        · intro x hx
          obtain ⟨cdd, hcdd, -⟩ := hchildData x hx
          rw [hcdd]; simp
        · intro q _ x hx xd hxd hk
          obtain ⟨cdd, hcdd, hcp⟩ := hchildData x hx
          rw [hcdd] at hxd
          cases hxd
          rw [hsv0.fragmentHasNoParent x xd hcdd hk] at hcp
          simp at hcp
      have happ₁ : ∀ p, some (cloneSingle s d doc).1 = some p →
          AppendableInto t₀ s₂.tree d.children p := by
        intro p hp
        cases Option.some.inj hp
        refine ⟨⟨cd₂, hcd₂⟩, ?_, ?_, ?_, ?_⟩
        · intro c hc pd hpd
          rw [hcd₂] at hpd
          cases hpd
          rw [hck₂]
          refine hsv0.childrenOnlyUnderContainers n d ht0n ?_
          intro he; rw [he] at hc; simp at hc
        · intro c hc cdd hcdd
          obtain ⟨cdd', hcdd', hcp⟩ := hchildData c hc
          rw [hcdd'] at hcdd
          cases hcdd
          constructor
          · intro hk; rw [hsv0.documentHasNoParent c cdd hcdd' hk] at hcp; simp at hcp
          · intro hk; rw [hsv0.fragmentHasNoParent c cdd hcdd' hk] at hcp; simp at hcp
        · intro c hc cdd hcdd hk pd hpd
          obtain ⟨cdd', hcdd', hcp⟩ := hchildData c hc
          rw [hcdd'] at hcdd
          cases hcdd
          rw [hcd₂] at hpd
          cases hpd
          rw [hck₂]
          exact hsv0.doctypeParentIsDocument c cdd hcdd' hk n hcp d ht0n
        · intro pd hpd hdocp
          rw [hcd₂] at hpd
          cases hpd
          rw [childrenOf_eq hcd₂, hcch₂]
          simp only [kindsOf, List.map_nil, List.nil_append]
          have hdk : d.kind = NodeKind.document := by rw [← hck₂]; exact hdocp
          have := hdt0.documentChildren n d ht0n hdk
          have hce : childrenOf t₀ n = d.children := childrenOf_eq ht0n
          rw [← hce]
          exact docKindsOk_of_documentChildrenOk this
      have hf₁ : forestSize t₀ fuel d.children < fuel := by
        rw [forestSize_cons, length_preorderFuel_succ ht0n, childrenOf_eq ht0n] at hf
        omega
      obtain ⟨kids₀, s₃, hkids⟩ :=
        ih t₀ s₂ d.children doc (some (cloneSingle s d doc).1) hsv0 hdt0 hpre₁ happ₁ hf₁
      have hspec₁ := cloneMany_spec fuel t₀ s₂ d.children doc (some (cloneSingle s d doc).1)
        kids₀ s₃ hpre₁ hkids
      obtain ⟨hv₃, hdoc₃⟩ :=
        admissible_cloneMany fuel s₂ d.children doc _ kids₀ s₃ hv₂ hdoc₂ hkids
      have hkeep₃ : ∀ m md, s₂.tree.get? m = some md → m ≠ (cloneSingle s d doc).1 →
          s₃.tree.get? m = some md := by
        intro m md hm hmc
        exact hspec₁.keep m md hm (by intro q hq; cases Option.some.inj hq; exact hmc)
      have hsub₃ : ∀ m md, t₀.get? m = some md → s₃.tree.get? m = some md := by
        intro m md hm
        refine hkeep₃ m md (hsub₂ m md hm) ?_
        intro he; rw [he, ht0copy] at hm; simp at hm
      have hpre₂ : CloneManyPre t₀ s₃ rest doc parent := by
        refine ⟨hpre.wf0, hv₃, hdoc₃, hsub₃, ?_, ?_, ?_⟩
        · intro p hp
          refine ⟨(hpre.parentNew p hp).1, ?_⟩
          cases hx : s.tree.get? p with
          | none => exact absurd hx (hpre.parentNew p hp).2
          | some pd =>
            obtain ⟨pd', hpd', -⟩ := hparent₂ p hp pd hx
            have hpc : p ≠ (cloneSingle s d doc).1 := by
              intro he; rw [he, hcopyFresh] at hx; simp at hx
            rw [hkeep₃ p pd' hpd' hpc]; simp
        · intro x hx; exact hpre.srcIn x (List.mem_cons_of_mem _ hx)
        · intro p hp x hx xd hxd
          exact hpre.notFragment p hp x (List.mem_cons_of_mem _ hx) xd hxd
      -- append 先の children は、s から s₃ まで（copy が一つ増える以外）動かない。
      have hchildKeep : ∀ p, parent = some p → ∀ pd, s.tree.get? p = some pd →
          ∀ c ∈ pd.children, kindOf s₃.tree c = kindOf s.tree c := by
        intro p hp pd hpd c hc
        obtain ⟨cdd, hcdd, hcp⟩ := hpre.admissible.wellFormed.parent_child p pd hpd c hc
        have hcnep : c ≠ p := by
          intro he
          have hpar : parentOf s.tree c = some p := by simp [parentOf, hcdd, hcp]
          rw [← he] at hpar
          exact hpre.admissible.wellFormed.acyclic c (Ancestor.step hpar)
        have hcnc : c ≠ (cloneSingle s d doc).1 := hA.ne_of_mem hcdd
        have h2 := hkeep₂ c cdd hcdd (by intro q hq; cases hq.symm ▸ hp; exact hcnep)
        rw [kindOf, kindOf, hkeep₃ c cdd h2 hcnc, hcdd]
      have hcopyKind : kindOf s₃.tree (cloneSingle s d doc).1 = some d.kind := by
        obtain ⟨cd₃, hcd₃, -, hsh₃, -, -⟩ := hspec₁.parentGrows _ cd₂ rfl hcd₂
        rw [kindOf, hcd₃]
        simp only [Option.map_some, Option.some.injEq]
        rw [← hck₂]
        simpa using congrArg NodeData.kind hsh₃
      have happ₂ : ∀ p, parent = some p → AppendableInto t₀ s₃.tree rest p := by
        intro p hp
        have hA' := happ p hp
        obtain ⟨pd, hpd⟩ := hA'.present
        have hpc : p ≠ (cloneSingle s d doc).1 := by
          intro he; rw [he, hcopyFresh] at hpd; simp at hpd
        obtain ⟨pd', hpd'₂, hchp, hkp⟩ := hparent₂ p hp pd hpd
        have hpd'₃ : s₃.tree.get? p = some pd' := hkeep₃ p pd' hpd'₂ hpc
        refine ⟨⟨pd', hpd'₃⟩, ?_, ?_, ?_, ?_⟩
        · intro c hc q hq
          rw [hpd'₃] at hq; cases hq
          rw [hkp]
          exact hA'.canHaveChildren n (List.mem_cons_self ..) pd hpd
        · intro c hc cdd hcdd
          exact hA'.kinds c (List.mem_cons_of_mem _ hc) cdd hcdd
        · intro c hc cdd hcdd hk q hq
          rw [hpd'₃] at hq; cases hq
          rw [hkp]
          exact hA'.doctype c (List.mem_cons_of_mem _ hc) cdd hcdd hk pd hpd
        · intro q hq hdocq
          rw [hpd'₃] at hq; cases hq
          have hlist : kindsOf s₃.tree (childrenOf s₃.tree p) ++ kindsOf t₀ rest =
              kindsOf s.tree (childrenOf s.tree p) ++ kindsOf t₀ (n :: rest) := by
            rw [childrenOf_eq hpd'₃, hchp, childrenOf_eq hpd]
            have hmap : kindsOf s₃.tree pd.children = kindsOf s.tree pd.children :=
              List.map_congr_left fun c hc => hchildKeep p hp pd hpd c hc
            simp only [kindsOf, List.map_append, List.map_cons, List.map_nil] at hmap ⊢
            rw [hmap, hcopyKind]
            simp [kindOf, ht0n]
          rw [hlist]
          exact hA'.docKinds pd hpd (by rw [← hkp]; exact hdocq)
      have hf₂ : forestSize t₀ fuel rest < fuel := by
        have hmono := forestSize_mono t₀ fuel rest
        rw [forestSize_cons, length_preorderFuel_succ ht0n, childrenOf_eq ht0n] at hf
        omega
      obtain ⟨siblings, s₄, hsib⟩ := ih t₀ s₃ rest doc parent hsv0 hdt0 hpre₂ happ₂ hf₂
      exact ⟨(cloneSingle s d doc).1 :: siblings, s₄, by
        simp only [cloneMany, hd, happ2, hkids, hsib]⟩


/-! ## `cloneNode` は落ちない -/

/-- **clone は妥当な木の上では必ず成功する。** -/
theorem cloneNodeIn_isOk {s : DOMState} {n doc : NodeId} {subtree : Bool} {d : NodeData}
    (hv : AdmissibleDOMState s) (hdoc : IsDocument s.tree doc)
    (hd : s.tree.get? n = some d) :
    ∃ c s', cloneNodeIn s n doc subtree = .ok (c, s') := by
  have hpre : CloneManyPre s.tree s [n] doc none := by
    refine ⟨hv.wellFormed, hv, hdoc, fun _ _ hm => hm, by simp, ?_, by simp⟩
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    rw [hd]; simp
  have hf : forestSize s.tree (s.tree.size + 1) [n] < s.tree.size + 1 := by
    rw [forestSize_cons, forestSize_nil]
    have := length_preorderFuel_le_size hv.wellFormed (s.tree.size + 1) n
    omega
  obtain ⟨kids, s', hcm⟩ := cloneMany_isOk (s.tree.size + 1) s.tree s [n] doc none
    hv.structural hv.documentTrees hpre (by simp) hf
  have hkids : kids ≠ [] := by
    intro he
    have hspec := cloneMany_spec (s.tree.size + 1) s.tree s [n] doc none kids s' hpre hcm
    rw [he] at hspec
    simpa using hspec.len
  simp only [cloneNodeIn, hd]
  cases subtree with
  | false =>
    exact ⟨(cloneSingle s d doc).1, (cloneSingle s d doc).2, by simp⟩
  | true =>
    cases kids with
    | nil => exact absurd rfl hkids
    | cons c rest => exact ⟨c, s', by simp [hcm]⟩

/-- **`cloneNode` は妥当な木の上では必ず成功する。** -/
theorem cloneNode_isOk {s : DOMState} {n : NodeId} {deep : Bool} {d : NodeData}
    (hv : AdmissibleDOMState s) (hd : s.tree.get? n = some d) :
    ∃ c s', cloneNode s n deep = .ok (c, s') := by
  rw [cloneNode_eq hd]
  exact cloneNodeIn_isOk hv (isDocument_of_get? hv hd) hd

/-- **`importNode` は、Document でない node なら必ず成功する。** -/
theorem importNode_isOk {s : DOMState} {doc n : NodeId} {subtree : Bool} {dd d : NodeData}
    (hv : AdmissibleDOMState s) (hdd : s.tree.get? doc = some dd)
    (hdk : dd.kind = NodeKind.document) (hd : s.tree.get? n = some d)
    (hnk : d.kind ≠ NodeKind.document) :
    ∃ c s', importNode s doc n subtree = .ok (c, s') := by
  unfold importNode requireDocument
  rw [hdd]
  simp only [hdk, beq_self_eq_true, if_pos, hd]
  rw [if_neg (by simpa using hnk)]
  exact cloneNodeIn_isOk hv ⟨dd, hdd, hdk⟩ hd

/-! ## `adoptNode` は失敗しない

`cloneNode` と同じことを `adoptNode` についても言う。落ちうる場所は四つある。

| step | 失敗 | 妥当な木で起きない理由 |
| --- | --- | --- |
| `requireDocument` | `TypeError` | 受け手が Document であることを仮定する |
| `get? n` | `NotFoundError` | node が木にあることを仮定する |
| step 1 | `NotSupportedError` | node が Document でないことを仮定する |
| step 2 の `remove` | `NotFoundError` | parent がある node にしか呼ばない |

step 1 の `ownerDocumentOf` は `get?` の像なので、node が木にあれば必ず `some` である。
-/

/-- **`adopt` は木にある node に対して必ず成功する。** -/
theorem adopt_isOk {s : DOMState} (hwf : WellFormed s.tree) {node doc : NodeId} {nd : NodeData}
    (hnd : s.tree.get? node = some nd) : ∃ s₁, adopt s node doc = .ok s₁ := by
  have hown : ownerDocumentOf s.tree node = some nd.ownerDocument := by
    simp [ownerDocumentOf, hnd]
  unfold adopt
  rw [hown]
  cases hp : parentOf s.tree node with
  | none =>
    simp only []
    by_cases hd : doc = nd.ownerDocument
    · exact ⟨s, by simp [hd]⟩
    · exact ⟨s.withTree (setOwnerDocument s.tree node doc), by simp [hd]⟩
  | some p =>
    obtain ⟨s₁, h₁⟩ := (remove_succeeds_iff hwf (n := node) (b := false)).mpr (by rw [hp]; rfl)
    simp only [h₁]
    by_cases hd : doc = nd.ownerDocument
    · exact ⟨s₁, by simp [hd]⟩
    · exact ⟨s₁.withTree (setOwnerDocument s₁.tree node doc), by simp [hd]⟩

/-- **`adoptNode` は、Document でない node なら必ず成功する。** -/
theorem adoptNode_isOk {s : DOMState} {doc n : NodeId} {dd d : NodeData}
    (hv : AdmissibleDOMState s) (hdd : s.tree.get? doc = some dd)
    (hdk : dd.kind = NodeKind.document) (hd : s.tree.get? n = some d)
    (hnk : d.kind ≠ NodeKind.document) :
    ∃ s', adoptNode s doc n = .ok (n, s') := by
  unfold adoptNode requireDocument
  rw [hdd]
  simp only [hdk, beq_self_eq_true, if_pos, hd]
  rw [if_neg (by simpa using hnk)]
  obtain ⟨s₁, h₁⟩ := adopt_isOk hv.wellFormed hd (doc := doc)
  exact ⟨s₁, by rw [h₁]⟩

end Dom
