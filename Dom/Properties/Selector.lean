import Dom.Selector.Api
import Dom.Properties.Tree
import Dom.Properties.Path

/-!
# selector の API が満たすこと（契約）

`Dom/Selector/Api.lean` の四つの method について、差分テストで見ているのと
同じことを定理として書く。

仕様本文から独立に書き写した**関係意味論**のほうは `Dom/Spec/Selector.lean` にある。
こちらは実行関数についての定理（契約）で、あちらは翻訳を誤っていないかを見るものである。

* `querySelector()` は `querySelectorAll()` の先頭である
* `querySelectorAll()` は **tree order の部分列**で、**重複を持たない**
* そこに入るのはちょうど「scoping root の descendant である element で、
  selector に当たるもの」である
* `closest()` が返すのは inclusive ancestor である element で、
  **それより近いものは当たらない**
-/

namespace Dom

open Selectors

variable {t : Tree}

/-! ## `querySelector` と `querySelectorAll` -/

/-- **`querySelector()` は `querySelectorAll()` の先頭である。** -/
theorem querySelector_eq_head (t : Tree) (selectors : String) (node : NodeId) :
    querySelector t selectors node = (querySelectorAll t selectors node).map List.head? := by
  unfold querySelector querySelectorAll
  cases requireParentNode t node with
  | error e => rfl
  | ok _ =>
    cases scopeMatch t selectors node with
    | error e => rfl
    | ok l => rfl

/-- `querySelectorAll()` は parse に成功したら `matchTree` そのものである。 -/
theorem querySelectorAll_eq_matchTree {selectors : String} {node : NodeId} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hr : requireParentNode t node = .ok ()) :
    querySelectorAll t selectors node = .ok (matchTree t sel node) := by
  unfold querySelectorAll scopeMatch
  rw [hr, hp]

/-! ## `match a selector against a tree` -/

/--
**結果は候補列の部分列である。**

候補は `preorder` そのものなので、結果は tree order に並ぶ。
-/
theorem matchTree_sublist (t : Tree) (sel : SelectorList) (node : NodeId) :
    (matchTree t sel node).Sublist (preorder t node) :=
  List.Sublist.trans List.filter_sublist List.filter_sublist

/-- **結果は重複を持たない。** -/
theorem matchTree_nodup (hwf : WellFormed t) (sel : SelectorList) (node : NodeId) :
    (matchTree t sel node).Nodup :=
  (matchTree_sublist t sel node).nodup (preorder_nodup hwf node)

/--
**結果に入るのはちょうど、scoping root の descendant である element で
selector に当たるものである。**
-/
theorem mem_matchTree_iff (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) (sel : SelectorList) (e : NodeId) :
    e ∈ matchTree t sel node ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        matchSelList { tree := t, scope := some node } sel e = true := by
  simp only [matchTree, List.mem_filter, mem_preorder_iff hwf hn, Bool.and_eq_true, bne_iff_ne,
    ne_eq, and_assoc]
  constructor
  · rintro ⟨hin, hne, hel, hm⟩
    refine ⟨?_, hel, hm⟩
    rcases hin with heq | hanc
    · exact absurd heq.symm hne
    · exact hanc
  · rintro ⟨hanc, hel, hm⟩
    refine ⟨Or.inr hanc, fun heq => ?_, hel, hm⟩
    rw [heq] at hanc
    exact absurd hanc (ancestor_irrefl hwf _)

/-- 結果に入るのは element だけである。 -/
theorem isElement_of_mem_matchTree {sel : SelectorList} {node e : NodeId}
    (h : e ∈ matchTree t sel node) : isElementNode t e = true := by
  simp only [matchTree, List.mem_filter, Bool.and_eq_true] at h
  exact h.1.2.2

/-! ## `closest` -/

theorem mem_inclusiveAncestorElements_iff (hwf : WellFormed t) (n f : NodeId) :
    f ∈ inclusiveAncestorElements t n ↔ InclusiveAncestor t f n ∧ isElementNode t f = true := by
  simp only [inclusiveAncestorElements, List.mem_filter, mem_inclusiveAncestors_iff hwf]

/-- 受け手が Element で selector を読めたなら、`closest()` は列の探索そのものである。 -/
theorem closest_eq {selectors : String} {element : NodeId} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hr : requireElementNode t element = .ok ()) :
    closest t selectors element =
      .ok ((inclusiveAncestorElements t element).find?
        (fun e => matchSelList { tree := t, scope := some element } sel e)) := by
  unfold closest
  rw [hr, hp]

/-- **`closest()` が返すのは inclusive ancestor である element で、selector に当たる。** -/
theorem closest_spec (hwf : WellFormed t) {selectors : String} {element e : NodeId}
    {sel : SelectorList} (hp : parseSelector selectors = some sel)
    (hr : requireElementNode t element = .ok ())
    (h : closest t selectors element = .ok (some e)) :
    InclusiveAncestor t e element ∧ isElementNode t e = true ∧
      matchSelList { tree := t, scope := some element } sel e = true := by
  rw [closest_eq hp hr] at h
  simp only [Except.ok.injEq] at h
  have hmem := List.mem_of_find?_eq_some h
  obtain ⟨hmatch, _⟩ := List.find?_eq_some_iff_append.mp h
  obtain ⟨hanc, hel⟩ := (mem_inclusiveAncestorElements_iff hwf element e).mp hmem
  exact ⟨hanc, hel, hmatch⟩

/-- **より近いものは当たらない。** `closest()` が列の先頭から探すことの言い換え。 -/
theorem closest_first {selectors : String} {element e : NodeId} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hr : requireElementNode t element = .ok ())
    (h : closest t selectors element = .ok (some e)) :
    ∃ nearer farther, inclusiveAncestorElements t element = nearer ++ e :: farther ∧
      ∀ f ∈ nearer, matchSelList { tree := t, scope := some element } sel f = false := by
  rw [closest_eq hp hr] at h
  simp only [Except.ok.injEq] at h
  obtain ⟨_, nearer, farther, hsplit, hno⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨nearer, farther, hsplit, fun f hf => by simpa using hno f hf⟩

/-- **当たるものが一つも無いときだけ null を返す。** -/
theorem closest_eq_none_iff (hwf : WellFormed t) {selectors : String} {element : NodeId}
    {sel : SelectorList} (hp : parseSelector selectors = some sel)
    (hr : requireElementNode t element = .ok ()) :
    closest t selectors element = .ok none ↔
      ∀ f, InclusiveAncestor t f element → isElementNode t f = true →
        matchSelList { tree := t, scope := some element } sel f = false := by
  rw [closest_eq hp hr]
  simp only [Except.ok.injEq]
  constructor
  · intro h f hanc hel
    have := List.find?_eq_none.mp h f
      ((mem_inclusiveAncestorElements_iff hwf element f).mpr ⟨hanc, hel⟩)
    simpa using this
  · intro h
    refine List.find?_eq_none.mpr fun x hx => ?_
    obtain ⟨hanc, hel⟩ := (mem_inclusiveAncestorElements_iff hwf element x).mp hx
    simp [h x hanc hel]

/-- **自分が当たるなら `closest()` は自分を返す。** -/
theorem closest_self {selectors : String} {element : NodeId} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hr : requireElementNode t element = .ok ())
    (hel : isElementNode t element = true)
    (hm : matchSelList { tree := t, scope := some element } sel element = true) :
    closest t selectors element = .ok (some element) := by
  rw [closest_eq hp hr]
  simp only [inclusiveAncestorElements, List.filter_cons, hel, if_pos, List.find?_cons, hm]

/-! ## scoping root が見えるのは `:scope` からだけ -/

/--
**`:scope` を含まない selector の照合は scoping root に依らない。**

`matchSimple` が `ctx.scope` を読むのは `Simple.scope` の枝だけなので、
そこを塞げば scoping root は観測できない。

四つの相互再帰をまとめて、selector の大きさ `k` についての強い帰納法で示す。
`:has()` は anchor を書き換えるので、帰納法の仮定は anchor について全称にしてある。
-/
theorem scope_irrelevant (t : Tree) (s₁ s₂ : Option NodeId) : ∀ (k : Nat),
    (∀ (a : Option NodeId) (l : List Complex) (n : NodeId), lSize l ≤ k → scopeFreeL l = true →
        matchSelList ⟨t, s₁, a⟩ l n = matchSelList ⟨t, s₂, a⟩ l n) ∧
    (∀ (a : Option NodeId) (c : Complex) (n : NodeId), cxSize c ≤ k → scopeFreeCx c = true →
        matchComplex ⟨t, s₁, a⟩ c n = matchComplex ⟨t, s₂, a⟩ c n) ∧
    (∀ (a : Option NodeId) (p : List Simple) (n : NodeId), cpSize p ≤ k → scopeFreeCp p = true →
        matchCompound ⟨t, s₁, a⟩ p n = matchCompound ⟨t, s₂, a⟩ p n) ∧
    (∀ (a : Option NodeId) (s : Simple) (n : NodeId), sSize s ≤ k → scopeFreeS s = true →
        matchSimple ⟨t, s₁, a⟩ s n = matchSimple ⟨t, s₂, a⟩ s n) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun a l n hk _ => ?_, fun a c n hk _ => ?_, fun a p n hk _ => ?_,
      fun a s n hk _ => ?_⟩
    · exact absurd hk (by have := lSize_pos l; omega)
    · exact absurd hk (by have := cxSize_pos c; omega)
    · exact absurd hk (by have := cpSize_pos p; omega)
    · exact absurd hk (by have := sSize_pos s; omega)
  | succ k ih =>
    refine ⟨fun a l n hk hf => ?_, fun a c n hk hf => ?_, fun a p n hk hf => ?_,
      fun a s n hk hf => ?_⟩
    · rw [matchSelList, matchSelList]
      refine List.any_congr rfl fun c => ?_
      exact ih.2.1 a c.1 n (by have := cxSize_lt_lSize l c.1 c.2; omega)
        (scopeFreeCx_of_mem l c.1 c.2 hf)
    · cases c with
      | one parts =>
        rw [matchComplex, matchComplex]
        exact ih.2.2.1 a parts n (by rw [cxSize] at hk; omega) (by rwa [scopeFreeCx] at hf)
      | seq parts comb left =>
        rw [scopeFreeCx, Bool.and_eq_true] at hf
        rw [cxSize] at hk
        rw [matchComplex, matchComplex]
        rw [ih.2.2.1 a parts n (by omega) hf.1]
        refine congrArg _ (List.any_congr rfl fun m => ?_)
        exact ih.2.1 a left m (by omega) hf.2
    · rw [matchCompound, matchCompound]
      refine List.all_congr rfl fun x => ?_
      exact ih.2.2.2 a x.1 n (by have := sSize_lt_cpSize p x.1 x.2; omega)
        (scopeFreeS_of_mem p x.1 x.2 hf)
    · rw [matchSimple, matchSimple]
      cases hg : t.get? n with
      | none => rfl
      | some d =>
        by_cases he : (d.kind != NodeKind.element) = true
        · simp only [he, if_pos, isScopeSelector_eq_false hf, Bool.false_and]
        · simp only [he, Bool.false_eq_true, if_false]
          cases s with
          | scope => simp [scopeFreeS] at hf
          | isSel l =>
            dsimp only
            exact ih.1 a l n (by rw [sSize] at hk; omega) (by rwa [scopeFreeS] at hf)
          | whereSel l =>
            dsimp only
            exact ih.1 a l n (by rw [sSize] at hk; omega) (by rwa [scopeFreeS] at hf)
          | notSel l =>
            dsimp only
            rw [ih.1 a l n (by rw [sSize] at hk; omega) (by rwa [scopeFreeS] at hf)]
          | has l =>
            dsimp only
            refine List.any_congr rfl fun c => ?_
            exact ih.1 (some n) l c (by rw [sSize] at hk; omega) (by rwa [scopeFreeS] at hf)
          | nth kind ab ofSel =>
            cases ofSel with
            | none => dsimp only
            | some l =>
              dsimp only
              have hl : (fun m => matchSelList (MatchCtx.mk t s₁ a) l m)
                  = (fun m => matchSelList (MatchCtx.mk t s₂ a) l m) :=
                funext fun m => ih.1 a l m (by rw [sSize, oSize] at hk; omega)
                  (by rw [scopeFreeS, scopeFreeO] at hf; exact hf)
              cases kind <;> simp only [hl]
          | _ => rfl

/-- `:scope` を含まなければ、どの scoping root で照合しても同じである。 -/
theorem matchSelList_scope_irrelevant {t : Tree} {s₁ s₂ : Option NodeId} {a : Option NodeId}
    {l : List Complex} {n : NodeId} (hf : scopeFreeL l = true) :
    matchSelList ⟨t, s₁, a⟩ l n = matchSelList ⟨t, s₂, a⟩ l n :=
  (scope_irrelevant t s₁ s₂ (lSize l)).1 a l n (Nat.le_refl _) hf

/-! ## `matches()` と `querySelectorAll()` の整合 -/

theorem requireElementNode_ok_iff (t : Tree) (e : NodeId) :
    requireElementNode t e = .ok () ↔ isElementNode t e = true := by
  unfold requireElementNode isElementNode kindOf
  cases t.get? e with
  | none => simp
  | some d => by_cases h : d.kind == NodeKind.element <;> simp_all

/-- 受け手が Element で selector を読めたなら、`matches()` は照合そのものである。 -/
theorem matchesSelector_eq {t : Tree} {selectors : String} {e : NodeId} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hr : requireElementNode t e = .ok ()) :
    matchesSelector t selectors e = .ok (matchSelList ⟨t, some e, none⟩ sel e) := by
  unfold matchesSelector
  rw [hr, hp]

/--
**`:scope` を含まない selector なら、`querySelectorAll()` の結果に入ることと
`matches()` が true を返すことは、候補であることのもとで一致する。**

`:scope` を含むときは一致しない。`querySelectorAll()` の scoping root は受け手だが、
`matches()` の scoping root は element 自身だからである。その違いが観測できるのは
`:scope` を通してだけで、それを言うのが `scope_irrelevant` である。
-/
theorem mem_matchTree_iff_matches (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) {selectors : String} {sel : SelectorList}
    (hp : parseSelector selectors = some sel) (hf : scopeFreeL sel = true) (e : NodeId) :
    e ∈ matchTree t sel node ↔
      Descendant t e node ∧ matchesSelector t selectors e = .ok true := by
  rw [mem_matchTree_iff hwf hn sel e]
  constructor
  · rintro ⟨hd, hel, hm⟩
    refine ⟨hd, ?_⟩
    rw [matchesSelector_eq hp ((requireElementNode_ok_iff t e).mpr hel)]
    rw [matchSelList_scope_irrelevant (s₂ := some node) hf]
    exact congrArg _ hm
  · rintro ⟨hd, hmatch⟩
    by_cases hel : isElementNode t e = true
    · refine ⟨hd, hel, ?_⟩
      rw [matchesSelector_eq hp ((requireElementNode_ok_iff t e).mpr hel)] at hmatch
      have := Except.ok.inj hmatch
      rwa [matchSelList_scope_irrelevant (s₂ := some node) hf] at this
    · exfalso
      have hne : requireElementNode t e ≠ .ok () := fun h =>
        hel ((requireElementNode_ok_iff t e).mp h)
      unfold matchesSelector at hmatch
      cases hr : requireElementNode t e with
      | error err =>
        rw [hr] at hmatch
        exact absurd hmatch (by simp)
      | ok u => exact hne hr

end Dom
