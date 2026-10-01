import Selectors.Spec.ScanStep

/-!
# `scan` は selector の文法に一致する

`Selectors/Spec/Scan.lean` の文法（`SelListRel` / `ItemRel` / `TailRel` / `CompoundRel` /
`SubclassesRel` / `PieceRel`）と、`Selectors/Parser.lean` の状態機械 `scan` が、
同じ selector を同じ構文木に読み、同じものを拒むことを示す（`scan_spec`・`parseSelector_spec`）。

証明は三段である。

1. compound 一つ：`Selectors/Spec/ScanStep.lean` の `scan_compound` / `scan_compound_fail`。
2. 項目一つ：`scan` の状態（`cur` と `pend`、`parts` は空）ごとに、残りが満たすべき文法を
   `Res` として書き、区切り（空白・combinator・終わり）と compound の一歩ごとに
   `scan` と `Res` が同じように進むことを、残りの長さについての帰納法で示す（`item_main`）。
3. selector list：`,` で分けた項目を順に読む（`scan_items`）。forgiving では読めない項目を落とす。

中の selector list（`:is()` などの引数）は component 列の大きさについての帰納法で扱う（`innerOk_all`）。
-/

namespace Selectors.Spec

open Selectors Infra

/-! ## 項目の途中の残り（文法の側） -/

/--
先頭に空白を挟んでよい compound と、その後ろ。`k` 付きの状態（combinator を読んだあと）と、
relative selector の先頭の combinator を読んだあとの残りがこの形である。
-/
def AfterComb (cfg : ScanCfg) (mk : List Simple → Complex) (x : List Component) (c : Complex) :
    Prop :=
  ∃ w r rest ps, x = w ++ r ++ rest ∧ AllWs w ∧ r ≠ [] ∧ CompoundRel cfg r ps ∧
    TailRel cfg (mk ps) rest c

theorem allWs_cons_ws {w : List Component} (h : AllWs w) : AllWs (.tok .whitespace :: w) := by
  intro c hc; rcases List.mem_cons.mp hc with rfl | hc; rfl; exact h c hc

theorem allWs_tail {c : Component} {w : List Component} (h : AllWs (c :: w)) : AllWs w :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem compoundRel_ne_ws {cfg : ScanCfg} {r : List Component} {ps : List Simple}
    (h : CompoundRel cfg r ps) : ∀ rest, r ≠ .tok .whitespace :: rest := by
  intro rest hr
  exact compoundRel_noBoundary h _ (by rw [hr]; simp) ws_isBoundary

theorem compoundRel_ne_comb {cfg : ScanCfg} {r : List Component} {ps : List Simple}
    (h : CompoundRel cfg r ps) {d : Char} {k : Combinator} (hd : CombDelim d k) :
    ∀ rest, r ≠ .tok (.delim d) :: rest := by
  intro rest hr
  exact compoundRel_noBoundary h _ (by rw [hr]; simp) (comb_isBoundary hd)

/-- **空白を一つ前に足しても `AfterComb` は変わらない。** -/
theorem afterComb_ws {cfg : ScanCfg} {mk : List Simple → Complex} {x : List Component} {c : Complex} :
    AfterComb cfg mk (.tok .whitespace :: x) c ↔ AfterComb cfg mk x c := by
  constructor
  · rintro ⟨w, r, rest, ps, hx, hw, hne, hr, ht⟩
    cases w with
    | nil =>
      obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp at hx; exact absurd hx.1.symm (by
        intro h; exact compoundRel_ne_ws hr r0 (by rw [h]))
    | cons c0 w =>
      simp at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨w, r, rest, ps, by simp, allWs_tail hw, hne, hr, ht⟩
  · rintro ⟨w, r, rest, ps, rfl, hw, hne, hr, ht⟩
    exact ⟨.tok .whitespace :: w, r, rest, ps, by simp, allWs_cons_ws hw, hne, hr, ht⟩

/-- `AfterComb` の残りは combinator で始まらない。 -/
theorem afterComb_comb {cfg : ScanCfg} {mk : List Simple → Complex} {x : List Component}
    {c : Complex} {d : Char} {k : Combinator} (hd : CombDelim d k) :
    ¬ AfterComb cfg mk (.tok (.delim d) :: x) c := by
  rintro ⟨w, r, rest, ps, hx, hw, hne, hr, ht⟩
  cases w with
  | nil =>
    obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp at hx; obtain ⟨h1, _⟩ := hx
    exact compoundRel_ne_comb hr hd r0 (by rw [h1])
  | cons c0 w =>
    simp at hx; obtain ⟨rfl, _⟩ := hx
    cases hw _ List.mem_cons_self

theorem afterComb_nil {cfg : ScanCfg} {mk : List Simple → Complex} {c : Complex} :
    ¬ AfterComb cfg mk [] c := by
  rintro ⟨w, r, rest, ps, hx, _, hne, _, _⟩
  have := congrArg List.length hx
  simp at this; have := List.length_pos_iff.mpr hne; omega

/-- **`TailRel` は、空だけの残りなら左側そのものになる。** -/
theorem tailRel_nil {cfg : ScanCfg} {left c : Complex} : TailRel cfg left [] c ↔ c = left := by
  rw [TailRel]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨sep, r, rest, h, hne, _⟩)
    · rfl
    · have := congrArg List.length h; simp at this; have := List.length_pos_iff.mpr hne; omega
  · rintro rfl; exact Or.inl ⟨by simp [AllWs], rfl⟩

theorem sepRel_ws_cons {sep : List Component} {k : Combinator} (h : SepRel sep k) :
    SepRel (.tok .whitespace :: sep) k := by
  rcases h with ⟨_, hws, rfl⟩ | ⟨w1, d, w2, rfl, hw1, hw2, hd⟩
  · exact Or.inl ⟨by simp, allWs_cons_ws hws, rfl⟩
  · exact Or.inr ⟨.tok .whitespace :: w1, d, w2, by simp, allWs_cons_ws hw1, hw2, hd⟩

/-- **空白の後ろに更に空白があっても、`TailRel` は変わらない。** -/
theorem tailRel_ws_ws {cfg : ScanCfg} {left c : Complex} {x : List Component} :
    TailRel cfg left (.tok .whitespace :: .tok .whitespace :: x) c ↔
      TailRel cfg left (.tok .whitespace :: x) c := by
  constructor
  · intro h
    rw [TailRel] at h ⊢
    rcases h with ⟨hws, rfl⟩ | ⟨sep, r, rest, hx, hne, k, ps, hsep, hr, ht⟩
    · exact Or.inl ⟨allWs_tail hws, rfl⟩
    · right
      cases sep with
      | nil => exact absurd hsep (by rintro (⟨h, _⟩ | ⟨w1, d, w2, h, _⟩) <;> simp at h)
      | cons s0 sep' =>
        simp at hx; obtain ⟨rfl, hx⟩ := hx
        cases sep' with
        | nil =>
          obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
          simp at hx; exact absurd hx.1.symm (fun h => compoundRel_ne_ws hr r0 (by rw [h]))
        | cons s1 sep'' =>
          simp at hx; obtain ⟨rfl, hx⟩ := hx
          refine ⟨.tok .whitespace :: sep'', r, rest, by simp [hx], hne, k, ps, ?_, hr, ht⟩
          rcases hsep with ⟨_, hws, rfl⟩ | ⟨w1, d, w2, h, hw1, hw2, hd⟩
          · exact Or.inl ⟨by simp, allWs_tail hws, rfl⟩
          · cases w1 with
            | nil => simp at h
            | cons a w1 =>
              simp at h; obtain ⟨_, h⟩ := h
              exact Or.inr ⟨w1, d, w2, h, allWs_tail hw1, hw2, hd⟩
  · intro h
    rw [TailRel] at h ⊢
    rcases h with ⟨hws, rfl⟩ | ⟨sep, r, rest, hx, hne, k, ps, hsep, hr, ht⟩
    · exact Or.inl ⟨allWs_cons_ws hws, rfl⟩
    · exact Or.inr ⟨.tok .whitespace :: sep, r, rest, by simp [hx], hne, k, ps,
        sepRel_ws_cons hsep, hr, ht⟩

theorem combDelim_unique {d : Char} {k k' : Combinator} (h : CombDelim d k) (h' : CombDelim d k') :
    k = k' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> first | rfl | exact absurd h (by decide)

/-- **空白の後ろに combinator が来たら、そこから先は `AfterComb` である。** -/
theorem tailRel_ws_comb {cfg : ScanCfg} {left c : Complex} {x : List Component} {d : Char}
    {k : Combinator} (hd : CombDelim d k) :
    TailRel cfg left (.tok .whitespace :: .tok (.delim d) :: x) c ↔
      AfterComb cfg (fun ps => .seq ps k left) x c := by
  rw [TailRel]
  constructor
  · rintro (⟨hws, _⟩ | ⟨sep, r, rest, hx, hne, k', ps, hsep, hr, ht⟩)
    · cases hws (.tok (.delim d)) (by simp)
    · rcases hsep with ⟨hsne, hws, _⟩ | ⟨w1, d', w2, rfl, hw1, hw2, hd'⟩
      · -- 空白だけの separator の後ろに compound が来るなら、その compound が combinator で始まる
        exfalso
        obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
        cases sep with
        | nil => exact absurd rfl hsne
        | cons s0 sep' =>
          simp at hx; obtain ⟨_, hx⟩ := hx
          cases sep' with
          | nil => simp at hx; exact compoundRel_ne_comb hr hd r0 (by rw [hx.1])
          | cons s1 sep'' =>
            simp at hx; obtain ⟨rfl, _⟩ := hx
            cases hws (.tok (.delim d)) (by simp)
      · cases w1 with
        | nil => simp at hx
        | cons a w1 =>
          simp at hx; obtain ⟨_, hx⟩ := hx
          cases w1 with
          | nil =>
            simp at hx; obtain ⟨rfl, hx⟩ := hx
            have := combDelim_unique hd hd'; subst this
            exact ⟨w2, r, rest, ps, by simp [hx], hw2, hne, hr, ht⟩
          | cons b w1 =>
            simp at hx; obtain ⟨rfl, _⟩ := hx
            cases hw1 (.tok (.delim d)) (by simp)
  · rintro ⟨w, r, rest, ps, rfl, hw, hne, hr, ht⟩
    exact Or.inr ⟨[.tok .whitespace, .tok (.delim d)] ++ w, r, rest, by simp, hne, k, ps,
      Or.inr ⟨[.tok .whitespace], d, w, by simp, allWs_cons_ws (by simp [AllWs]), hw, hd⟩, hr, ht⟩

/-- **combinator で始まる残りは `AfterComb` である。** -/
theorem tailRel_comb {cfg : ScanCfg} {left c : Complex} {x : List Component} {d : Char}
    {k : Combinator} (hd : CombDelim d k) :
    TailRel cfg left (.tok (.delim d) :: x) c ↔ AfterComb cfg (fun ps => .seq ps k left) x c := by
  rw [TailRel]
  constructor
  · rintro (⟨hws, _⟩ | ⟨sep, r, rest, hx, hne, k', ps, hsep, hr, ht⟩)
    · cases hws (.tok (.delim d)) (by simp)
    · rcases hsep with ⟨hsne, hws, _⟩ | ⟨w1, d', w2, rfl, hw1, hw2, hd'⟩
      · obtain ⟨s0, sep', rfl⟩ := List.exists_cons_of_ne_nil hsne
        simp at hx; obtain ⟨rfl, _⟩ := hx; cases hws _ List.mem_cons_self
      · cases w1 with
        | nil =>
          simp at hx; obtain ⟨rfl, hx⟩ := hx
          have := combDelim_unique hd hd'; subst this
          exact ⟨w2, r, rest, ps, by simp [hx], hw2, hne, hr, ht⟩
        | cons a w1 =>
          simp at hx; obtain ⟨rfl, _⟩ := hx; cases hw1 _ List.mem_cons_self
  · rintro ⟨w, r, rest, ps, rfl, hw, hne, hr, ht⟩
    exact Or.inr ⟨.tok (.delim d) :: w, r, rest, by simp, hne, k, ps,
      Or.inr ⟨[], d, w, by simp, by simp [AllWs], hw, hd⟩, hr, ht⟩

/-- **区切りで始まらない残りは、最長の compound と、その後ろの `TailRel` に分かれる。** -/
theorem afterComb_run {cfg : ScanCfg} {mk : List Simple → Complex} {r y : List Component}
    {c : Complex} (hrnb : NoBoundary r) (hrne : r ≠ []) (hy : BoundaryStart y) :
    AfterComb cfg mk (r ++ y) c ↔ ∃ ps, CompoundRel cfg r ps ∧ TailRel cfg (mk ps) y c := by
  constructor
  · rintro ⟨w, r', rest, ps, hx, hw, hne, hr, ht⟩
    cases w with
    | nil =>
      simp at hx
      obtain ⟨rfl, rfl⟩ := run_split_unique hx hrnb (compoundRel_noBoundary hr) hy
        (tailRel_boundaryStart ht)
      exact ⟨ps, hr, ht⟩
    | cons w0 w =>
      obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hrne
      simp at hx; obtain ⟨rfl, _⟩ := hx
      exact absurd (hw _ List.mem_cons_self ▸ ws_isBoundary) (hrnb _ List.mem_cons_self)
  · rintro ⟨ps, hr, ht⟩
    exact ⟨[], r, y, ps, by simp, by simp [AllWs], hrne, hr, ht⟩

/-- **空白の後ろに compound が来たら、descendant でつなぐ。** -/
theorem tailRel_ws_run {cfg : ScanCfg} {left c : Complex} {r y : List Component}
    (hrnb : NoBoundary r) (hrne : r ≠ []) (hy : BoundaryStart y) :
    TailRel cfg left (.tok .whitespace :: (r ++ y)) c ↔
      ∃ ps, CompoundRel cfg r ps ∧ TailRel cfg (.seq ps .descendant left) y c := by
  obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hrne
  have hc0 : ¬ IsBoundary c0 := hrnb _ List.mem_cons_self
  rw [TailRel]
  constructor
  · rintro (⟨hws, _⟩ | ⟨sep, r', rest, hx, hne, k, ps, hsep, hr, ht⟩)
    · exact absurd (hws c0 (by simp) ▸ ws_isBoundary) hc0
    · rcases hsep with ⟨hsne, hws, rfl⟩ | ⟨w1, d, w2, rfl, hw1, hw2, hd⟩
      · obtain ⟨s0, sep', rfl⟩ := List.exists_cons_of_ne_nil hsne
        simp at hx; obtain ⟨_, hx⟩ := hx
        cases sep' with
        | nil =>
          simp at hx
          have hx' : (c0 :: r0) ++ y = r' ++ rest := by simpa using hx
          obtain ⟨rfl, rfl⟩ := run_split_unique hx' hrnb (compoundRel_noBoundary hr) hy
            (tailRel_boundaryStart ht)
          exact ⟨ps, hr, ht⟩
        | cons s1 sep'' =>
          simp at hx; obtain ⟨rfl, _⟩ := hx
          exact absurd (hws c0 (by simp) ▸ ws_isBoundary) hc0
      · exfalso
        cases w1 with
        | nil => simp at hx
        | cons a w1 =>
          simp at hx; obtain ⟨_, hx⟩ := hx
          cases w1 with
          | nil => simp at hx; exact hc0 (hx.1 ▸ comb_isBoundary hd)
          | cons b w1 =>
            simp at hx; obtain ⟨rfl, _⟩ := hx
            exact hc0 (hw1 c0 (by simp) ▸ ws_isBoundary)
  · rintro ⟨ps, hr, ht⟩
    exact Or.inr ⟨[.tok .whitespace], c0 :: r0, y, by simp, hrne, .descendant, ps,
      Or.inl ⟨by simp, by simp [AllWs, IsWs], rfl⟩, hr, ht⟩

/-! ## `ItemRel` の一歩 -/

theorem itemRel_nil {cfg : ScanCfg} {c : Complex} : ¬ ItemRel cfg [] c := by
  rw [ItemRel]
  rintro ⟨w1, lead, r, rest, h, lk, ps, _, _, hne, _, _⟩
  have := congrArg List.length h; simp at this; have := List.length_pos_iff.mpr hne; omega

theorem itemRel_ws {cfg : ScanCfg} {x : List Component} {c : Complex} :
    ItemRel cfg (.tok .whitespace :: x) c ↔ ItemRel cfg x c := by
  rw [ItemRel, ItemRel]
  constructor
  · rintro ⟨w1, lead, r, rest, hx, lk, ps, hw1, hlead, hne, hr, ht⟩
    cases w1 with
    | nil =>
      exfalso
      rcases hlead with ⟨rfl, _⟩ | ⟨d, k, w, rfl, _, _, _, _⟩
      · obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp at hx; exact compoundRel_ne_ws hr r0 (by rw [← hx.1])
      · simp at hx
    | cons a w1 =>
      simp at hx; obtain ⟨rfl, hx⟩ := hx
      exact ⟨w1, lead, r, rest, by simp [hx], lk, ps, allWs_tail hw1, hlead, hne, hr, ht⟩
  · rintro ⟨w1, lead, r, rest, rfl, lk, ps, hw1, hlead, hne, hr, ht⟩
    exact ⟨.tok .whitespace :: w1, lead, r, rest, by simp, lk, ps, allWs_cons_ws hw1, hlead, hne, hr, ht⟩

theorem itemRel_comb {cfg : ScanCfg} {x : List Component} {c : Complex} {d : Char}
    {k : Combinator} (hd : CombDelim d k) :
    ItemRel cfg (.tok (.delim d) :: x) c ↔
      cfg.relative = true ∧ AfterComb cfg (BaseComplex cfg (some k)) x c := by
  rw [ItemRel]
  constructor
  · rintro ⟨w1, lead, r, rest, hx, lk, ps, hw1, hlead, hne, hr, ht⟩
    cases w1 with
    | nil =>
      rcases hlead with ⟨rfl, _⟩ | ⟨d', k', w, rfl, hw, hd', hrel, rfl⟩
      · obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp at hx; exact absurd hx.1 (fun h => compoundRel_ne_comb hr hd r0 (by rw [← h]))
      · simp at hx; obtain ⟨rfl, hx⟩ := hx
        have := combDelim_unique hd hd'; subst this
        exact ⟨hrel, w, r, rest, ps, by simp [hx], hw, hne, hr, ht⟩
    | cons a w1 =>
      simp at hx; obtain ⟨rfl, _⟩ := hx; cases hw1 _ List.mem_cons_self
  · rintro ⟨hrel, w, r, rest, ps, rfl, hw, hne, hr, ht⟩
    exact ⟨[], .tok (.delim d) :: w, r, rest, by simp, some k, ps, by simp [AllWs],
      Or.inr ⟨d, k, w, rfl, hw, hd, hrel, rfl⟩, hne, hr, ht⟩

theorem itemRel_run {cfg : ScanCfg} {r y : List Component} {c : Complex}
    (hrnb : NoBoundary r) (hrne : r ≠ []) (hy : BoundaryStart y) :
    ItemRel cfg (r ++ y) c ↔ ∃ ps, CompoundRel cfg r ps ∧ TailRel cfg (BaseComplex cfg none ps) y c := by
  obtain ⟨c0, r0, rfl⟩ := List.exists_cons_of_ne_nil hrne
  have hc0 : ¬ IsBoundary c0 := hrnb _ List.mem_cons_self
  rw [ItemRel]
  constructor
  · rintro ⟨w1, lead, r', rest, hx, lk, ps, hw1, hlead, hne, hr, ht⟩
    cases w1 with
    | nil =>
      rcases hlead with ⟨rfl, rfl⟩ | ⟨d, k, w, rfl, _, hd, _, _⟩
      · simp only [List.nil_append] at hx
        have hx' : (c0 :: r0) ++ y = r' ++ rest := by simpa using hx
        obtain ⟨rfl, rfl⟩ := run_split_unique hx' hrnb (compoundRel_noBoundary hr) hy
          (tailRel_boundaryStart ht)
        exact ⟨ps, hr, ht⟩
      · simp at hx; exact absurd (hx.1 ▸ comb_isBoundary hd) hc0
    | cons a w1 =>
      simp at hx; obtain ⟨rfl, _⟩ := hx
      exact absurd (hw1 _ List.mem_cons_self ▸ ws_isBoundary) hc0
  · rintro ⟨ps, hr, ht⟩
    exact ⟨[], [], c0 :: r0, y, by simp, none, ps, by simp [AllWs], Or.inl ⟨rfl, rfl⟩, hrne, hr, ht⟩

/-! ## 区切りでの `scan`（実行側） -/

theorem flush_nil {cfg : ScanCfg} {st : ScanSt} (hp : st.parts = []) : flush cfg st = some st := by
  unfold flush; rw [hp]

theorem scan_ws_nil {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) (z : List Component) :
    scan cfg st (.tok .whitespace :: z) = scan cfg st z := by
  rw [scan.eq_def]; simp only [flush_nil hp]

theorem combDelim_beq {d : Char} {k : Combinator} (hd : CombDelim d k) :
    (d == CH_GT || d == CH_PLUS || d == CH_TILDE) = true ∧
      (if d == CH_GT then Combinator.child else if d == CH_PLUS then Combinator.nextSibling
        else Combinator.subsequentSibling) = k := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem scan_comb {cfg : ScanCfg} (st : ScanSt) {d : Char} {k : Combinator} (hd : CombDelim d k)
    (z : List Component) :
    scan cfg st (.tok (.delim d) :: z) =
      match flush cfg st with
      | some st' =>
        if st'.pend.isSome then
          (if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma z) else none)
        else scan cfg { st' with pend := some k } z
      | none => if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma z) else none := by
  obtain ⟨h1, h2⟩ := combDelim_beq hd
  rw [scan.eq_def]; simp only [h1, if_true, h2]; rfl

theorem scan_end {cfg : ScanCfg} (st : ScanSt) :
    scan cfg st [] =
      match finishComplex cfg st with
      | some st' => some st'.done.reverse
      | none => if cfg.forgiving = true then some st.done.reverse else none := by
  rw [scan.eq_def]; rfl

theorem scan_comma {cfg : ScanCfg} (st : ScanSt) (rest : List Component) :
    scan cfg st (.tok .comma :: rest) =
      match finishComplex cfg st with
      | some st' => scan cfg st' rest
      | none => if cfg.forgiving = true then scan cfg (initSt cfg st.done) rest else none := by
  rw [scan.eq_def]; rfl

/-- compound を閉じたときにできる、新しい左側。 -/
def newCur (cfg : ScanCfg) (cur : Option Complex) (pend : Option Combinator) (ps : List Simple) :
    Option Complex :=
  match cur with
  | none =>
    if cfg.relative then some (.seq ps (pend.getD .descendant) (.one [.anchor]))
    else if pend.isSome then none else some (.one ps)
  | some c => some (.seq ps (pend.getD .descendant) c)

theorem flush_parts {cfg : ScanCfg} (st : ScanSt) {ps : List Simple} (hne : ps ≠ []) :
    flush cfg { st with parts := ps.reverse } =
      (newCur cfg st.cur st.pend ps).map
        (fun L => { st with cur := some L, pend := none, parts := [] }) := by
  unfold flush newCur
  have : ps.reverse ≠ [] := by simpa using hne
  obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil this
  simp only [has]
  rw [← has, List.reverse_reverse]
  cases st.cur with
  | none =>
    cases hr : cfg.relative <;> cases hpend : st.pend <;> simp
  | some c => simp

theorem finishComplex_nil {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) :
    finishComplex cfg st =
      match st.cur, st.pend with
      | some L, none => some (initSt cfg (L :: st.done))
      | _, _ => none := by
  unfold finishComplex
  rw [flush_nil hp]
  simp only
  cases st.cur <;> cases st.pend <;> simp

/-! ## 区切りまでの切り出し -/

def isBoundaryB : Component → Bool
  | .tok .whitespace => true
  | .tok .comma => true
  | .tok (.delim d) => d == '>' || d == '+' || d == '~'
  | _ => false

theorem isBoundaryB_iff (c : Component) : isBoundaryB c = true ↔ IsBoundary c := by
  constructor
  · intro h
    match c, h with
    | .tok .whitespace, _ => exact ws_isBoundary
    | .tok .comma, _ => exact Or.inr (Or.inl rfl)
    | .tok (.delim d), h =>
      simp only [isBoundaryB, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (rfl | rfl) | rfl
      · exact comb_isBoundary (k := .child) (Or.inl ⟨rfl, rfl⟩)
      · exact comb_isBoundary (k := .nextSibling) (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact comb_isBoundary (k := .subsequentSibling) (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rintro (rfl | rfl | ⟨d, k, rfl, hk⟩)
    · rfl
    · rfl
    · simp only [isBoundaryB, Bool.or_eq_true, beq_iff_eq]
      rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

/-- 先頭から、区切りでない component を続く限り取り、残りと組にする。 -/
def runSplit : List Component → List Component × List Component
  | [] => ([], [])
  | c :: x => if isBoundaryB c then ([], c :: x) else ((c :: (runSplit x).1), (runSplit x).2)

theorem runSplit_spec : ∀ x : List Component,
    x = (runSplit x).1 ++ (runSplit x).2 ∧ NoBoundary (runSplit x).1 ∧ BoundaryStart (runSplit x).2
  | [] => ⟨rfl, by simp [runSplit, NoBoundary], by simp [runSplit, BoundaryStart]⟩
  | c :: x => by
    obtain ⟨h1, h2, h3⟩ := runSplit_spec x
    by_cases hc : isBoundaryB c = true
    · simp only [runSplit, hc, if_true]
      refine ⟨rfl, by simp [NoBoundary], ?_⟩
      intro c' hc'; simp at hc'; subst hc'; exact (isBoundaryB_iff _).mp hc
    · simp only [runSplit, hc, Bool.false_eq_true, if_false]
      refine ⟨by simp [← h1], ?_, h3⟩
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [← isBoundaryB_iff]; exact hc
      · exact h2 c' hc'

theorem runSplit_ne_nil {c : Component} {x : List Component} (hc : ¬ IsBoundary c) :
    (runSplit (c :: x)).1 ≠ [] := by
  have : isBoundaryB c = false := by
    cases h : isBoundaryB c; rfl; exact absurd ((isBoundaryB_iff c).mp h) hc
  simp [runSplit, this]

/-! ## 状態ごとの残り -/

/-- `scan` の状態（`parts` が空のとき）に対応する、項目の残りの文法。 -/
def Res (cfg : ScanCfg) : Option Complex → Option Combinator → List Component → Complex → Prop
  | none, none, x, c => ItemRel cfg x c
  | none, some k, x, c => cfg.relative = true ∧ AfterComb cfg (BaseComplex cfg (some k)) x c
  | some L, none, x, c => TailRel cfg L (.tok .whitespace :: x) c
  | some L, some k, x, c => AfterComb cfg (fun ps => .seq ps k L) x c

theorem tailRel_ws_nil {cfg : ScanCfg} {L c : Complex} :
    TailRel cfg L [.tok .whitespace] c ↔ c = L := by
  rw [TailRel]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨sep, r, rest, h, hne, k, ps, hsep, _, _⟩)
    · rfl
    · obtain ⟨c0, s', rfl, _⟩ := sepRel_head hsep
      have h1 := congrArg List.length h
      simp only [List.length_cons, List.length_append, List.length_nil] at h1
      have := List.length_pos_iff.mpr hne; omega
  · rintro rfl; exact Or.inl ⟨by simp [AllWs, IsWs], rfl⟩

theorem res_nil {cfg : ScanCfg} {cur : Option Complex} {pend : Option Combinator} {c : Complex} :
    Res cfg cur pend [] c ↔ ∃ L, cur = some L ∧ pend = none ∧ c = L := by
  cases cur <;> cases pend <;> simp only [Res]
  · simp [itemRel_nil]
  · simp [afterComb_nil]
  · rw [tailRel_ws_nil]; simp
  · simp [afterComb_nil]

theorem res_ws {cfg : ScanCfg} {cur : Option Complex} {pend : Option Combinator} {x : List Component}
    {c : Complex} : Res cfg cur pend (.tok .whitespace :: x) c ↔ Res cfg cur pend x c := by
  cases cur <;> cases pend <;> simp only [Res]
  · exact itemRel_ws
  · rw [afterComb_ws]
  · exact tailRel_ws_ws
  · exact afterComb_ws

theorem res_comb {cfg : ScanCfg} {cur : Option Complex} {pend : Option Combinator}
    {x : List Component} {c : Complex} {d : Char} {k : Combinator} (hd : CombDelim d k) :
    Res cfg cur pend (.tok (.delim d) :: x) c ↔ pend = none ∧ Res cfg cur (some k) x c := by
  cases cur <;> cases pend <;> simp only [Res]
  · rw [itemRel_comb hd]; simp
  · simp [afterComb_comb hd]
  · rw [tailRel_ws_comb hd]; simp
  · simp [afterComb_comb hd]

theorem res_run {cfg : ScanCfg} {cur : Option Complex} {pend : Option Combinator}
    {r y : List Component} {c : Complex} (hrnb : NoBoundary r) (hrne : r ≠ []) (hy : BoundaryStart y) :
    Res cfg cur pend (r ++ y) c ↔
      ∃ ps, CompoundRel cfg r ps ∧ ∃ L, newCur cfg cur pend ps = some L ∧ TailRel cfg L y c := by
  cases cur with
  | none =>
    cases pend with
    | none =>
      simp only [Res, newCur, Option.getD_none, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [itemRel_run hrnb hrne hy]
      apply exists_congr; intro ps; apply and_congr_right; intro _
      unfold BaseComplex
      cases cfg.relative <;> simp
    | some k =>
      simp only [Res, newCur, Option.getD_some, Option.isSome_some, if_true]
      rw [afterComb_run hrnb hrne hy]
      unfold BaseComplex
      cases hr : cfg.relative <;> simp
  | some L =>
    cases pend with
    | none =>
      simp only [Res, newCur, Option.getD_none]
      rw [tailRel_ws_run hrnb hrne hy]; simp
    | some k =>
      simp only [Res, newCur, Option.getD_some]
      rw [afterComb_run hrnb hrne hy]; simp

/-! ## 項目一つ -/

def NoComma (x : List Component) : Prop := ∀ c ∈ x, c ≠ .tok .comma

/-- 項目の後ろ。入力の終わりか、`,` で始まる。 -/
def ItemEnd (k : List Component) : Prop := k = [] ∨ ∃ rest, k = .tok .comma :: rest

/-- 項目が `c` に読めたあとの `scan`。 -/
def Cont (cfg : ScanCfg) (done : List Complex) (c : Complex) : List Component → Option SelectorList
  | [] => some (c :: done).reverse
  | _ :: rest => scan cfg (initSt cfg (c :: done)) rest

theorem dropToComma_append_noComma : ∀ {y : List Component}, NoComma y →
    ∀ k, dropToComma (y ++ k) = dropToComma k
  | [], _, _ => rfl
  | c :: y, h, k => by
    have hc : isComma c = false := by
      cases hcc : isComma c
      · rfl
      · exact absurd (dropToComma_mem_comma hcc) (h c List.mem_cons_self)
    rw [List.cons_append, dropToComma, if_neg (by rw [hc]; simp)]
    exact dropToComma_append_noComma (fun x hx => h x (List.mem_cons_of_mem _ hx)) k

theorem scan_initSt_nil (cfg : ScanCfg) (done : List Complex) :
    scan cfg (initSt cfg done) [] = if cfg.forgiving = true then some done.reverse else none := by
  rw [scan_end, finishComplex_nil _ rfl]; rfl

/-- **`parts` が空の状態で項目が終わったら、`left` があって combinator が保留でなければ読めている。** -/
theorem scan_itemEnd {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) {k : List Component}
    (hk : ItemEnd k) :
    scan cfg st k =
      match st.cur, st.pend with
      | some L, none => Cont cfg st.done L k
      | _, _ => failK cfg st.done k := by
  rcases hk with rfl | ⟨rest, rfl⟩
  · rw [scan_end, finishComplex_nil st hp]
    cases st.cur <;> cases st.pend <;> simp [Cont, failK, dropToComma, scan_initSt_nil] <;> rfl
  · rw [scan_comma, finishComplex_nil st hp]
    cases st.cur <;> cases st.pend <;> simp [Cont, failK, dropToComma, isComma]

theorem finishComplex_parts {cfg : ScanCfg} (st : ScanSt) {ps : List Simple} (hne : ps ≠ []) :
    finishComplex cfg { st with parts := ps.reverse } =
      (newCur cfg st.cur st.pend ps).map (fun L => initSt cfg (L :: st.done)) := by
  unfold finishComplex
  rw [flush_parts st hne]
  cases newCur cfg st.cur st.pend ps <;> simp

/-- 項目が `parts` を積んだ状態で終わったとき。 -/
theorem scan_itemEnd_parts {cfg : ScanCfg} (st : ScanSt) {ps : List Simple} (hne : ps ≠ [])
    {k : List Component} (hk : ItemEnd k) :
    scan cfg { st with parts := ps.reverse } k =
      match newCur cfg st.cur st.pend ps with
      | some L => Cont cfg st.done L k
      | none => failK cfg st.done k := by
  rcases hk with rfl | ⟨rest, rfl⟩
  · rw [scan_end, finishComplex_parts st hne]
    cases newCur cfg st.cur st.pend ps with
    | none => simp [failK, dropToComma, scan_initSt_nil]
    | some L => simp [Cont, initSt]
  · rw [scan_comma, finishComplex_parts st hne]
    cases newCur cfg st.cur st.pend ps <;> simp [Cont, failK, dropToComma, isComma]

theorem scan_ws {cfg : ScanCfg} (st : ScanSt) (z : List Component) :
    scan cfg st (.tok .whitespace :: z) =
      match flush cfg st with
      | some st' => scan cfg st' z
      | none => if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma z) else none := by
  rw [scan.eq_def]; rfl

theorem noComma_append {a b : List Component} (h : NoComma (a ++ b)) : NoComma a ∧ NoComma b :=
  ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

theorem noComma_tail {c : Component} {x : List Component} (h : NoComma (c :: x)) : NoComma x :=
  fun d hd => h d (List.mem_cons_of_mem _ hd)

theorem boundaryStart_append {y k : List Component} (hy : BoundaryStart y) (hk : ItemEnd k) :
    BoundaryStart (y ++ k) := by
  intro c hc
  cases y with
  | nil =>
    rcases hk with rfl | ⟨rest, rfl⟩
    · cases hc
    · simp at hc; subst hc; exact Or.inr (Or.inl rfl)
  | cons a y => exact hy c (by simpa using hc)

/--
**項目一つ。** `parts` が空の状態から項目の残り `x` を読むと、状態に対応する残りの文法
（`Res`）に当たれば読めた値で続き、当たらなければこの項目を諦める。
-/
theorem item_main {cfg : ScanCfg} : ∀ (n : Nat) (x : List Component), x.length ≤ n →
    InnerOk (csize x) → NoComma x → ∀ (st : ScanSt), st.parts = [] →
    ∀ (k : List Component), ItemEnd k →
      (∀ c, Res cfg st.cur st.pend x c → scan cfg st (x ++ k) = Cont cfg st.done c k) ∧
      ((¬ ∃ c, Res cfg st.cur st.pend x c) → scan cfg st (x ++ k) = failK cfg st.done k)
  | n, [], _, _, _, st, hp, k, hk => by
    rw [List.nil_append, scan_itemEnd st hp hk]
    constructor
    · intro c hres
      obtain ⟨L, hc, hpn, rfl⟩ := res_nil.mp hres
      simp [hc, hpn]
    · intro hno
      cases hc : st.cur with
      | none => simp
      | some L =>
        cases hpn : st.pend with
        | none => exact absurd ⟨L, res_nil.mpr ⟨L, hc, hpn, rfl⟩⟩ hno
        | some _ => simp
  | 0, _ :: _, hn, _, _, _, _, _, _ => by simp at hn
  | n + 1, c0 :: x', hn, hih, hnc, st, hp, k, hk => by
    have hn' : x'.length ≤ n := by simpa using hn
    have hih' : InnerOk (csize x') := innerOk_mono (by simp only [csize_cons]; omega) hih
    by_cases hb : IsBoundary c0
    · rcases hb with rfl | rfl | ⟨d, k', rfl, hd⟩
      · -- 空白
        rw [List.cons_append, scan_ws_nil st hp]
        obtain ⟨ihC, ihS⟩ := item_main n x' hn' hih' (noComma_tail hnc) st hp k hk
        exact ⟨fun c h => ihC c (res_ws.mp h), fun h => ihS (fun ⟨c, hc⟩ => h ⟨c, res_ws.mpr hc⟩)⟩
      · exact absurd rfl (hnc _ List.mem_cons_self)
      · -- combinator
        rw [List.cons_append, scan_comb st hd, flush_nil hp]
        simp only
        cases hpend : st.pend with
        | some k0 =>
          simp only [Option.isSome_some, if_true]
          have : (if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma (x' ++ k))
              else none) = failK cfg st.done k := by
            simp [failK, dropToComma_append_noComma (noComma_tail hnc)]
          rw [this]
          refine ⟨fun c h => ?_, fun _ => rfl⟩
          rw [res_comb hd] at h; cases h.1
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          obtain ⟨ihC, ihS⟩ := item_main n x' hn' hih' (noComma_tail hnc)
            { st with pend := some k' } hp k hk
          refine ⟨fun c h => ihC c ?_, fun h => ihS (fun ⟨c, hc⟩ => h ⟨c, ?_⟩)⟩
          · rw [res_comb hd] at h; exact h.2
          · rw [res_comb hd]; exact ⟨rfl, hc⟩
    · -- compound
      obtain ⟨hsplit, hrnb, hy⟩ := runSplit_spec (c0 :: x')
      generalize hr : (runSplit (c0 :: x')).1 = r at hsplit hrnb
      generalize hyy : (runSplit (c0 :: x')).2 = y at hsplit hy
      have hrne : r ≠ [] := hr ▸ runSplit_ne_nil hb
      have hylen : y.length ≤ n := by
        have := congrArg List.length hsplit; simp at this
        have := List.length_pos_iff.mpr hrne; omega
      have hcs : csize r ≤ csize (c0 :: x') ∧ csize y ≤ csize (c0 :: x') := by
        rw [hsplit, csize_append]; omega
      have hncy : NoComma y := (noComma_append (hsplit ▸ hnc)).2
      rw [hsplit, List.append_assoc]
      have hyk := boundaryStart_append hy hk
      -- compound を閉じたあと
      have post : ∀ ps : List Simple, ps ≠ [] →
          (∀ c L, newCur cfg st.cur st.pend ps = some L → TailRel cfg L y c →
            scan cfg { st with parts := ps.reverse } (y ++ k) = Cont cfg st.done c k) ∧
          ((¬ ∃ c L, newCur cfg st.cur st.pend ps = some L ∧ TailRel cfg L y c) →
            scan cfg { st with parts := ps.reverse } (y ++ k) = failK cfg st.done k) := by
        intro ps hpsne
        cases y with
        | nil =>
          rw [List.nil_append, scan_itemEnd_parts st hpsne hk]
          constructor
          · intro c L hL ht; rw [hL]; rw [tailRel_nil.mp ht]
          · intro hno
            cases hL : newCur cfg st.cur st.pend ps with
            | none => rfl
            | some L => exact absurd ⟨L, L, hL, tailRel_nil.mpr rfl⟩ hno
        | cons c1 y' =>
          have hy'len : y'.length ≤ n := by simp at hylen; omega
          have hih'' : InnerOk (csize y') :=
            innerOk_mono (by have h2 := hcs.2; rw [csize_cons] at h2; omega) hih
          rcases hy c1 rfl with rfl | rfl | ⟨d, k', rfl, hd⟩
          · -- 空白
            rw [List.cons_append, scan_ws, flush_parts st hpsne]
            cases hL : newCur cfg st.cur st.pend ps with
            | none =>
              simp only [Option.map_none]
              refine ⟨(fun c L h _ => by cases h), fun _ => ?_⟩
              simp [failK, dropToComma_append_noComma (noComma_tail hncy)]
            | some L =>
              simp only [Option.map_some]
              obtain ⟨ihC, ihS⟩ := item_main n y' hy'len hih'' (noComma_tail hncy)
                { st with cur := some L, pend := none, parts := [] } rfl k hk
              refine ⟨fun c L' hL' ht => ?_, fun hno => ?_⟩
              · cases hL'; exact ihC c ht
              · exact ihS (fun ⟨c, hc⟩ => hno ⟨c, L, rfl, hc⟩)
          · exact absurd rfl (hncy _ List.mem_cons_self)
          · -- combinator
            rw [List.cons_append, scan_comb _ hd, flush_parts st hpsne]
            cases hL : newCur cfg st.cur st.pend ps with
            | none =>
              simp only [Option.map_none]
              refine ⟨(fun c L h _ => by cases h), fun _ => ?_⟩
              simp [failK, dropToComma_append_noComma (noComma_tail hncy)]
            | some L =>
              simp only [Option.map_some, Option.isSome_none, Bool.false_eq_true, if_false]
              obtain ⟨ihC, ihS⟩ := item_main n y' hy'len hih'' (noComma_tail hncy)
                { st with cur := some L, pend := some k', parts := [] } rfl k hk
              refine ⟨fun c L' hL' ht => ?_, fun hno => ?_⟩
              · cases hL'; exact ihC c ((tailRel_comb hd).mp ht)
              · exact ihS (fun ⟨c, hc⟩ => hno ⟨c, L, rfl, (tailRel_comb hd).mpr hc⟩)
      constructor
      · intro c hres
        obtain ⟨ps, hps, L, hL, ht⟩ := (res_run hrnb hrne hy).mp hres
        have hpsne : ps ≠ [] := by
          intro h; subst h
          rw [CompoundRel] at hps
          rcases hps with ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, h⟩
          · cases h
          · exact h rfl
        rw [scan_compound (innerOk_mono hcs.1 hih) hps st hp _ hyk]
        exact (post ps hpsne).1 c L hL ht
      · intro hno
        by_cases hps : ∃ ps, CompoundRel cfg r ps
        · obtain ⟨ps, hps⟩ := hps
          have hpsne : ps ≠ [] := by
            intro h; subst h
            rw [CompoundRel] at hps
            rcases hps with ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, h⟩
            · cases h
            · exact h rfl
          rw [scan_compound (innerOk_mono hcs.1 hih) hps st hp _ hyk]
          exact (post ps hpsne).2 (fun ⟨c, L, hL, ht⟩ =>
            hno ⟨c, (res_run hrnb hrne hy).mpr ⟨ps, hps, L, hL, ht⟩⟩)
        · rw [scan_compound_fail (innerOk_mono hcs.1 hih) hrnb hrne st hp hps _ hyk]
          simp [failK, dropToComma_append_noComma hncy]

/-! ## selector list -/

/-- 項目ごとの結果。読めた項目は `some`、forgiving で落とした項目は `none`。 -/
inductive ItemsRel (cfg : ScanCfg) : List (List Component) → List (Option Complex) → Prop where
  | nil : ItemsRel cfg [] []
  | keep {it : List Component} {its : List (List Component)} {c : Complex} {rs : List (Option Complex)}
      (h : ItemRel cfg it c) (t : ItemsRel cfg its rs) : ItemsRel cfg (it :: its) (some c :: rs)
  | drop {it : List Component} {its : List (List Component)} {rs : List (Option Complex)}
      (hf : cfg.forgiving = true) (h : ¬ ∃ c, ItemRel cfg it c) (t : ItemsRel cfg its rs) :
      ItemsRel cfg (it :: its) (none :: rs)

theorem intercalate_cons_cons (it it2 : List Component) (rest : List (List Component)) :
    [Component.tok .comma].intercalate (it :: it2 :: rest) =
      it ++ .tok .comma :: [Component.tok .comma].intercalate (it2 :: rest) := by
  rw [List.intercalate_cons_cons]; simp

/-- **項目に分けた列の `scan` は、項目ごとの結果を順に並べる。** -/
theorem scan_items {cfg : ScanCfg} : ∀ (items : List (List Component)), items ≠ [] →
    (∀ it ∈ items, NoComma it ∧ InnerOk (csize it)) → ∀ (done : List Complex) (L : SelectorList),
    scan cfg (initSt cfg done) ([Component.tok .comma].intercalate items) = some L ↔
      ∃ res, ItemsRel cfg items res ∧ L = done.reverse ++ res.filterMap id
  | [], h, _, _, _ => absurd rfl h
  | [it], _, hit, done, L => by
    obtain ⟨hnc, hih⟩ := hit it (by simp)
    simp only [List.intercalate_singleton]
    obtain ⟨hC, hS⟩ := item_main it.length it (Nat.le_refl _) hih hnc (initSt cfg done) rfl []
      (Or.inl rfl)
    simp only [List.append_nil] at hC hS
    constructor
    · intro h
      by_cases hex : ∃ c, ItemRel cfg it c
      · obtain ⟨c, hc⟩ := hex
        rw [hC c hc] at h
        simp only [Cont, Option.some.injEq] at h
        exact ⟨[some c], .keep hc .nil, by simp [initSt] at h; simp [← h]⟩
      · rw [hS hex] at h
        unfold failK at h
        cases hf : cfg.forgiving with
        | false => simp [hf] at h
        | true =>
          rw [if_pos hf, dropToComma, scan_initSt_nil, if_pos hf] at h
          simp only [Option.some.injEq, initSt] at h
          exact ⟨[none], .drop hf hex .nil, by simp [← h]⟩
    · rintro ⟨res, hres, rfl⟩
      cases hres with
      | keep hc t =>
        cases t
        rw [hC _ hc]; simp [Cont, initSt]
      | drop hf hno t =>
        cases t
        rw [hS hno]; simp only [failK, hf, if_true, dropToComma, scan_initSt_nil]; simp [initSt]
  | it :: it2 :: rest, _, hit, done, L => by
    obtain ⟨hnc, hih⟩ := hit it (by simp)
    have hrest : ∀ x ∈ it2 :: rest, NoComma x ∧ InnerOk (csize x) :=
      fun x hx => hit x (List.mem_cons_of_mem _ hx)
    rw [intercalate_cons_cons]
    obtain ⟨hC, hS⟩ := item_main it.length it (Nat.le_refl _) hih hnc (initSt cfg done) rfl
      (.tok .comma :: [Component.tok .comma].intercalate (it2 :: rest)) (Or.inr ⟨_, rfl⟩)
    constructor
    · intro h
      by_cases hex : ∃ c, ItemRel cfg it c
      · obtain ⟨c, hc⟩ := hex
        rw [hC c hc] at h
        simp only [Cont, initSt] at h
        obtain ⟨res, hres, rfl⟩ := (scan_items (it2 :: rest) (by simp) hrest (c :: done) L).mp h
        exact ⟨some c :: res, .keep hc hres, by simp⟩
      · rw [hS hex] at h
        unfold failK at h
        cases hf : cfg.forgiving with
        | false => simp [hf] at h
        | true =>
          rw [if_pos hf] at h
          simp only [dropToComma, isComma, if_true, initSt] at h
          obtain ⟨res, hres, rfl⟩ := (scan_items (it2 :: rest) (by simp) hrest done L).mp h
          exact ⟨none :: res, .drop hf hex hres, by simp⟩
    · rintro ⟨res, hres, rfl⟩
      cases hres with
      | keep hc t =>
        rename_i c rs
        rw [hC _ hc]
        simp only [Cont, initSt]
        exact (scan_items (it2 :: rest) (by simp) hrest (c :: done) _).mpr ⟨rs, t, by simp⟩
      | drop hf hno t =>
        rename_i rs
        rw [hS hno]
        simp only [failK, hf, if_true, dropToComma, isComma, initSt]
        exact (scan_items (it2 :: rest) (by simp) hrest done _).mpr ⟨rs, t, by simp⟩

/-- 項目一つの結果の条件（`SelListRel` の中身）。 -/
def ItemOk (cfg : ScanCfg) (it : List Component) : Option Complex → Prop
  | some c => ItemRel cfg it c
  | none => cfg.forgiving = true ∧ ¬ ∃ c, ItemRel cfg it c

theorem itemsRel_iff_zip {cfg : ScanCfg} : ∀ (items : List (List Component)) (res : List (Option Complex)),
    ItemsRel cfg items res ↔ res.length = items.length ∧ ∀ q ∈ items.zip res, ItemOk cfg q.1 q.2
  | [], [] => by simp; exact .nil
  | [], _ :: _ => by simp; intro h; cases h
  | _ :: _, [] => by simp; intro h; cases h
  | it :: its, r :: rs => by
    rw [List.zip_cons_cons, List.forall_mem_cons, List.length_cons, List.length_cons]
    constructor
    · intro h
      cases h with
      | keep hc t =>
        obtain ⟨h1, h2⟩ := (itemsRel_iff_zip its _).mp t
        exact ⟨by omega, hc, h2⟩
      | drop hf hno t =>
        obtain ⟨h1, h2⟩ := (itemsRel_iff_zip its _).mp t
        exact ⟨by omega, ⟨hf, hno⟩, h2⟩
    · rintro ⟨hlen, hq, hrest⟩
      have t := (itemsRel_iff_zip its rs).mpr ⟨by omega, hrest⟩
      cases r with
      | some c => exact .keep hq t
      | none => exact .drop hq.1 hq.2 t

theorem forall_attach_zip {α β : Type} {l : List α} {r : List β} {P : α → β → Prop} :
    (∀ p ∈ l.attach.zip r, P p.1.1 p.2) ↔ ∀ q ∈ l.zip r, P q.1 q.2 := by
  have : l.zip r = (l.attach.zip r).map (Prod.map Subtype.val id) := by
    rw [← List.zip_map_left, List.attach_map_subtype_val]
  rw [this, List.forall_mem_map]
  rfl

/-- **`SelListRel` は項目への分け方と、項目ごとの結果である。** -/
theorem selListRel_iff {cfg : ScanCfg} {cs : List Component} {l : List Complex} :
    SelListRel cfg cs l ↔
      ∃ items, CommaItems cs items ∧ ∃ res, ItemsRel cfg items res ∧ l = res.filterMap id := by
  rw [SelListRel]
  constructor
  · rintro ⟨items, h, res, hlen, hall, rfl⟩
    refine ⟨items, h, res, (itemsRel_iff_zip items res).mpr ⟨hlen, ?_⟩, rfl⟩
    have := (forall_attach_zip (P := fun it r => ItemOk cfg it r)).mp (fun p hp => by
      have := hall p hp
      cases hp2 : p.2 <;> rw [hp2] at this <;> exact this)
    exact this
  · rintro ⟨items, h, res, hres, rfl⟩
    obtain ⟨hlen, hall⟩ := (itemsRel_iff_zip items res).mp hres
    refine ⟨items, h, res, hlen, fun p hp => ?_, rfl⟩
    have := (forall_attach_zip (P := fun it r => ItemOk cfg it r)).mpr hall p hp
    cases hp2 : p.2 <;> rw [hp2] at this <;> exact this

/-! ## まとめ -/

/-- top-level の `,` で分ける。 -/
def splitCommas : List Component → List (List Component)
  | [] => [[]]
  | c :: rest =>
    if isComma c then [] :: splitCommas rest
    else
      match splitCommas rest with
      | it :: its => (c :: it) :: its
      | [] => [[c]]

theorem splitCommas_ne_nil : ∀ cs, splitCommas cs ≠ []
  | [] => by simp [splitCommas]
  | c :: rest => by
    unfold splitCommas
    split
    · simp
    · split <;> simp

theorem splitCommas_spec : ∀ cs : List Component, CommaItems cs (splitCommas cs)
  | [] => ⟨by simp [splitCommas], by simp [splitCommas], by simp [splitCommas]⟩
  | c :: rest => by
    obtain ⟨h1, h2, h3⟩ := splitCommas_spec rest
    unfold splitCommas
    by_cases hc : isComma c = true
    · rw [if_pos hc]
      have : c = .tok .comma := dropToComma_mem_comma hc
      subst this
      refine ⟨?_, by simp, ?_⟩
      · obtain ⟨it, its, hcons⟩ := List.exists_cons_of_ne_nil h2
        rw [hcons] at h1 ⊢
        rw [List.intercalate_cons_cons]; simp [h1]
      · intro it hit; simp at hit
        rcases hit with rfl | hit
        · simp
        · exact h3 it hit
    · rw [if_neg hc]
      cases hs : splitCommas rest with
      | nil => exact absurd hs (splitCommas_ne_nil rest)
      | cons it its =>
        simp only
        rw [hs] at h1 h3
        refine ⟨?_, by simp, ?_⟩
        · cases its with
          | nil => simp at h1 ⊢; exact h1
          | cons it2 its2 =>
            rw [List.intercalate_cons_cons] at h1 ⊢; simp [h1]
        · intro x hx
          simp at hx
          rcases hx with rfl | hx
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · intro h; subst h; simp [isComma] at hc
            · exact h3 _ (by simp) y hy
          · exact h3 x (by simp [hx])

theorem commaItems_ok {cs : List Component} {items : List (List Component)} (h : CommaItems cs items)
    (hih : InnerOk (csize cs)) : ∀ it ∈ items, NoComma it ∧ InnerOk (csize it) := by
  intro it hit
  refine ⟨fun c hc => h.2.2 it hit c hc, innerOk_mono ?_ hih⟩
  rw [h.1]; exact csize_le_of_mem_intercalate _ items it hit

/-- **どの大きさまでも、`scan` は関係 `SelListRel` に一致する。** -/
theorem innerOk_all : ∀ N, InnerOk N
  | 0 => fun _ _ h => absurd h (by omega)
  | N + 1 => by
    intro cfg cs hcs l
    have hih : InnerOk (csize cs) := innerOk_mono (by omega) (innerOk_all N)
    rw [selListRel_iff]
    constructor
    · intro h
      have hsplit := splitCommas_spec cs
      have h' : scan cfg (initSt cfg []) ([Component.tok .comma].intercalate (splitCommas cs)) = some l := by
        rw [← hsplit.1]; exact h
      obtain ⟨res, hres, hl⟩ := (scan_items _ hsplit.2.1 (commaItems_ok hsplit hih) [] l).mp h'
      exact ⟨splitCommas cs, hsplit, res, hres, by simpa using hl⟩
    · rintro ⟨items, hitems, res, hres, rfl⟩
      rw [hitems.1]
      exact (scan_items items hitems.2.1 (commaItems_ok hitems hih) [] _).mpr ⟨res, hres, by simp⟩

/-- **`scan` は selector の文法 `SelListRel` にちょうど一致する。** -/
theorem scan_spec (cfg : ScanCfg) (cs : List Component) (l : SelectorList) :
    scan cfg (initSt cfg []) cs = some l ↔ SelListRel cfg cs l :=
  innerOk_all (csize cs + 1) cfg cs (by omega) l

/-- **§19.1 "parse a selector" は、文法 `ParsesTo` にちょうど一致する。** -/
theorem parseSelector_spec (input : String) (l : SelectorList) :
    parseSelector input = some l ↔ ParsesTo input l := by
  unfold parseSelector ParsesTo
  cases h : parseComponents input with
  | none => simp
  | some cs =>
    simp only [Option.some.injEq, exists_eq_left']
    exact scan_spec _ cs l

/-- **`parseSelector` が失敗する（`SyntaxError`）のは、文法に当たる読み方が無いときだけである。** -/
theorem parseSelector_none_iff (input : String) :
    parseSelector input = none ↔ ¬ ∃ l, ParsesTo input l := by
  constructor
  · intro h ⟨l, hl⟩; rw [(parseSelector_spec input l).mpr hl] at h; cases h
  · intro h
    cases hp : parseSelector input with
    | none => rfl
    | some l => exact absurd ⟨l, (parseSelector_spec input l).mp hp⟩ h

end Selectors.Spec
