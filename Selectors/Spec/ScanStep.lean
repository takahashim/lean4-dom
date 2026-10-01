import Selectors.Spec.Scan
import Selectors.Spec.Split
import Selectors.Spec.AttrSound

/-!
# `scan` の一歩ずつの性質

`Selectors/Spec/ScanSound.lean` が `scan` と文法の関係（`Selectors/Spec/Scan.lean`）の一致を示すための
部品。compound の区切り（`IsBoundary`）、subclass selector 一つ（`scan_piece` / `scan_noPiece`）、
compound 一つ（`scan_compound` / `scan_compound_fail`）について、`scan` が何をするかを言う。

失敗は「この項目を諦める」で、strict なら `none`、forgiving なら次の `,` から読み直す（`failK`）。
-/
namespace Selectors.Spec
open Selectors Infra

/-! ## 区切り -/

/-- compound の終わりになる component。空白、`,`、combinator の delim。 -/
def IsBoundary (c : Component) : Prop :=
  c = .tok .whitespace ∨ c = .tok .comma ∨ ∃ d k, c = .tok (.delim d) ∧ CombDelim d k

/-- 列が空か、区切りで始まる。 -/
def BoundaryStart (z : List Component) : Prop := ∀ c, z.head? = some c → IsBoundary c

/-- 区切りを含まない。 -/
def NoBoundary (r : List Component) : Prop := ∀ c ∈ r, ¬ IsBoundary c

theorem not_boundary_tok_of {t : Token}
    (h1 : t ≠ .whitespace) (h2 : t ≠ .comma)
    (h3 : ∀ d, t = .delim d → d ≠ '>' ∧ d ≠ '+' ∧ d ≠ '~') : ¬ IsBoundary (.tok t) := by
  rintro (h | h | ⟨d, k, h, hk⟩)
  · exact h1 (by cases h; rfl)
  · exact h2 (by cases h; rfl)
  · cases h
    obtain ⟨a, b, c⟩ := h3 d rfl
    rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp_all

theorem typeRel_noBoundary {t : List Component} {s : Simple} (h : TypeRel t s) : NoBoundary t := by
  rcases h with ⟨n, rfl, _⟩ | ⟨rfl, _⟩ | ⟨n, rfl, _⟩ | ⟨rfl, _⟩ <;>
    intro c hc <;> simp at hc <;> (try rcases hc with rfl | rfl | rfl) <;> (try subst hc) <;>
    exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd <;> decide)

theorem pieceRel_noBoundary {cfg : ScanCfg} {p : List Component} {s : Simple}
    (h : PieceRel cfg p s) : NoBoundary p := by
  have hfunc : ∀ name args, NoBoundary [Component.tok .colon, .func name args] := by
    intro name args c hc
    simp at hc
    rcases hc with rfl | rfl
    · exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd)
    · rintro (h | h | ⟨d, k, h, _⟩) <;> cases h
  rw [PieceRel] at h
  rcases h with ⟨v, rfl, _⟩ | ⟨n, rfl, _⟩ | ⟨items, rfl, _⟩ | ⟨n, rfl, _⟩ |
    ⟨name, args, rfl, _⟩ | ⟨name, args, rfl, _⟩ | ⟨name, args, rfl, _⟩ |
    ⟨name, args, _, _, _, rfl, _⟩ | ⟨name, args, rfl, _⟩
  · intro c hc; simp at hc; subst hc
    exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd)
  · intro c hc; simp at hc
    rcases hc with rfl | rfl
    · exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd <;> decide)
    · exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd)
  · intro c hc; simp at hc; subst hc
    rintro (h | h | ⟨d, k, h, _⟩) <;> cases h
  · intro c hc; simp at hc
    rcases hc with rfl | rfl <;> exact not_boundary_tok_of (by simp) (by simp) (by intro d hd; cases hd)
  all_goals exact hfunc _ _

theorem noBoundary_append {a b : List Component} (ha : NoBoundary a) (hb : NoBoundary b) :
    NoBoundary (a ++ b) := by
  intro c hc; rcases List.mem_append.mp hc with h | h; exact ha c h; exact hb c h

theorem subclassesRel_noBoundary_aux {cfg : ScanCfg} : ∀ (n : Nat) (r : List Component)
    (ss : List Simple), r.length ≤ n → SubclassesRel cfg r ss → NoBoundary r
  | n, r, ss, hn, h => by
    rw [SubclassesRel] at h
    rcases h with ⟨rfl, _⟩ | ⟨p, rest, rfl, hne, s, ss', hp, hrest, _⟩
    · intro c hc; simp at hc
    · cases n with
      | zero => simp at hn; exact absurd hn.1 hne
      | succ n =>
        have : rest.length ≤ n := by
          rw [List.length_append] at hn; have := List.length_pos_iff.mpr hne; omega
        exact noBoundary_append (pieceRel_noBoundary hp)
          (subclassesRel_noBoundary_aux n rest ss' this hrest)

theorem subclassesRel_noBoundary {cfg : ScanCfg} {r : List Component} {ss : List Simple}
    (h : SubclassesRel cfg r ss) : NoBoundary r :=
  subclassesRel_noBoundary_aux r.length r ss (Nat.le_refl _) h

theorem compoundRel_noBoundary {cfg : ScanCfg} {r : List Component} {ps : List Simple}
    (h : CompoundRel cfg r ps) : NoBoundary r := by
  rw [CompoundRel] at h
  rcases h with ⟨t, rest, s, ss, rfl, ht, hr, _⟩ | ⟨hr, _⟩
  · exact noBoundary_append (typeRel_noBoundary ht) (subclassesRel_noBoundary hr)
  · exact subclassesRel_noBoundary hr

theorem comb_isBoundary {d : Char} {k : Combinator} (h : CombDelim d k) :
    IsBoundary (.tok (.delim d)) := Or.inr (Or.inr ⟨d, k, rfl, h⟩)

theorem ws_isBoundary : IsBoundary (.tok .whitespace) := Or.inl rfl

/-- separator は空でなく、区切りで始まる。 -/
theorem sepRel_head {sep : List Component} {k : Combinator} (h : SepRel sep k) :
    ∃ c rest, sep = c :: rest ∧ IsBoundary c := by
  rcases h with ⟨hne, hws, _⟩ | ⟨w1, d, w2, rfl, hw1, _, hd⟩
  · obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨c, rest, rfl, by rw [hws c (by simp)]; exact ws_isBoundary⟩
  · cases w1 with
    | nil => exact ⟨_, _, rfl, comb_isBoundary hd⟩
    | cons c w1 => exact ⟨c, _, rfl, by rw [hw1 c (by simp)]; exact ws_isBoundary⟩

/-- **`TailRel` の残りは空か、区切りで始まる。** -/
theorem tailRel_boundaryStart {cfg : ScanCfg} {left : Complex} {x : List Component} {c : Complex}
    (h : TailRel cfg left x c) : BoundaryStart x := by
  rw [TailRel] at h
  intro c' hc'
  rcases h with ⟨hws, _⟩ | ⟨sep, r, rest, rfl, _, k, parts, hsep, _, _⟩
  · rw [hws c' (List.mem_of_mem_head? hc')]; exact ws_isBoundary
  · obtain ⟨c0, srest, rfl, hb⟩ := sepRel_head hsep
    simp at hc'; subst hc'; exact hb

/-- **区切りを含まない列の、区切りの手前までの切り方は一つである。** -/
theorem run_split_unique : ∀ {r r' y y' : List Component}, r ++ y = r' ++ y' →
    NoBoundary r → NoBoundary r' → BoundaryStart y → BoundaryStart y' → r = r' ∧ y = y'
  | [], r', y, y', h, _, hr', hy, _ => by
    cases r' with
    | nil => simpa using h
    | cons c r' =>
      simp at h; subst h
      exact absurd (hy c (by simp)) (hr' c (by simp))
  | c :: r, [], y, y', h, hr, _, _, hy' => by
    simp at h; subst h
    exact absurd (hy' c (by simp)) (hr c (by simp))
  | c :: r, c' :: r', y, y', h, hr, hr', hy, hy' => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := run_split_unique h (fun x hx => hr x (by simp [hx]))
      (fun x hx => hr' x (by simp [hx])) hy hy'
    exact ⟨by rw [h1], h2⟩

/-- 区切りを含まない列は `,` も含まないので、`dropToComma` は素通りする。 -/
theorem dropToComma_append_noBoundary : ∀ {a : List Component}, NoBoundary a →
    ∀ b, dropToComma (a ++ b) = dropToComma b
  | [], _, b => rfl
  | c :: a, h, b => by
    have hc : isComma c = false := by
      cases hcc : isComma c
      · rfl
      · exact absurd (Or.inr (Or.inl (dropToComma_mem_comma hcc))) (h c (by simp))
    rw [List.cons_append, dropToComma, if_neg (by rw [hc]; simp)]
    exact dropToComma_append_noBoundary (fun x hx => h x (by simp [hx])) b


theorem simplePseudo_iff (n : String) (s : Simple) : simplePseudo n = some s ↔ PseudoName n s := by
  unfold simplePseudo PseudoName
  generalize asciiLowercase n = m
  split <;> simp_all <;> exact eq_comm

theorem nthKindOf_iff (n : String) (kind : NthKind) (ofA : Bool) :
    nthKindOf n = some (kind, ofA) ↔ NthName n kind ofA := by
  unfold nthKindOf NthName
  generalize asciiLowercase n = m
  split <;> simp_all <;> (intro _; exact eq_comm)

theorem nthName_lower {n : String} {kind : NthKind} {ofA : Bool} (h : NthName n kind ofA) :
    asciiLowercase n ≠ "is" ∧ asciiLowercase n ≠ "where" ∧ asciiLowercase n ≠ "not" ∧
      asciiLowercase n ≠ "has" := by
  unfold NthName at h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem splitAtOf_none_iff : ∀ (l : List Component),
    splitAtOf l = none ↔ ∀ m ∈ l, isOfIdent m = false
  | [] => by simp [splitAtOf]
  | c :: rest => by
    rw [splitAtOf]
    by_cases hc : isOfIdent c = true
    · rw [if_pos hc]
      simp only [reduceCtorEq, false_iff]
      intro hall
      have := hall c List.mem_cons_self
      rw [hc] at this; cases this
    · rw [if_neg hc]
      have ih := splitAtOf_none_iff rest
      cases h : splitAtOf rest with
      | some ab =>
        simp only [reduceCtorEq, false_iff]
        intro hall
        have := ih.mpr (fun m hm => hall m (List.mem_cons_of_mem _ hm))
        rw [h] at this; cases this
      | none =>
        simp only [true_iff]
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simpa using hc
        · exact ih.mp h m hm

theorem asciiLowercase_idem (s : String) : asciiLowercase (asciiLowercase s) = asciiLowercase s := by
  unfold asciiLowercase
  rw [String.toList_ofList, List.map_map]
  congr 1
  exact List.map_congr_left (fun c _ => asciiLowerChar_idem c)

theorem nthName_beq {n : String} {kind : NthKind} {ofA : Bool} (h : NthName n kind ofA) :
    (asciiLowercase n == "is") = false ∧ (asciiLowercase n == "where") = false ∧
      (asciiLowercase n == "not") = false ∧ (asciiLowercase n == "has") = false := by
  obtain ⟨h1, h2, h3, h4⟩ := nthName_lower h
  simp [h1, h2, h3, h4]

/-- 中の selector list についての帰納法の仮定。 -/
def InnerOk (bound : Nat) : Prop :=
  ∀ (cfg : ScanCfg) (args : List Component), csize args < bound → ∀ l,
    scan cfg (initSt cfg []) args = some l ↔ SelListRel cfg args l

theorem csize_func_args (name : String) (args : List Component) :
    csize args < csize [Component.tok .colon, .func name args] := by
  simp only [csize, csizeC]; omega

/-- **subclass selector 一つが読めるなら、`scan` はその simple selector を `parts` に積んで進む。** -/
theorem scan_piece {cfg : ScanCfg} {p : List Component} {s : Simple}
    (hih : InnerOk (csize p)) (h : PieceRel cfg p s) (st : ScanSt) (w : List Component) :
    scan cfg st (p ++ w) = scan cfg { st with parts := s :: st.parts } w := by
  rw [PieceRel] at h
  rcases h with ⟨v, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨items, rfl, hattr⟩ | ⟨n, rfl, hps⟩ |
    ⟨name, args, rfl, l, hname, hl⟩ | ⟨name, args, rfl, l, hname, rfl, hl⟩ |
    ⟨name, args, rfl, l, hname, hin, rfl, hl⟩ |
    ⟨name, args, kind, ofA, ab, rfl, hnth, hnoof, hab, rfl⟩ |
    ⟨name, args, rfl, kind, ab, a, m, b, l, rfl, hnth, hm, hnoof, hab, hl, rfl⟩
  · rw [List.cons_append, List.nil_append, scan]; simp
  · simp only [List.cons_append, List.nil_append]; rw [scan]; simp [CH_GT, CH_PLUS, CH_TILDE, CH_DOT]
  · simp only [List.cons_append, List.nil_append]; rw [scan]
    rw [(parseAttrBlock_spec items s).mpr hattr]; simp
  · simp only [List.cons_append, List.nil_append]; rw [scan]
    rw [(simplePseudo_iff n s).mpr hps]
  · have hscan := (hih (innerCfg true false cfg.inHas) args (csize_func_args name args) l).mpr hl
    simp only [List.cons_append, List.nil_append]; rw [scan]
    rcases hname with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · simp only [hn]; simp only [innerCfg] at hscan; simp [hscan]
    · simp only [hn]; simp only [innerCfg] at hscan; simp [hscan]
  · have hscan := (hih (innerCfg false false cfg.inHas) args (csize_func_args name args) l).mpr hl
    simp only [List.cons_append, List.nil_append]; rw [scan]
    simp only [hname]; simp only [innerCfg] at hscan; simp [hscan]
  · have hscan := (hih (innerCfg false true true) args (csize_func_args name args) l).mpr hl
    simp only [List.cons_append, List.nil_append]; rw [scan]
    simp only [hname, hin]; simp only [innerCfg] at hscan; simp [hscan]
  · obtain ⟨h1, h2, h3, h4⟩ := nthName_lower hnth
    simp only [List.cons_append, List.nil_append]; rw [scan]
    obtain ⟨b1, b2, b3, b4⟩ := nthName_beq hnth
    simp only [b1, b2, b3, b4, Bool.or_false, Bool.false_eq_true, if_false]
    rw [show nthKindOf (asciiLowercase name) = some (kind, ofA) from by
      unfold nthKindOf; rw [asciiLowercase_idem]; exact (nthKindOf_iff _ _ _).mpr hnth]
    simp only
    split
    · rw [(parseAnBFull_spec args ab).mpr hab]
    · next hs => rw [(splitAtOf_none_iff args).mpr hnoof] at hs; cases hs
  · obtain ⟨h1, h2, h3, h4⟩ := nthName_lower hnth
    have hb : csize b < csize [Component.tok .colon, .func name (a ++ m :: b)] := by
      simp only [csize, csizeC, csize_append]; omega
    have hscan := (hih (innerCfg false false cfg.inHas) b hb l).mpr hl
    simp only [List.cons_append, List.nil_append]; rw [scan]
    obtain ⟨b1, b2, b3, b4⟩ := nthName_beq hnth
    simp only [b1, b2, b3, b4, Bool.or_false, Bool.false_eq_true, if_false]
    rw [show nthKindOf (asciiLowercase name) = some (kind, true) from by
      unfold nthKindOf; rw [asciiLowercase_idem]; exact (nthKindOf_iff _ _ _).mpr hnth]
    simp only
    split
    · next hs =>
      rw [splitAtOf_none_iff] at hs
      rw [hs m (by simp)] at hm; cases hm
    · next a' b' hs =>
      obtain ⟨m', heq, hm', hno'⟩ := (splitAtOf_spec _ _ _).mp hs
      have hsplit := (splitAtOf_spec (a ++ m :: b) a b).mpr ⟨m, rfl, hm, hnoof⟩
      rw [hs] at hsplit
      simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [(parseAnBFull_spec _ ab).mpr hab]
      simp only [innerCfg] at hscan; simp [hscan]

/-- 項目の途中で失敗したときの `scan` の続き。forgiving なら次の `,` から読み直す。 -/
def failK (cfg : ScanCfg) (done : List Complex) (z : List Component) : Option SelectorList :=
  if cfg.forgiving = true then scan cfg (initSt cfg done) (dropToComma z) else none

theorem pieceRel_hash {cfg : ScanCfg} (v : String) : PieceRel cfg [.tok (.hash v true)] (.id v) := by
  rw [PieceRel]; exact Or.inl ⟨v, rfl, rfl⟩

theorem noBoundary_tail {c : Component} {r : List Component} (h : NoBoundary (c :: r)) :
    NoBoundary r := fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem noBoundary_head {c : Component} {r : List Component} (h : NoBoundary (c :: r)) :
    ¬ IsBoundary c := h c List.mem_cons_self

theorem not_ident_head_of_boundaryStart {z : List Component} (hz : BoundaryStart z) (n : String)
    (rest : List Component) : z ≠ .tok (.ident n) :: rest := by
  rintro rfl
  rcases hz _ rfl with h | h | ⟨d, k, h, _⟩ <;> cases h

theorem pieceRel_cls {cfg : ScanCfg} (n : String) :
    PieceRel cfg [.tok (.delim '.'), .tok (.ident n)] (.cls n) := by
  rw [PieceRel]; exact Or.inr (Or.inl ⟨n, rfl, rfl⟩)

theorem pieceRel_attr {cfg : ScanCfg} {items : List Component} {s : Simple}
    (h : AttrBlockSyntax items s) : PieceRel cfg [.block .lbracket items] s := by
  rw [PieceRel]; exact Or.inr (Or.inr (Or.inl ⟨items, rfl, h⟩))

theorem pieceRel_pseudo {cfg : ScanCfg} {n : String} {s : Simple} (h : PseudoName n s) :
    PieceRel cfg [.tok .colon, .tok (.ident n)] s := by
  rw [PieceRel]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl, h⟩)))

/-- 失敗する token の後ろの `scan`。 -/
theorem failK_of_noBoundary {cfg : ScanCfg} {done : List Complex} {r z : List Component}
    (h : NoBoundary r) :
    (if cfg.forgiving = true then scan cfg (initSt cfg done) (dropToComma (r ++ z)) else none) =
      failK cfg done z := by
  simp [failK, dropToComma_append_noBoundary h]

example (cfg : ScanCfg) (st : ScanSt) (x : List Component) : scan cfg st (.tok (.delim '.') :: x) =
      match x with
      | .tok (.ident n) :: rest2 => scan cfg { st with parts := .cls n :: st.parts } rest2
      | r => if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma r) else none := by
  rw [scan.eq_def]
  simp only [show ('.' == CH_GT || '.' == CH_PLUS || '.' == CH_TILDE) = false from by decide,
    show ('.' == CH_DOT) = true from by decide, Bool.false_eq_true, if_false, if_true]
  rfl

theorem delim_dot_scan_fail {cfg : ScanCfg} (st : ScanSt) (x : List Component)
    (hx : ∀ n rest, x ≠ .tok (.ident n) :: rest) :
    scan cfg st (.tok (.delim '.') :: x) =
      if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma x) else none := by
  rw [scan.eq_def]
  simp only [show ('.' == CH_GT || '.' == CH_PLUS || '.' == CH_TILDE) = false from by decide,
    show ('.' == CH_DOT) = true from by decide, Bool.false_eq_true, if_false, if_true]

theorem delim_star_scan_fail {cfg : ScanCfg} (st : ScanSt) (hpe : st.parts.isEmpty = false)
    (x : List Component) :
    scan cfg st (.tok (.delim '*') :: x) =
      if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma x) else none := by
  rw [scan.eq_def]
  simp only [show ('*' == CH_GT || '*' == CH_PLUS || '*' == CH_TILDE) = false from by decide,
    show ('*' == CH_DOT) = false from by decide, show ('*' == CH_STAR) = true from by decide,
    hpe, Bool.not_false, Bool.false_eq_true, if_false, if_true]

theorem delim_other_scan_fail {cfg : ScanCfg} (st : ScanSt) {d : Char}
    (hg : (d == CH_GT || d == CH_PLUS || d == CH_TILDE) = false) (hdot : d ≠ '.') (hstar : d ≠ '*')
    (x : List Component) :
    scan cfg st (.tok (.delim d) :: x) =
      if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma x) else none := by
  have h1 : (d == CH_DOT) = false := by simp [CH_DOT]; exact hdot
  have h2 : (d == CH_STAR) = false := by simp [CH_STAR]; exact hstar
  rw [scan.eq_def]
  simp only [hg, h1, h2, Bool.false_eq_true, if_false]

theorem pieceRel_is {cfg : ScanCfg} {name : String} {args : List Component} {l : List Complex}
    {s : Simple} (hn : (asciiLowercase name = "is" ∧ s = .isSel l) ∨
      (asciiLowercase name = "where" ∧ s = .whereSel l))
    (hl : SelListRel (innerCfg true false cfg.inHas) args l) :
    PieceRel cfg [.tok .colon, .func name args] s := by
  rw [PieceRel]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨name, args, rfl, l, hn, hl⟩))))

theorem pieceRel_not {cfg : ScanCfg} {name : String} {args : List Component} {l : List Complex}
    (hn : asciiLowercase name = "not") (hl : SelListRel (innerCfg false false cfg.inHas) args l) :
    PieceRel cfg [.tok .colon, .func name args] (.notSel l) := by
  rw [PieceRel]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨name, args, rfl, l, hn, rfl, hl⟩)))))

theorem pieceRel_has {cfg : ScanCfg} {name : String} {args : List Component} {l : List Complex}
    (hn : asciiLowercase name = "has") (hin : cfg.inHas = false)
    (hl : SelListRel (innerCfg false true true) args l) :
    PieceRel cfg [.tok .colon, .func name args] (.has l) := by
  rw [PieceRel]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨name, args, rfl, l, hn, hin, rfl, hl⟩))))))

theorem pieceRel_nth_none {cfg : ScanCfg} {name : String} {args : List Component} {kind : NthKind}
    {ofA : Bool} {ab : AnB} (hn : NthName name kind ofA) (hno : ∀ m ∈ args, isOfIdent m = false)
    (hab : AnBFull args ab) :
    PieceRel cfg [.tok .colon, .func name args] (.nth kind ab none) := by
  rw [PieceRel]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨name, args, kind, ofA, ab, rfl, hn, hno, hab, rfl⟩)))))))

theorem pieceRel_nth_of {cfg : ScanCfg} {name : String} {a b : List Component} {m : Component}
    {kind : NthKind} {ab : AnB} {l : List Complex} (hn : NthName name kind true)
    (hm : isOfIdent m = true) (hno : ∀ c ∈ a, isOfIdent c = false) (hab : AnBFull a ab)
    (hl : SelListRel (innerCfg false false cfg.inHas) b l) :
    PieceRel cfg [.tok .colon, .func name (a ++ m :: b)] (.nth kind ab (some l)) := by
  rw [PieceRel]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨name, a ++ m :: b, rfl, kind, ab, a, m, b, l, rfl, hn, hm, hno, hab, hl, rfl⟩)))))))

theorem nthKindOf_lower (name : String) : nthKindOf (asciiLowercase name) = nthKindOf name := by
  unfold nthKindOf; rw [asciiLowercase_idem]

theorem innerOk_mono {a b : Nat} (h : a ≤ b) (hb : InnerOk b) : InnerOk a :=
  fun cfg args hs l => hb cfg args (by omega) l

/-- `:` の後ろに func が来て、subclass selector として読めないなら失敗する。 -/
theorem scan_colon_func_fail {cfg : ScanCfg} (st : ScanSt) (name : String) (args rest : List Component)
    (hih : InnerOk (csize [Component.tok .colon, .func name args]))
    (hno : ∀ s, ¬ PieceRel cfg [.tok .colon, .func name args] s) :
    scan cfg st (.tok .colon :: .func name args :: rest) =
      if cfg.forgiving = true then scan cfg (initSt cfg st.done) (dropToComma rest) else none := by
  have hcs := csize_func_args name args
  rw [scan.eq_def]
  simp only
  by_cases hiw : (asciiLowercase name == "is" || asciiLowercase name == "where") = true
  · rw [if_pos hiw]
    have hn : asciiLowercase name = "is" ∨ asciiLowercase name = "where" := by simpa using hiw
    cases hsc : scan { forgiving := true, relative := false, inHas := cfg.inHas }
        (initSt { forgiving := true, relative := false, inHas := cfg.inHas } []) args with
    | none => rfl
    | some l =>
      exfalso
      have hl := (hih (innerCfg true false cfg.inHas) args hcs l).mp hsc
      rcases hn with hn | hn
      · exact hno _ (pieceRel_is (Or.inl ⟨hn, rfl⟩) hl)
      · exact hno _ (pieceRel_is (Or.inr ⟨hn, rfl⟩) hl)
  rw [if_neg hiw]
  by_cases hnot : (asciiLowercase name == "not") = true
  · rw [if_pos hnot]
    have hn : asciiLowercase name = "not" := by simpa using hnot
    cases hsc : scan { forgiving := false, relative := false, inHas := cfg.inHas }
        (initSt { forgiving := false, relative := false, inHas := cfg.inHas } []) args with
    | none => rfl
    | some l => exact absurd (pieceRel_not hn ((hih _ args hcs l).mp hsc)) (hno _)
  rw [if_neg hnot]
  by_cases hhas : (asciiLowercase name == "has") = true
  · rw [if_pos hhas]
    have hn : asciiLowercase name = "has" := by simpa using hhas
    cases hin : cfg.inHas with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hsc : scan { forgiving := false, relative := true, inHas := true }
          (initSt { forgiving := false, relative := true, inHas := true } []) args with
      | none => rfl
      | some l => exact absurd (pieceRel_has hn hin ((hih _ args hcs l).mp hsc)) (hno _)
  rw [if_neg hhas]
  rw [nthKindOf_lower]
  cases hk : nthKindOf name with
  | none => rfl
  | some ko =>
    obtain ⟨kind, ofA⟩ := ko
    have hnth := (nthKindOf_iff name kind ofA).mp hk
    simp only
    split
    · next hs =>
      cases hp : parseAnBFull args with
      | none => rfl
      | some ab =>
        exact absurd (pieceRel_nth_none hnth ((splitAtOf_none_iff args).mp hs)
          ((parseAnBFull_spec args ab).mp hp)) (hno _)
    · next a b hs =>
      cases ofA with
      | false => simp
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, if_false]
        cases hp : parseAnBFull a with
        | none => rfl
        | some ab =>
          simp only
          obtain ⟨m, rfl, hm, hnoof⟩ := (splitAtOf_spec _ _ _).mp hs
          have hb : csize b < csize [Component.tok .colon, .func name (a ++ m :: b)] := by
            simp only [csize, csizeC, csize_append]; omega
          cases hsc : scan { forgiving := false, relative := false, inHas := cfg.inHas }
              (initSt { forgiving := false, relative := false, inHas := cfg.inHas } []) b with
          | none => rfl
          | some l =>
            exact absurd (pieceRel_nth_of hnth hm hnoof ((parseAnBFull_spec a ab).mp hp)
              ((hih _ b hb l).mp hsc)) (hno _)

/--
**compound の途中で、先頭が subclass selector として読めないなら、`scan` はこの項目を諦める。**

`st.parts` が空でないので、type selector（ident と `*`）も通らない。
-/
theorem scan_noPiece {cfg : ScanCfg} {c : Component} {r' : List Component}
    (hih : InnerOk (csize (c :: r'))) (hnb : NoBoundary (c :: r')) (st : ScanSt)
    (hacc : st.parts ≠ [] ∨ ((∀ n, c ≠ .tok (.ident n)) ∧ c ≠ .tok (.delim '*')))
    (hno : ∀ p rest s, c :: r' = p ++ rest → ¬ PieceRel cfg p s)
    (z : List Component) (hz : BoundaryStart z) :
    scan cfg st (c :: (r' ++ z)) = failK cfg st.done z := by
  have hr' := noBoundary_tail hnb
  have hc := noBoundary_head hnb
  cases c with
  | tok t =>
    cases t with
    | whitespace => exact absurd ws_isBoundary hc
    | comma => exact absurd (Or.inr (Or.inl rfl)) hc
    | delim d =>
      by_cases hcomb : d = '>' ∨ d = '+' ∨ d = '~'
      · exfalso; apply hc
        rcases hcomb with rfl | rfl | rfl
        · exact comb_isBoundary (k := .child) (Or.inl ⟨rfl, rfl⟩)
        · exact comb_isBoundary (k := .nextSibling) (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact comb_isBoundary (k := .subsequentSibling) (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have hg : (d == CH_GT || d == CH_PLUS || d == CH_TILDE) = false := by
        simp only [CH_GT, CH_PLUS, CH_TILDE, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro h <;> apply hcomb
        · left; rw [h]
        · right; left; rw [h]
        · right; right; rw [h]
      by_cases hdot : d = '.'
      · subst hdot
        cases r' with
        | nil =>
          rw [List.nil_append, delim_dot_scan_fail st z
            (fun n rest => not_ident_head_of_boundaryStart hz n rest)]
          rfl
        | cons c2 r'' =>
          by_cases h2 : ∃ n, c2 = .tok (.ident n)
          · obtain ⟨n, rfl⟩ := h2; exact absurd (pieceRel_cls n) (hno _ r'' _ rfl)
          · rw [List.cons_append, delim_dot_scan_fail st _
              (by intro n rest h; simp at h; exact h2 ⟨n, h.1⟩)]
            exact failK_of_noBoundary hr'
      · by_cases hstar : d = '*'
        · subst hstar
          have hpe : st.parts.isEmpty = false := by
            rcases hacc with h | h
            · cases hh : st.parts <;> simp_all
            · exact absurd rfl h.2
          rw [delim_star_scan_fail st hpe]; exact failK_of_noBoundary hr'
        · rw [delim_other_scan_fail st hg hdot hstar]; exact failK_of_noBoundary hr'
    | hash v isId =>
      cases isId with
      | true => exact absurd (pieceRel_hash v) (hno _ r' _ rfl)
      | false => rw [scan.eq_def]; simp only [Bool.false_eq_true, if_false]; exact failK_of_noBoundary hr'
    | ident n =>
      have hpe : st.parts.isEmpty = false := by
        rcases hacc with h | h
        · cases hh : st.parts <;> simp_all
        · exact absurd rfl (h.1 n)
      rw [scan.eq_def]; simp only [hpe, Bool.false_eq_true, if_false]; exact failK_of_noBoundary hr'
    | colon =>
      cases r' with
      | nil =>
        simp only [List.nil_append]
        cases z with
        | nil => rw [scan.eq_def]; simp [failK]
        | cons c z' =>
          rcases hz c rfl with rfl | rfl | ⟨d, k, rfl, _⟩ <;> (rw [scan.eq_def]; simp [failK])
      | cons c2 r'' =>
        have hr'' := noBoundary_tail hr'
        cases c2 with
        | tok t2 =>
          cases t2 with
          | ident n =>
            cases hps : simplePseudo n with
            | some s => exact absurd (pieceRel_pseudo ((simplePseudo_iff n s).mp hps)) (hno _ r'' s rfl)
            | none =>
              rw [List.cons_append, scan.eq_def]; simp only [hps]; exact failK_of_noBoundary hr''
          | _ =>
            rw [List.cons_append, scan.eq_def]; simp only
            first | exact failK_of_noBoundary hr' | exact failK_of_noBoundary hr''
        | func name args =>
          have hih' : InnerOk (csize [Component.tok .colon, .func name args]) :=
            innerOk_mono (by simp only [csize]; omega) hih
          rw [List.cons_append, scan_colon_func_fail st name args _ hih'
            (fun s hs => hno _ r'' s rfl hs)]
          exact failK_of_noBoundary hr''
        | block b items =>
          rw [List.cons_append, scan.eq_def]; simp only
          first | exact failK_of_noBoundary hr' | exact failK_of_noBoundary hr''
    | _ => rw [scan.eq_def]; simp only; exact failK_of_noBoundary hr'
  | func name args => rw [scan.eq_def]; simp only; exact failK_of_noBoundary hr'
  | block b items =>
    cases hp : parseAttrBlock items with
    | none => rw [scan.eq_def]; simp only [hp]; exact failK_of_noBoundary hr'
    | some s =>
      by_cases hb : b = .lbracket
      · subst hb
        exact absurd (pieceRel_attr ((parseAttrBlock_spec items s).mp hp)) (hno _ r' s rfl)
      · have hb' : (b == Token.lbracket) = false := by simp [hb]
        rw [scan.eq_def]; simp only [hp, hb', Bool.false_eq_true, if_false]
        exact failK_of_noBoundary hr'

/-! ## compound 一つ -/

theorem pieceRel_ne_nil {cfg : ScanCfg} {p : List Component} {s : Simple} (h : PieceRel cfg p s) :
    p ≠ [] := by
  rw [PieceRel] at h
  rcases h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ |
    ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> simp

/-- piece は ident でも `*` でも `|` でも始まらない。 -/
theorem pieceRel_head {cfg : ScanCfg} {p : List Component} {s : Simple} (h : PieceRel cfg p s) :
    ∃ c rest, p = c :: rest ∧ (∀ n, c ≠ .tok (.ident n)) ∧ c ≠ .tok (.delim '*') ∧
      c ≠ .tok (.delim '|') := by
  rw [PieceRel] at h
  rcases h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ |
    ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;>
    exact ⟨_, _, rfl, by simp, by simp, by simp⟩

/-- **subclass selector の並びが読めるなら、`scan` はそれを順に積む。** -/
theorem scan_subclasses {cfg : ScanCfg} : ∀ (n : Nat) (r : List Component) (ss : List Simple),
    r.length ≤ n → InnerOk (csize r) → SubclassesRel cfg r ss → ∀ (st : ScanSt) (w : List Component),
    scan cfg st (r ++ w) = scan cfg { st with parts := ss.reverse ++ st.parts } w
  | n, r, ss, hn, hih, h, st, w => by
    rw [SubclassesRel] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨p, rest, rfl, hne, s, ss', hp, hrest, rfl⟩
    · simp
    · cases n with
      | zero => simp at hn; exact absurd hn.1 hne
      | succ n =>
        have hlen : rest.length ≤ n := by
          rw [List.length_append] at hn; have := List.length_pos_iff.mpr hne; omega
        rw [List.append_assoc, scan_piece (innerOk_mono (by simp only [csize_append]; omega) hih) hp,
          scan_subclasses n rest ss' hlen (innerOk_mono (by simp only [csize_append]; omega) hih) hrest]
        simp

/-- **subclass selector の並びとして読めないなら、`scan` はこの項目を諦める。** -/
theorem scan_subclasses_fail {cfg : ScanCfg} : ∀ (n : Nat) (r : List Component),
    r.length ≤ n → InnerOk (csize r) → NoBoundary r → ∀ (st : ScanSt),
    (st.parts ≠ [] ∨ ∀ c rest, r = c :: rest → (∀ n, c ≠ .tok (.ident n)) ∧ c ≠ .tok (.delim '*')) →
    (¬ ∃ ss, SubclassesRel cfg r ss) → ∀ (z : List Component), BoundaryStart z →
    scan cfg st (r ++ z) = failK cfg st.done z
  | n, r, hn, hih, hnb, st, hacc, hno, z, hz => by
    cases r with
    | nil => exact absurd ⟨[], by rw [SubclassesRel]; exact Or.inl ⟨rfl, rfl⟩⟩ hno
    | cons c r' =>
      by_cases hp : ∃ p rest s, c :: r' = p ++ rest ∧ PieceRel cfg p s
      · obtain ⟨p, rest, s, hsplit, hps⟩ := hp
        have hpne := pieceRel_ne_nil hps
        cases n with
        | zero => simp at hn
        | succ n =>
          have hlen : rest.length ≤ n := by
            have := congrArg List.length hsplit; simp at this hn
            have := List.length_pos_iff.mpr hpne; omega
          have hcs : csize p ≤ csize (c :: r') ∧ csize rest ≤ csize (c :: r') := by
            rw [hsplit, csize_append]; omega
          have hrestnb : NoBoundary rest := fun x hx => hnb x (by rw [hsplit]; simp [hx])
          rw [show (c :: r') ++ z = p ++ (rest ++ z) by rw [hsplit, List.append_assoc],
            scan_piece (innerOk_mono hcs.1 hih) hps]
          have := scan_subclasses_fail n rest hlen (innerOk_mono hcs.2 hih) hrestnb
            { st with parts := s :: st.parts } (Or.inl (by simp))
            (by
              rintro ⟨ss', hss'⟩
              exact hno ⟨s :: ss', by
                rw [SubclassesRel]; exact Or.inr ⟨p, rest, hsplit, hpne, s, ss', hps, hss', rfl⟩⟩) z hz
          simpa [failK] using this
      · rw [List.cons_append]
        exact scan_noPiece hih hnb st
          (by rcases hacc with h | h; exact Or.inl h; exact Or.inr (h c r' rfl))
          (fun p rest s hs hps => hp ⟨p, rest, s, hs, hps⟩) z hz

theorem scan_ident_type {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) (n : String)
    (x : List Component) :
    scan cfg st (.tok (.ident n) :: x) = scan cfg { st with parts := [.typeSel n] } x := by
  rw [scan.eq_def]; simp [hp]

theorem scan_star_type {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) (n : String)
    (x : List Component) :
    scan cfg st (.tok (.delim '*') :: .tok (.delim '|') :: .tok (.ident n) :: x) =
      scan cfg { st with parts := [.typeSel n] } x := by
  rw [scan.eq_def]
  simp [hp, CH_GT, CH_PLUS, CH_TILDE, CH_DOT, CH_STAR, CH_PIPE]

theorem scan_star_star {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) (x : List Component) :
    scan cfg st (.tok (.delim '*') :: .tok (.delim '|') :: .tok (.delim '*') :: x) =
      scan cfg { st with parts := [.univ] } x := by
  rw [scan.eq_def]
  simp [hp, CH_GT, CH_PLUS, CH_TILDE, CH_DOT, CH_STAR, CH_PIPE]

theorem scan_star_univ {cfg : ScanCfg} (st : ScanSt) (hp : st.parts = []) (x : List Component)
    (h1 : ∀ n rest, x ≠ .tok (.delim '|') :: .tok (.ident n) :: rest)
    (h2 : ∀ rest, x ≠ .tok (.delim '|') :: .tok (.delim '*') :: rest) :
    scan cfg st (.tok (.delim '*') :: x) = scan cfg { st with parts := [.univ] } x := by
  rw [scan.eq_def]
  simp only [show ('*' == CH_GT || '*' == CH_PLUS || '*' == CH_TILDE) = false from by decide,
    show ('*' == CH_DOT) = false from by decide, show ('*' == CH_STAR) = true from by decide,
    hp, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, if_true]
  split
  · next p n rest2 =>
    by_cases hp' : p = '|'
    · subst hp'; exact absurd rfl (h1 n rest2)
    · simp [CH_PIPE, hp']
  · next p q rest2 =>
    by_cases hp' : p = '|' ∧ q = '*'
    · obtain ⟨rfl, rfl⟩ := hp'; exact absurd rfl (h2 rest2)
    · have : (p == CH_PIPE && q == CH_STAR) = false := by
        simp only [CH_PIPE, CH_STAR, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases hpp : p = '|'
        · right; intro hq; exact hp' ⟨hpp, by rw [hq]⟩
        · left; intro hpq; exact hpp (by rw [hpq])
      simp [this]
  · rfl

theorem pipe_not_boundary : ¬ IsBoundary (.tok (.delim '|')) := by
  rintro (h | h | ⟨d, k, h, hk⟩)
  · cases h
  · cases h
  · cases h; rcases hk with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)

theorem subclassesRel_head {cfg : ScanCfg} {r : List Component} {ss : List Simple}
    (h : SubclassesRel cfg r ss) : ∀ c rest, r = c :: rest →
      (∀ n, c ≠ .tok (.ident n)) ∧ c ≠ .tok (.delim '*') ∧ c ≠ .tok (.delim '|') := by
  intro c rest hr
  rw [SubclassesRel] at h
  rcases h with ⟨rfl, _⟩ | ⟨p, rest', rfl, hne, s, ss', hp, _, _⟩
  · cases hr
  · obtain ⟨c', r'', rfl, h1, h2, h3⟩ := pieceRel_head hp
    simp at hr; obtain ⟨rfl, _⟩ := hr; exact ⟨h1, h2, h3⟩

/-- `*` の後ろが `|E` でも `|*` でもない、subclass の並びと区切り。 -/
theorem star_lookahead_ok {cfg : ScanCfg} {rest z : List Component} {ss : List Simple}
    (hrest : SubclassesRel cfg rest ss) (hz : BoundaryStart z) :
    (∀ n r, rest ++ z ≠ .tok (.delim '|') :: .tok (.ident n) :: r) ∧
      (∀ r, rest ++ z ≠ .tok (.delim '|') :: .tok (.delim '*') :: r) := by
  have key : ∀ r, rest ++ z ≠ .tok (.delim '|') :: r := by
    intro r h
    cases rest with
    | nil => simp at h; exact pipe_not_boundary (hz _ (by rw [h]; rfl))
    | cons c rest' =>
      simp at h
      exact (subclassesRel_head hrest c rest' rfl).2.2 h.1
  exact ⟨fun n r h => key _ h, fun r h => key _ h⟩

/-- **compound が読めるなら、`scan` はそれを `parts` に積む。** -/
theorem scan_compound {cfg : ScanCfg} {r : List Component} {ps : List Simple}
    (hih : InnerOk (csize r)) (h : CompoundRel cfg r ps) (st : ScanSt) (hp0 : st.parts = [])
    (z : List Component) (hz : BoundaryStart z) :
    scan cfg st (r ++ z) = scan cfg { st with parts := ps.reverse } z := by
  rw [CompoundRel] at h
  rcases h with ⟨t, rest, s, ss, rfl, ht, hrest, rfl⟩ | ⟨hr, _⟩
  · have hih' : InnerOk (csize rest) := innerOk_mono (by simp only [csize_append]; omega) hih
    rw [List.append_assoc]
    rcases ht with ⟨n, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.cons_append, List.nil_append]
      rw [scan_ident_type st hp0, scan_subclasses _ rest ss (Nat.le_refl _) hih' hrest]; simp
    · simp only [List.cons_append, List.nil_append]
      obtain ⟨h1, h2⟩ := star_lookahead_ok hrest hz
      rw [scan_star_univ st hp0 _ h1 h2, scan_subclasses _ rest ss (Nat.le_refl _) hih' hrest]; simp
    · simp only [List.cons_append, List.nil_append]
      rw [scan_star_type st hp0, scan_subclasses _ rest ss (Nat.le_refl _) hih' hrest]; simp
    · simp only [List.cons_append, List.nil_append]
      rw [scan_star_star st hp0, scan_subclasses _ rest ss (Nat.le_refl _) hih' hrest]; simp
  · rw [scan_subclasses _ r ps (Nat.le_refl _) hih hr]; simp [hp0]

theorem compoundRel_type {cfg : ScanCfg} {t rest : List Component} {s : Simple} {ss : List Simple}
    (ht : TypeRel t s) (hr : SubclassesRel cfg rest ss) : CompoundRel cfg (t ++ rest) (s :: ss) := by
  rw [CompoundRel]; exact Or.inl ⟨t, rest, s, ss, rfl, ht, hr, rfl⟩

/-- **compound として読めないなら、`scan` はこの項目を諦める。** -/
theorem scan_compound_fail {cfg : ScanCfg} {r : List Component} (hih : InnerOk (csize r))
    (hnb : NoBoundary r) (hne : r ≠ []) (st : ScanSt) (hp0 : st.parts = [])
    (hno : ¬ ∃ ps, CompoundRel cfg r ps) (z : List Component) (hz : BoundaryStart z) :
    scan cfg st (r ++ z) = failK cfg st.done z := by
  obtain ⟨c, r', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hr'nb := noBoundary_tail hnb
  have hih' : InnerOk (csize r') := innerOk_mono (by simp only [csize_cons]; omega) hih
  have sub_fail : ∀ (x : List Component) (s0 : Simple), NoBoundary x → csize x ≤ csize r' →
      (¬ ∃ ss, SubclassesRel cfg x ss) →
      scan cfg { st with parts := [s0] } (x ++ z) = failK cfg st.done z := by
    intro x s0 hx hcs hnx
    have := scan_subclasses_fail _ x (Nat.le_refl _) (innerOk_mono hcs hih') hx
      { st with parts := [s0] } (Or.inl (by simp)) hnx z hz
    simpa [failK] using this
  by_cases hid : ∃ n, c = .tok (.ident n)
  · obtain ⟨n, rfl⟩ := hid
    rw [List.cons_append, scan_ident_type st hp0]
    exact sub_fail r' _ hr'nb (Nat.le_refl _)
      (fun ⟨ss, hss⟩ => hno ⟨_, compoundRel_type (t := [.tok (.ident n)]) (Or.inl ⟨n, rfl, rfl⟩) hss⟩)
  by_cases hstar : c = .tok (.delim '*')
  · subst hstar
    by_cases h3 : ∃ n r'', r' = .tok (.delim '|') :: .tok (.ident n) :: r''
    · obtain ⟨n, r'', rfl⟩ := h3
      simp only [List.cons_append]
      rw [scan_star_type st hp0]
      exact sub_fail r'' _ (noBoundary_tail (noBoundary_tail hr'nb))
        (by simp only [csize_cons]; omega)
        (fun ⟨ss, hss⟩ => hno ⟨_, compoundRel_type
          (t := [.tok (.delim '*'), .tok (.delim '|'), .tok (.ident n)])
          (Or.inr (Or.inr (Or.inl ⟨n, rfl, rfl⟩))) hss⟩)
    by_cases h4 : ∃ r'', r' = .tok (.delim '|') :: .tok (.delim '*') :: r''
    · obtain ⟨r'', rfl⟩ := h4
      simp only [List.cons_append]
      rw [scan_star_star st hp0]
      exact sub_fail r'' _ (noBoundary_tail (noBoundary_tail hr'nb))
        (by simp only [csize_cons]; omega)
        (fun ⟨ss, hss⟩ => hno ⟨_, compoundRel_type
          (t := [.tok (.delim '*'), .tok (.delim '|'), .tok (.delim '*')])
          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hss⟩)
    rw [List.cons_append, scan_star_univ st hp0]
    · exact sub_fail r' _ hr'nb (Nat.le_refl _)
        (fun ⟨ss, hss⟩ => hno ⟨_, compoundRel_type (t := [.tok (.delim '*')])
          (Or.inr (Or.inl ⟨rfl, rfl⟩)) hss⟩)
    · intro n rest h
      cases r' with
      | nil => simp at h; exact pipe_not_boundary (hz _ (by rw [h]; rfl))
      | cons c2 r2 =>
        cases r2 with
        | nil =>
          simp at h; obtain ⟨rfl, hz'⟩ := h
          exact (hz _ (by rw [hz']; rfl)) |> fun hb => by
            rcases hb with h | h | ⟨d, k, h, _⟩ <;> cases h
        | cons c3 r3 =>
          simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact h3 ⟨n, r3, rfl⟩
    · intro rest h
      cases r' with
      | nil => simp at h; exact pipe_not_boundary (hz _ (by rw [h]; rfl))
      | cons c2 r2 =>
        cases r2 with
        | nil =>
          simp at h; obtain ⟨rfl, hz'⟩ := h
          exact (hz _ (by rw [hz']; rfl)) |> fun hb => by
            rcases hb with h | h | ⟨d, k, h, hk⟩ <;> cases h
            rcases hk with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
        | cons c3 r3 =>
          simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact h4 ⟨r3, rfl⟩
  · by_cases hp : ∃ p rest s, c :: r' = p ++ rest ∧ PieceRel cfg p s
    · obtain ⟨p, rest, s, hsplit, hps⟩ := hp
      have hcs : csize p ≤ csize (c :: r') ∧ csize rest ≤ csize r' := by
        obtain ⟨c', p', rfl, -⟩ := pieceRel_head hps
        simp only [List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, rfl⟩ := hsplit
        simp only [csize_cons, csize_append]; omega
      have hrestnb : NoBoundary rest := fun x hx => hnb x (by rw [hsplit]; simp [hx])
      rw [show (c :: r') ++ z = p ++ (rest ++ z) by rw [hsplit, List.append_assoc],
        scan_piece (innerOk_mono hcs.1 hih) hps]
      have := sub_fail rest s hrestnb hcs.2 (fun ⟨ss, hss⟩ => hno ⟨s :: ss, by
        rw [CompoundRel, hsplit]
        exact Or.inr ⟨by rw [SubclassesRel]; exact Or.inr ⟨p, rest, rfl, pieceRel_ne_nil hps, s, ss,
          hps, hss, rfl⟩, by simp⟩⟩)
      simpa [hp0] using this
    · rw [List.cons_append]
      exact scan_noPiece hih hnb st (Or.inr ⟨fun n h => hid ⟨n, h⟩, hstar⟩)
        (fun p rest s hs hps => hp ⟨p, rest, s, hs, hps⟩) z hz

end Selectors.Spec
