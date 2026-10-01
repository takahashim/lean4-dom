import Selectors.Spec.Attr
import Selectors.Spec.AnB

/-!
# selector の文法の関係仕様（Selectors Level 4 §18・§19.1）

`Selectors/Parser.lean` の `scan` は component 列を一度だけ左から読む状態機械で、
組み立て中の compound（`parts`）、その左側（`cur`）、保留中の combinator（`pend`）を持ち回る。
ここでは同じ受理・拒否を、**状態を持たない文法**として書く。

| 関係 | 本文 |
| --- | --- |
| `SelListRel` | `<selector-list>` / `<forgiving-selector-list>` / `<relative-selector-list>`。top-level の `,` で項目に分け、strict なら全項目が読めること、forgiving なら読める項目だけを残す（§18.1） |
| `ItemRel` | 一つの `<complex-selector>`（relative なら `<relative-selector>`）。先頭の空白（と relative の先頭の combinator）のあとに compound が来る |
| `TailRel` | 残り。空白だけで終わるか、separator と compound が来て続く。separator は空白の並び（descendant）か、空白を挟んでよい `>` `+` `~` |
| `CompoundRel` | `<compound-selector>`。type selector が高々一つ先頭に来て、subclass selector が続く。空ではない |
| `PieceRel` | subclass selector 一つ。id・class・attribute・pseudo-class（`:is()` `:where()` `:not()` `:has()` `:nth-*()` は中の selector list へ再帰する） |

関係は `scan` の状態を一切持たない。区切りと項目の分け方は「列がこう分かれる」という等式で書いた。

## model の範囲（`docs/selectors-spec-version.md` と同じ）

* namespace prefix は `*|E` と `*|*` だけを読む（どちらも namespace を問わない）。`ns|E` と `|E` は読めない。
* pseudo-element は読めない。
* pseudo-class は `simplePseudo` と `nthKindOf` の表にあるものと、`:is()` `:where()` `:not()` `:has()` だけ。

forgiving な list は「読めない項目を落とす」ので否定を含む。そのため帰納的な関係ではなく、
component 列の大きさに沿った再帰で定義した Prop にしてある。
-/

namespace Selectors.Spec

open Selectors Infra

/-- 空白 token。 -/
def IsWs (c : Component) : Prop := c = .tok .whitespace

/-- 列がすべて空白。 -/
def AllWs (l : List Component) : Prop := ∀ c ∈ l, IsWs c

/-- top-level の `,` で列を分けた項目。項目の中に top-level の `,` は無い。 -/
def CommaItems (cs : List Component) (items : List (List Component)) : Prop :=
  cs = [Component.tok .comma].intercalate items ∧ items ≠ [] ∧ ∀ it ∈ items, ∀ c ∈ it, c ≠ .tok .comma

/-- §16 の combinator を表す delim。 -/
def CombDelim (d : Char) (k : Combinator) : Prop :=
  (d = '>' ∧ k = .child) ∨ (d = '+' ∧ k = .nextSibling) ∨ (d = '~' ∧ k = .subsequentSibling)

/--
compound と compound の間。空白だけの並び（descendant）か、前後に空白を置いてよい
`>` `+` `~` のどれか一つ。
-/
def SepRel (sep : List Component) (k : Combinator) : Prop :=
  (sep ≠ [] ∧ AllWs sep ∧ k = .descendant) ∨
  (∃ w1 d w2, sep = w1 ++ .tok (.delim d) :: w2 ∧ AllWs w1 ∧ AllWs w2 ∧ CombDelim d k)

/-- §5.1 の type selector と universal selector。`*|E` と `*|*` は namespace を問わない。 -/
def TypeRel (t : List Component) (s : Simple) : Prop :=
  (∃ n, t = [.tok (.ident n)] ∧ s = .typeSel n) ∨
  (t = [.tok (.delim '*')] ∧ s = .univ) ∨
  (∃ n, t = [.tok (.delim '*'), .tok (.delim '|'), .tok (.ident n)] ∧ s = .typeSel n) ∨
  (t = [.tok (.delim '*'), .tok (.delim '|'), .tok (.delim '*')] ∧ s = .univ)

/-- 引数を取らない pseudo-class の名前（ASCII 大文字小文字を区別しない）。 -/
def PseudoName (n : String) (s : Simple) : Prop :=
  (asciiLowercase n = "root" ∧ s = .root) ∨ (asciiLowercase n = "empty" ∧ s = .empty) ∨
  (asciiLowercase n = "first-child" ∧ s = .firstChild) ∨
  (asciiLowercase n = "last-child" ∧ s = .lastChild) ∨
  (asciiLowercase n = "only-child" ∧ s = .onlyChild) ∨
  (asciiLowercase n = "first-of-type" ∧ s = .firstOfType) ∨
  (asciiLowercase n = "last-of-type" ∧ s = .lastOfType) ∨
  (asciiLowercase n = "only-of-type" ∧ s = .onlyOfType) ∨
  (asciiLowercase n = "scope" ∧ s = .scope)

/-- `:nth-*()` の名前と、`of S` を取れるか（§14.4-§14.7）。 -/
def NthName (n : String) (kind : NthKind) (ofAllowed : Bool) : Prop :=
  (asciiLowercase n = "nth-child" ∧ kind = .child ∧ ofAllowed = true) ∨
  (asciiLowercase n = "nth-last-child" ∧ kind = .lastChild ∧ ofAllowed = true) ∨
  (asciiLowercase n = "nth-of-type" ∧ kind = .ofType ∧ ofAllowed = false) ∨
  (asciiLowercase n = "nth-last-of-type" ∧ kind = .lastOfType ∧ ofAllowed = false)

/-- 列が丸ごと `<an+b>` である（後ろには空白しか残らない）。 -/
def AnBFull (l : List Component) (ab : AnB) : Prop :=
  ∃ r, AnBSyntax l ab r ∧ dropWs r = []

/-! ## 大きさの道具（停止性） -/

theorem csize_append : ∀ (a b : List Component), csize (a ++ b) = csize a + csize b
  | [], b => by simp [csize]
  | c :: a, b => by rw [List.cons_append, csize_cons, csize_cons, csize_append a b]; omega

theorem csize_pos_of_ne_nil : ∀ {l : List Component}, l ≠ [] → 0 < csize l
  | [], h => absurd rfl h
  | c :: _, _ => by rw [csize_cons]; have := csizeC_pos c; omega

theorem csize_le_of_mem_intercalate (sep : List Component) :
    ∀ (xs : List (List Component)) (it : List Component), it ∈ xs →
      csize it ≤ csize (sep.intercalate xs)
  | [], _, h => absurd h (by simp)
  | [x], it, h => by simp at h; subst h; simp
  | x :: y :: rest, it, h => by
    rw [List.intercalate_cons_cons, csize_append, csize_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := csize_le_of_mem_intercalate sep (y :: rest) it h; omega

theorem lex_of_le {a b r s : Nat} (h : a ≤ b) (hr : r < s) :
    Prod.Lex (· < ·) (· < ·) (a, r) (b, s) := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact Prod.Lex.left _ _ h'
  · have : a = b := by omega
    subst this
    exact Prod.Lex.right _ hr

theorem lex_of_lt {a b r s : Nat} (h : a < b) : Prod.Lex (· < ·) (· < ·) (a, r) (b, s) :=
  Prod.Lex.left _ _ h

/-- 中の selector list を読む設定。 -/
def innerCfg (forgiving relative inHas : Bool) : ScanCfg :=
  { forgiving := forgiving, relative := relative, inHas := inHas }

/-- relative selector の先頭の combinator（あれば）。relative でなければ何も置けない。 -/
def LeadRel (cfg : ScanCfg) (lead : List Component) (lk : Option Combinator) : Prop :=
  (lead = [] ∧ lk = none) ∨
  (∃ d k w, lead = .tok (.delim d) :: w ∧ AllWs w ∧ CombDelim d k ∧ cfg.relative = true ∧
    lk = some k)

/--
最初の compound が作る complex selector。relative selector では、左に `:has()` の anchor を
先頭の combinator（無ければ descendant）で置く。
-/
def BaseComplex (cfg : ScanCfg) (lk : Option Combinator) (parts : List Simple) : Complex :=
  if cfg.relative then .seq parts (lk.getD .descendant) (.one [.anchor]) else .one parts

mutual

/--
§18 の selector list。top-level の `,` で項目に分け、strict なら全項目、forgiving なら
読める項目だけを、順に並べたものが `l`。
-/
def SelListRel (cfg : ScanCfg) (cs : List Component) (l : List Complex) : Prop :=
  ∃ items, ∃ _h : CommaItems cs items, ∃ res : List (Option Complex),
    res.length = items.length ∧
    (∀ p ∈ items.attach.zip res,
        match p.2 with
        | some c => ItemRel cfg p.1.1 c
        | none => cfg.forgiving = true ∧ ¬ ∃ c, ItemRel cfg p.1.1 c) ∧
    l = res.filterMap id
termination_by (csize cs, 5)
decreasing_by
  all_goals simp_wf
  all_goals exact lex_of_le (_h.1 ▸ csize_le_of_mem_intercalate _ items _ p.1.2) (by omega)

/--
一つの項目（`<complex-selector>`、relative なら `<relative-selector>`）。
先頭の空白と先頭の combinator のあとに compound が一つ来て、残りは `TailRel` が読む。
-/
def ItemRel (cfg : ScanCfg) (it : List Component) (c : Complex) : Prop :=
  ∃ w1 lead r rest, ∃ _h : it = w1 ++ lead ++ r ++ rest, ∃ lk parts,
    AllWs w1 ∧ LeadRel cfg lead lk ∧ r ≠ [] ∧ CompoundRel cfg r parts ∧
      TailRel cfg (BaseComplex cfg lk parts) rest c
termination_by (csize it, 4)
decreasing_by
  all_goals simp_wf
  all_goals exact lex_of_le (by subst _h; simp only [csize_append]; omega) (by omega)

/--
`left` まで読んだあとの残り。空白だけなら `left` が答えで、そうでなければ separator と
compound が来て、`left` の右に伸ばした complex selector で続きを読む。
-/
def TailRel (cfg : ScanCfg) (left : Complex) (x : List Component) (c : Complex) : Prop :=
  (AllWs x ∧ c = left) ∨
  (∃ sep r rest, ∃ _h : x = sep ++ r ++ rest, ∃ _hne : r ≠ [], ∃ k parts,
    SepRel sep k ∧ CompoundRel cfg r parts ∧ TailRel cfg (.seq parts k left) rest c)
termination_by (csize x, 3)
decreasing_by
  all_goals simp_wf
  · exact lex_of_le (by subst _h; simp only [csize_append]; omega) (by omega)
  · exact lex_of_lt (by subst _h; have := csize_pos_of_ne_nil _hne; simp only [csize_append]; omega)

/-- §18 の compound selector。type selector が高々一つ先頭に来て、subclass selector が続く。 -/
def CompoundRel (cfg : ScanCfg) (r : List Component) (parts : List Simple) : Prop :=
  (∃ t rest s ss, ∃ _h : r = t ++ rest, TypeRel t s ∧ SubclassesRel cfg rest ss ∧ parts = s :: ss) ∨
  (SubclassesRel cfg r parts ∧ parts ≠ [])
termination_by (csize r, 2)
decreasing_by
  all_goals simp_wf
  · exact lex_of_le (by subst _h; simp only [csize_append]; omega) (by omega)
  · exact lex_of_le (Nat.le_refl _) (by omega)

/-- subclass selector の並び。 -/
def SubclassesRel (cfg : ScanCfg) (r : List Component) (ss : List Simple) : Prop :=
  (r = [] ∧ ss = []) ∨
  (∃ p rest, ∃ _h : r = p ++ rest, ∃ _hne : p ≠ [], ∃ s ss',
    PieceRel cfg p s ∧ SubclassesRel cfg rest ss' ∧ ss = s :: ss')
termination_by (csize r, 1)
decreasing_by
  all_goals simp_wf
  · exact lex_of_le (by subst _h; simp only [csize_append]; omega) (by omega)
  · exact lex_of_lt (by subst _h; have := csize_pos_of_ne_nil _hne; simp only [csize_append]; omega)

/-- subclass selector 一つ。 -/
def PieceRel (cfg : ScanCfg) (p : List Component) (s : Simple) : Prop :=
  (∃ v, p = [.tok (.hash v true)] ∧ s = .id v) ∨
  (∃ n, p = [.tok (.delim '.'), .tok (.ident n)] ∧ s = .cls n) ∨
  (∃ items, p = [.block .lbracket items] ∧ AttrBlockSyntax items s) ∨
  (∃ n, p = [.tok .colon, .tok (.ident n)] ∧ PseudoName n s) ∨
  (∃ name args, ∃ _h : p = [.tok .colon, .func name args], ∃ l,
    ((asciiLowercase name = "is" ∧ s = .isSel l) ∨ (asciiLowercase name = "where" ∧ s = .whereSel l)) ∧
      SelListRel (innerCfg true false cfg.inHas) args l) ∨
  (∃ name args, ∃ _h : p = [.tok .colon, .func name args], ∃ l,
    asciiLowercase name = "not" ∧ s = .notSel l ∧ SelListRel (innerCfg false false cfg.inHas) args l) ∨
  (∃ name args, ∃ _h : p = [.tok .colon, .func name args], ∃ l,
    asciiLowercase name = "has" ∧ cfg.inHas = false ∧ s = .has l ∧
      SelListRel (innerCfg false true true) args l) ∨
  (∃ name args kind ofAllowed ab, p = [.tok .colon, .func name args] ∧ NthName name kind ofAllowed ∧
    (∀ m ∈ args, isOfIdent m = false) ∧ AnBFull args ab ∧ s = .nth kind ab none) ∨
  (∃ name args, ∃ _h : p = [.tok .colon, .func name args], ∃ kind ab a m b l,
    ∃ _ha : args = a ++ m :: b, NthName name kind true ∧ isOfIdent m = true ∧
      (∀ c ∈ a, isOfIdent c = false) ∧ AnBFull a ab ∧
      SelListRel (innerCfg false false cfg.inHas) b l ∧ s = .nth kind ab (some l))
termination_by (csize p, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp only [csize, csizeC, csize_append]
  all_goals exact lex_of_lt (by omega)

end

/-- §19.1 "parse a selector"。入力を component に分けて、strict な selector list として読む。 -/
def ParsesTo (input : String) (l : List Complex) : Prop :=
  ∃ cs, parseComponents input = some cs ∧ SelListRel (innerCfg false false false) cs l

end Selectors.Spec
