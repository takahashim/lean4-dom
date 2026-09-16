import Url.Parser

/-!
# 相対 URL 解決の関係仕様

base がある入力の解決結果を、state machine ではなく
**「結果の URL record が base と何を共有し、何を差し替えるか」**で書く。

`Url/Roundtrip.lean` は serialize したものを parse し直す向きの定理なので、
base を使う道（no scheme state から relative / file state へ抜ける道）を通らない。
`parseUrl input (some base)` の意味はそこにしか無いので、別に書く。

ここで書く関係は `Dom/Spec/` と同じ約束で、parser の関数を呼ばない。
percent-encode だけは仕様が §1.3 で別に定めている語彙なので `Url/Percent.lean` を使う。
-/

namespace Url.Spec

open Infra Url

/-! ## 解決結果の関係 -/

/--
base から引き継ぐ成分。

§4.4 relative state が base から写す五つ（scheme / credentials / host / port / path）で、
「相対参照は入力に書かれていない成分を base から取る」という仕様の芯である。
-/
structure Inherits (base out : Url) : Prop where
  scheme : out.scheme = base.scheme
  username : out.username = base.username
  password : out.password = base.password
  host : out.host = base.host
  port : out.port = base.port
  path : out.path = base.path

/-- `#f` の形。fragment だけが入力から来て、query までは base のままである。 -/
structure FragmentResolved (base : Url) (f : String) (out : Url) : Prop extends
    Inherits base out where
  query : out.query = base.query
  fragment : out.fragment = some f

/-- `?q` の形。query は入力から来て、**fragment は落ちる**。 -/
structure QueryResolved (base : Url) (q : String) (out : Url) : Prop extends
    Inherits base out where
  query : out.query = some q
  fragment : out.fragment = none

/-- 空入力の形。base をそのまま写し、fragment だけ落とす。 -/
structure EmptyResolved (base out : Url) : Prop extends Inherits base out where
  query : out.query = base.query
  fragment : out.fragment = none

/-! ## 入力から来る文字列 -/

/--
fragment に入る文字列。§4.4 fragment state の percent-encode を一文字ずつ当てたもの。

parser は左から `url.fragment` に足していくが、こちらは入力の側の再帰で書く。
両者が一致することは `run_fragment` の中身である。
-/
def fragmentText : List Char → String
  | [] => ""
  | c :: rest => encChar fragmentSet c ++ fragmentText rest

/-- query に入る文字列。§4.4 query state の percent-encode set は special かどうかで変わる。 -/
def queryText (special : Bool) (l : List Char) : String :=
  String.ofList (utf8PercentEncode (if special then specialQuerySet else querySet) l)

/-! ## state の走行 -/

/-- fragment state は残りの入力を percent-encode しながら fragment に足すだけである。 -/
theorem run_fragment (base : Option Url) : ∀ (l : List Char) (ctx : PCtx) (g : String),
    ctx.url.fragment = some g →
    run base .fragment l ctx = .ok { ctx.url with fragment := some (g ++ fragmentText l) } := by
  intro l
  induction l with
  | nil =>
    intro ctx g hg
    rw [run, step]
    simp [fragmentText, ← hg]
  | cons c rest ih =>
    intro ctx g hg
    rw [run, step]
    rw [ih { ctx with url := { ctx.url with fragment := some ((ctx.url.fragment.getD "")
      ++ encChar fragmentSet c) } } ((ctx.url.fragment.getD "") ++ encChar fragmentSet c) rfl]
    simp [hg, fragmentText, String.append_assoc]

/-- query state は `#` か入力の終わりまで buffer に積む。 -/
theorem run_query (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    (∀ c ∈ l, ¬ c = '#') →
    run base .query l ctx
      = .ok { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ l }) } := by
  intro l
  induction l with
  | nil => intro ctx _; rw [run, step]; simp
  | cons c rest ih =>
    intro ctx h
    rw [run, step]
    · rw [ih { ctx with buffer := ctx.buffer ++ [c] } (fun x hx => h x (by simp [hx]))]
      simp
    · exact h c (by simp)

/-! ## `#f`：fragment だけの相対参照 -/

/-- credentials を持たない URL の username と password は空文字列である。 -/
theorem credentials_empty {u : Url} (h : u.includesCredentials = false) :
    u.username = "" ∧ u.password = "" := by
  simp only [Url.includesCredentials, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  exact ⟨String.isEmpty_toSlice_iff.mp h.1, String.isEmpty_toSlice_iff.mp h.2⟩

/--
**`#f` は base の全成分を引き継ぎ、fragment だけを差し替える。**

no scheme state からの三つの道（opaque path の base、relative state、file state）が
どれも同じ結果に合流することを言っている。opaque path の base と `file` の base では
仕様は credentials も host も写さないが、`ValidUrl` がそれらを空だと保証するので
結果は同じになる。
-/
theorem run_noScheme_fragment (b : Url) (f : List Char) (ctx : PCtx)
    (hb : ValidUrl b) (hurl : ctx.url = {}) :
    ∃ out, run (some b) .noScheme ('#' :: f) ctx = .ok out ∧
      FragmentResolved b (fragmentText f) out := by
  rw [run, step]
  rw [if_neg (by simp)]
  by_cases hop : b.hasOpaquePath = true
  · rw [if_pos hop]
    refine ⟨_, run_fragment _ f _ "" rfl, ?_⟩
    obtain ⟨hu, hp⟩ := credentials_empty (hb.opaqueNoCredentials hop)
    exact ⟨⟨rfl, by simp [hurl, hu], by simp [hurl, hp], by simp [hurl, hb.opaqueNoHost hop],
      by simp [hurl, hb.opaqueNoPort hop], rfl⟩, rfl, by simp⟩
  · rw [if_neg hop]
    by_cases hf : b.scheme = "file"
    · rw [if_neg (by simp [hf])]
      rw [run, step]
      rw [if_neg (by simp)]
      rw [if_pos (by simp [hf])]
      refine ⟨_, run_fragment _ f _ "" rfl, ?_⟩
      obtain ⟨hu, hp⟩ := credentials_empty (hb.fileNoCredentials hf)
      exact ⟨⟨by simp [hf], by simp [hurl, hu], by simp [hurl, hp], rfl,
        by simp [hurl, hb.fileNoPort hf], rfl⟩, rfl, by simp⟩
    · rw [if_pos (by simpa using hf)]
      rw [run, step]
      rw [if_neg (by simp)]
      rw [if_neg (by simp)]
      exact ⟨_, run_fragment _ f _ "" rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, by simp⟩

/-! ## `?q`：query だけの相対参照 -/

/--
**`?q` は base の全成分を引き継ぎ、query を差し替えて fragment を落とす。**

fragment が落ちるのは relative state が base の fragment を写さないからで、
`#f` との違いはここにある。
-/
theorem run_noScheme_query (b : Url) (q : List Char) (ctx : PCtx)
    (hb : ValidUrl b) (hurl : ctx.url = {}) (hbuf : ctx.buffer = [])
    (hop : b.hasOpaquePath = false) (hq : ∀ c ∈ q, ¬ c = '#') :
    ∃ out, run (some b) .noScheme ('?' :: q) ctx = .ok out ∧
      QueryResolved b (queryText b.isSpecial q) out := by
  rw [run, step]
  rw [if_neg (by simp [hop])]
  rw [if_neg (by simp [hop])]
  by_cases hf : b.scheme = "file"
  · rw [if_neg (by simp [hf])]
    rw [run, step]
    rw [if_neg (by simp)]
    rw [if_pos (by simp [hf])]
    refine ⟨_, run_query _ q _ hq, ?_⟩
    obtain ⟨hu, hp⟩ := credentials_empty (hb.fileNoCredentials hf)
    refine ⟨⟨by simp [hf], by simp [hurl, hu], by simp [hurl, hp], rfl,
      by simp [hurl, hb.fileNoPort hf], rfl⟩, ?_, by simp [hurl]⟩
    simp only [queryOf, queryText, Url.isSpecial, hf, hbuf, List.nil_append, Option.getD_some]
    rfl
  · rw [if_pos (by simpa using hf)]
    rw [run, step]
    rw [if_neg (by simp)]
    rw [if_neg (by simp)]
    refine ⟨_, run_query _ q _ hq, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, by simp [hurl]⟩
    simp only [queryOf, queryText, Url.isSpecial, hbuf, List.nil_append, Option.getD_some]
    rfl

/-! ## 空入力 -/

/-- **空の相対参照は base をそのまま写し、fragment だけを落とす。** -/
theorem run_noScheme_empty (b : Url) (ctx : PCtx) (hb : ValidUrl b) (hurl : ctx.url = {})
    (hop : b.hasOpaquePath = false) :
    ∃ out, run (some b) .noScheme [] ctx = .ok out ∧ EmptyResolved b out := by
  rw [run, step]
  rw [if_neg (by simp [hop])]
  rw [if_neg (by simp [hop])]
  by_cases hf : b.scheme = "file"
  · rw [if_neg (by simp [hf])]
    rw [run, step]
    rw [if_neg (by simp)]
    rw [if_pos (by simp [hf])]
    obtain ⟨hu, hp⟩ := credentials_empty (hb.fileNoCredentials hf)
    exact ⟨_, rfl, ⟨by simp [hf], by simp [hurl, hu], by simp [hurl, hp], rfl,
      by simp [hurl, hb.fileNoPort hf], rfl⟩, rfl, by simp [hurl]⟩
  · rw [if_pos (by simpa using hf)]
    rw [run, step]
    rw [if_neg (by simp)]
    rw [if_neg (by simp)]
    exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, by simp [hurl]⟩

/-! ## 入口 -/

/-- scheme start state は ASCII alpha でない先頭文字を no scheme state へ渡す。 -/
private theorem parse_noScheme_of_not_alpha {input : String} {b : Url} {a : Char}
    {l : List Char} {toAscii : List Char → Option String}
    (hp : preprocess input = a :: l) (ha : isAsciiAlpha a = false) :
    basicUrlParse input (some b) toAscii
      = (match run (some b) .noScheme (a :: l) { url := {}, toAscii } with
          | .ok u => some u | _ => none) := by
  unfold basicUrlParse
  rw [hp, run, step]
  rw [if_neg (by simp [ha])]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  cases h : run (some b) .noScheme (a :: l) { url := {}, toAscii } <;> simp

/-- **入口から見た `#f`。** -/
theorem basicUrlParse_fragment {input : String} {b : Url} {f : List Char}
    {toAscii : List Char → Option String} (hb : ValidUrl b)
    (hp : preprocess input = '#' :: f) :
    ∃ out, basicUrlParse input (some b) toAscii = some out ∧
      FragmentResolved b (fragmentText f) out := by
  obtain ⟨out, hrun, hres⟩ := run_noScheme_fragment b f { url := {}, toAscii } hb rfl
  exact ⟨out, by rw [parse_noScheme_of_not_alpha hp (by decide), hrun], hres⟩

/-- **入口から見た `?q`。** -/
theorem basicUrlParse_query {input : String} {b : Url} {q : List Char}
    {toAscii : List Char → Option String} (hb : ValidUrl b)
    (hop : b.hasOpaquePath = false) (hq : ∀ c ∈ q, ¬ c = '#')
    (hp : preprocess input = '?' :: q) :
    ∃ out, basicUrlParse input (some b) toAscii = some out ∧
      QueryResolved b (queryText b.isSpecial q) out := by
  obtain ⟨out, hrun, hres⟩ := run_noScheme_query b q { url := {}, toAscii } hb rfl rfl hop hq
  exact ⟨out, by rw [parse_noScheme_of_not_alpha hp (by decide), hrun], hres⟩

/-- **入口から見た空入力。** -/
theorem basicUrlParse_empty {input : String} {b : Url}
    {toAscii : List Char → Option String} (hb : ValidUrl b)
    (hop : b.hasOpaquePath = false) (hp : preprocess input = []) :
    ∃ out, basicUrlParse input (some b) toAscii = some out ∧ EmptyResolved b out := by
  obtain ⟨out, hrun, hres⟩ := run_noScheme_empty b { url := {}, toAscii } hb rfl hop
  refine ⟨out, ?_, hres⟩
  unfold basicUrlParse
  rw [hp, run, step]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false]
  rw [hrun]

/-! ## 証人

`http://a/b` を base にして三つの形をそれぞれ確かめる。前提の `ValidUrl` は
`checkValidUrl` で落ちる。
-/

private def exBase : Url := { scheme := "http", host := some (.domain "a"), path := .list ["b"] }

/-- `#f` は base をそのまま引き継ぐ。 -/
example : ∃ out, basicUrlParse "#f" (some exBase) = some out ∧
    FragmentResolved exBase (fragmentText ['f']) out :=
  basicUrlParse_fragment ((checkValidUrl_iff _).mp (by decide)) rfl

/-- `?q` は query を差し替え、fragment を落とす。 -/
example : ∃ out, basicUrlParse "?q" (some exBase) = some out ∧
    QueryResolved exBase (queryText true ['q']) out :=
  basicUrlParse_query ((checkValidUrl_iff _).mp (by decide)) rfl (by decide) rfl

/-- 空入力は base から fragment だけを落とす。 -/
example : ∃ out, basicUrlParse "" (some exBase) = some out ∧ EmptyResolved exBase out :=
  basicUrlParse_empty ((checkValidUrl_iff _).mp (by decide)) rfl rfl

end Url.Spec
