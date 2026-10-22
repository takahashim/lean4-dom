import Url.Spec.Path
import Url.Spec.Failure
import Url.Roundtrip.Query
import Url.Roundtrip.Canonical

/-!
# 相対参照の解決（§4.4 relative state、relative slash state、special relative or authority state）

`Url/Spec/Relative.lean` は `#f`・`?q`・空入力の三つを書いた。ここでは残りの相対参照、
**path を持つ相対参照**を書く。RFC 3986 §5.2 と同じ発想で、state machine を写さずに

1. 参照を fragment（最初の `#` の後）、query（その手前の最初の `?` の後）、path 部分に分け（`splitRef`）、
2. path 部分を `Url/Spec/Path.lean` の畳み込みで base の path に合成し、
3. scheme・credentials・host・port は base から取る

という形で書く（`refResolved`）。

| 参照の形 | 合成の起点 | 本文 |
| --- | --- | --- |
| path-relative（`g`、`../g`） | base の path を shorten したもの | relative state 2.8 |
| absolute-path（`/g`） | 空の path | relative state 2.2、relative slash state 3 |
| `http:g`（base と同じ special scheme） | path-relative と同じ | special relative or authority state 2 |

`file` の base は file state という別の道を通るので、ここでは扱わない。
-/

namespace Url.Spec

open Infra Url

/-! ## 参照を分ける -/

/-- 最初の `d` で分ける。`d` が無ければ後ろは null。 -/
def splitFirst (d : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: t => if c = d then ([], some t) else ((c :: (splitFirst d t).1), (splitFirst d t).2)

/-- **`d` を含まない前置きの後の最初の `d` で分ける。** -/
theorem splitFirst_append (d : Char) : ∀ (a r : List Char), d ∉ a →
    splitFirst d (a ++ d :: r) = (a, some r)
  | [], r, _ => by simp [splitFirst]
  | x :: a, r, h => by
    have hx : x ≠ d := fun e => h (by simp [e])
    have ih := splitFirst_append d a r (fun hm => h (List.mem_cons_of_mem _ hm))
    simp [splitFirst, hx, ih]

/-- `d` が無ければ分けない。 -/
theorem splitFirst_of_not_mem (d : Char) : ∀ (l : List Char), d ∉ l → splitFirst d l = (l, none)
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ d := fun e => h (by simp [e])
    have ih := splitFirst_of_not_mem d l (fun hm => h (List.mem_cons_of_mem _ hm))
    simp [splitFirst, hx, ih]

/-- 列は `d` を含まないか、最初の `d` の前後に一通りに分かれる。 -/
theorem first_occurrence (d : Char) : ∀ (l : List Char),
    d ∉ l ∨ ∃ a r, l = a ++ d :: r ∧ d ∉ a
  | [] => .inl (by simp)
  | x :: l => by
    by_cases hx : x = d
    · exact .inr ⟨[], l, by simp [hx], by simp⟩
    · rcases first_occurrence d l with h | ⟨a, r, rfl, ha⟩
      · exact .inl (by simp [h, Ne.symm hx])
      · exact .inr ⟨x :: a, r, rfl, by simp [ha, Ne.symm hx]⟩

/--
参照を path 部分・query・fragment に分ける。

`#` を先に切ってよいのは、query state も path state も `#` で止まり、fragment state は何でも読むからである。
`?` は `#` より前のものだけが query の始まりになる（`#` の後ろの `?` は fragment の一部）。
-/
def splitRef (l : List Char) : List Char × Option (List Char) × Option (List Char) :=
  let (a, f) := splitFirst '#' l
  let (h, q) := splitFirst '?' a
  (h, q, f)

/-- 解決した URL。scheme から port までは base、path は合成したもの、query と fragment は参照から。 -/
def refResolved (b : Url) (path : List String) (q f : Option (List Char)) : Url :=
  { b with path := .list path, query := q.map (queryText b.isSpecial),
           fragment := f.map fragmentText }

/-! ## path state から先 -/

/-- query state は `#` まで読み、fragment state へ渡す。 -/
theorem run_query_until_hash (base : Option Url) (q f : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hq : '#' ∉ q) :
    run base .query (q ++ '#' :: f) ctx
      = run base .fragment f
          { ctx with
            url := { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ q }),
                                  fragment := some "" }
            buffer := [] } := by
  rw [run_query_chunk base q _ ctx (fun c hc he => hq (he ▸ hc)), run_query_hash base f]
  exact hov

theorem queryOf_empty (ctx : PCtx) (q : List Char) (hq : ctx.url.query = some "")
    (hb : ctx.buffer = []) :
    queryOf { ctx with buffer := ctx.buffer ++ q } = queryText ctx.url.isSpecial q := by
  simp [queryOf, queryText, hq, hb]

/--
**path state から先を読み切ると、path は `resolveSegs`、query と fragment は参照の分け方どおりになる。**
-/
theorem run_path_ref (base : Option Url) (l : List Char) (ctx : PCtx) {P : List String}
    (hp : ctx.url.path = .list P) (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none) :
    run base .path l ctx
      = .ok { ctx.url with
          path := .list (resolveSegs (ctx.url.scheme == "file") P
            (pathSegments ctx.url.isSpecial (splitRef l).1))
          query := (splitRef l).2.1.map (queryText ctx.url.isSpecial)
          fragment := (splitRef l).2.2.map fragmentText } := by
  have hnq_h : ∀ {h : List Char}, '?' ∉ h → '#' ∉ h → ∀ c ∈ h, c ≠ '?' ∧ c ≠ '#' :=
    fun hq hh c hc => ⟨fun e => hq (e ▸ hc), fun e => hh (e ▸ hc)⟩
  rcases first_occurrence '#' l with hnh | ⟨a, f, rfl, hnh⟩
  · rcases first_occurrence '?' l with hnq | ⟨h, q, rfl, hnq⟩
    · simp only [splitRef, splitFirst_of_not_mem _ _ hnh, splitFirst_of_not_mem _ _ hnq]
      rw [run_path_spec base l ctx hp hov hbuf (hnq_h hnq hnh)]
      simp [hq0, hf0]
    · simp only [splitRef, splitFirst_of_not_mem _ _ hnh, splitFirst_append _ _ _ hnq]
      rw [run_path_spec_query base h q ctx hp hov hbuf
        (hnq_h hnq (fun hm => hnh (by simp [hm])))]
      rw [Spec.run_query base q _ (fun c hc e => hnh (by subst e; simp [hc]))]
      simp [queryOf, queryText, hf0, Url.isSpecial]
      rfl
  · rcases first_occurrence '?' a with hnq | ⟨h, q, rfl, hnq⟩
    · simp only [splitRef, splitFirst_append _ _ _ hnh, splitFirst_of_not_mem _ _ hnq]
      rw [run_path_spec_fragment base a f ctx hp hov hbuf (hnq_h hnq hnh)]
      rw [Spec.run_fragment base f _ "" rfl]
      simp [hq0]
    · simp only [splitRef, splitFirst_append _ _ _ hnh, splitFirst_append _ _ _ hnq]
      rw [List.append_assoc, List.cons_append, run_path_spec_query base h _ ctx hp hov hbuf
        (hnq_h hnq (fun hm => hnh (by simp [hm])))]
      rw [run_query_until_hash base q f _ (by exact hov) (fun hm => hnh (by simp [hm])),
        Spec.run_fragment base f _ "" rfl]
      · simp [queryOf, queryText, Url.isSpecial]
        rfl

/-! ## relative state から -/

/--
**path-relative 参照**（`g`、`./g`、`../g` など。先頭が区切りでも `?` でも `#` でもない）。

relative state 2.8 は base の credentials・host・port・path を写し、path を shorten してから
path state に読み直させる（query は null に戻す）。合成の起点は base の path から最後を落としたもの。
-/
theorem run_relative_pathRef (b : Url) (l : List Char) (ctx : PCtx) {Pb : List String}
    (hbp : b.path = .list Pb) (hbf : b.scheme ≠ "file")
    (hurl : ctx.url = {}) (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    {c : Char} {t : List Char} (hl : l = c :: t) (hc : isPathSep b.isSpecial c = false)
    (hq : c ≠ '?') (hh : c ≠ '#') :
    run (some b) .relative l ctx
      = .ok (refResolved b (resolveSegs false (shorten false Pb) (pathSegments b.isSpecial (splitRef l).1))
          (splitRef l).2.1 (splitRef l).2.2) := by
  have hs : c ≠ '/' := fun e => by simp [isPathSep, e] at hc
  have hbs : ¬(b.isSpecial = true ∧ c = '\\') := fun ⟨h1, h2⟩ => by simp [isPathSep, h1, h2] at hc
  subst hl
  rw [run, step]
  simp only [hurl]
  rw [if_neg (by simpa using hs), if_neg (by simpa [Url.isSpecial] using hbs)]
  have hsh : shortenPath
        { scheme := b.scheme, username := b.username, password := b.password, host := b.host,
          port := b.port, path := b.path }
      = { scheme := b.scheme, username := b.username, password := b.password, host := b.host,
          port := b.port, path := .list (shorten false Pb) } := by
    unfold shortenPath shorten
    rw [hbp]
    simp [hbf]
  rw [hsh, run_path_ref (some b) (c :: t) _ (P := shorten false Pb) rfl (by exact hov)
    (by exact hbuf) rfl rfl]
  have hbf' : (b.scheme == "file") = false := by simpa using hbf
  simp [refResolved, Url.isSpecial, hbf']

/-- relative slash state 3：区切りが続かなければ base の credentials・host・port を写して path state へ。 -/
theorem run_relativeSlash_path (b : Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = b.isSpecial)
    (hr : ∀ d t, rest = d :: t → isPathSep b.isSpecial d = false) :
    run (some b) .relativeSlash rest ctx
      = run (some b) .path rest
          { ctx with url := { ctx.url with username := b.username, password := b.password,
                                           host := b.host, port := b.port } } := by
  cases rest with
  | nil => rw [run, step]; simp
  | cons d t =>
    have hd := hr d t rfl
    simp only [isPathSep, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_imp] at hd
    rw [run, step]
    rw [if_neg (by
      simp only [hsp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.some.injEq, not_and,
        not_or]
      exact fun h => ⟨hd.1, hd.2 h⟩)]
    rw [if_neg (by simpa using hd.1)]

/--
**absolute-path 参照**（`/g`。区切りが一つだけで、次が区切りでない）。

relative state 2.2 で relative slash state へ移り、relative slash state 3 で base の credentials・host・port を
写して path state へ渡る。path は写さないので、合成の起点は空の path である。
-/
theorem run_relative_absRef (b : Url) (l : List Char) (ctx : PCtx)
    (hurl : ctx.url = {}) (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    {c : Char} {rest : List Char} (hl : l = c :: rest) (hc : isPathSep b.isSpecial c = true)
    (hr : ∀ d t, rest = d :: t → isPathSep b.isSpecial d = false) (hbf : b.scheme ≠ "file") :
    run (some b) .relative l ctx
      = .ok (refResolved b (resolveSegs false [] (pathSegments b.isSpecial (splitRef rest).1))
          (splitRef rest).2.1 (splitRef rest).2.2) := by
  subst hl
  have hbf' : (b.scheme == "file") = false := by simpa using hbf
  have hgo : run (some b) .relative (c :: rest) ctx
      = run (some b) .relativeSlash rest { ctx with url := { ({} : Url) with scheme := b.scheme } } := by
    rw [run, step]
    simp only [hurl]
    simp only [isPathSep, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hc
    rcases hc with rfl | ⟨hsp, rfl⟩
    · simp
    · simp [Url.isSpecial, ← hsp]
  rw [hgo, run_relativeSlash_path b rest _ rfl hr]
  rw [run_path_ref (some b) rest _ (P := []) rfl (by exact hov) (by exact hbuf) rfl rfl]
  simp [refResolved, Url.isSpecial, hbf']

/-! ## 入口から -/

/-- no scheme state 4：opaque path でも `file` でもない base では relative state へ進む。 -/
theorem run_noScheme_relative (b : Url) (l : List Char) (ctx : PCtx)
    (hop : b.hasOpaquePath = false) (hbf : b.scheme ≠ "file") :
    run (some b) .noScheme l ctx = run (some b) .relative l ctx := by
  have hbf' : (b.scheme != "file") = true := by simpa using hbf
  cases l with
  | nil => rw [run, step]; simp [hop, hbf']
  | cons c t => rw [run, step]; simp [hop, hbf']

/-- scheme の無い入力は、no scheme state が返したものがそのまま parse の結果になる。 -/
theorem basicUrlParse_of_noScheme {input : String} {b : Url} {out : Url}
    {toAscii : List Char → Option String} (hs : ¬ HasScheme (preprocess input))
    (h : run (some b) .noScheme (preprocess input) { url := {}, toAscii } = .ok out) :
    basicUrlParse input (some b) toAscii = some out := by
  unfold basicUrlParse
  rcases run_schemeStart_cases (some b) (preprocess input) { url := {}, toAscii } rfl hs with hc | hc
  · rw [hc]; simp [h]
  · rw [hc, h]

/--
**入口から見た path-relative 参照。** 結果は base の scheme・credentials・host・port と、
base の path を shorten したところから参照の path を畳んだ path、参照の query と fragment である。
-/
theorem basicUrlParse_pathRef {input : String} {b : Url} {Pb : List String}
    {toAscii : List Char → Option String}
    (hbp : b.path = .list Pb) (hbf : b.scheme ≠ "file")
    {c : Char} {t : List Char} (hp : preprocess input = c :: t) (hs : ¬ HasScheme (c :: t))
    (hc : isPathSep b.isSpecial c = false) (hq : c ≠ '?') (hh : c ≠ '#') :
    basicUrlParse input (some b) toAscii
      = some (refResolved b
          (resolveSegs false (shorten false Pb) (pathSegments b.isSpecial (splitRef (c :: t)).1))
          (splitRef (c :: t)).2.1 (splitRef (c :: t)).2.2) := by
  have hop : b.hasOpaquePath = false := by simp [Url.hasOpaquePath, hbp, Path.isOpaque]
  refine basicUrlParse_of_noScheme (by rw [hp]; exact hs) ?_
  rw [hp, run_noScheme_relative b _ _ hop hbf]
  exact run_relative_pathRef b _ _ hbp hbf rfl rfl rfl rfl hc hq hh

/-- **入口から見た absolute-path 参照。** path は空のところから参照の path を畳む。 -/
theorem basicUrlParse_absRef {input : String} {b : Url}
    {toAscii : List Char → Option String}
    (hop : b.hasOpaquePath = false) (hbf : b.scheme ≠ "file")
    {c : Char} {rest : List Char} (hp : preprocess input = c :: rest)
    (hc : isPathSep b.isSpecial c = true)
    (hr : ∀ d t, rest = d :: t → isPathSep b.isSpecial d = false) :
    basicUrlParse input (some b) toAscii
      = some (refResolved b (resolveSegs false [] (pathSegments b.isSpecial (splitRef rest).1))
          (splitRef rest).2.1 (splitRef rest).2.2) := by
  have hs : ¬ HasScheme (c :: rest) := by
    rintro ⟨a, pre, tail, he, ha, _⟩
    simp only [List.cons.injEq] at he
    rw [← he.1] at ha
    simp only [isPathSep, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hc
    rcases hc with rfl | ⟨_, rfl⟩ <;> revert ha <;> decide
  refine basicUrlParse_of_noScheme (by rw [hp]; exact hs) ?_
  rw [hp, run_noScheme_relative b _ _ hop hbf]
  exact run_relative_absRef b _ _ rfl rfl rfl rfl hc hr hbf

/-! ## base と同じ special scheme（`http:g`） -/

/-- special relative or authority state 2：`//` が続かなければ relative state で読み直す。 -/
theorem run_specialRelativeOrAuthority_relative (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hr : ∀ r2, rest ≠ '/' :: '/' :: r2) :
    run base .specialRelativeOrAuthority rest ctx = run base .relative rest ctx := by
  cases rest with
  | nil => rw [run, step]; intro _ h; cases h
  | cons d t =>
    rw [run, step]
    intro r2 hd ht
    simp only [Option.some.injEq] at hd
    exact hr r2 (by rw [hd, ht])

/-- relative state が見る url は scheme を上書きした後のものだけである。 -/
theorem run_relative_scheme_irrelevant (b : Url) (l : List Char) (ctx : PCtx) (s : String) :
    run (some b) .relative l { ctx with url := { scheme := s } }
      = run (some b) .relative l { ctx with url := {} } := by
  cases l with
  | nil =>
    rw [run, step]
    conv => rhs; rw [run, step]
  | cons c t =>
    rw [run, step]
    conv => rhs; rw [run, step]

/--
**scheme が base と同じ special scheme で `//` が続かない入力は、scheme を外した参照として解決する。**

scheme state 2.6 が special relative or authority state へ渡し、そこで relative state に読み直させる。
relative state は scheme を base のもので上書きするので、scheme state が書いた scheme は残らない。
-/
theorem basicUrlParse_sameScheme {input : String} {b out : Url}
    {toAscii : List Char → Option String} {a : Char} {pre rest : List Char}
    (hp : preprocess input = a :: (pre ++ ':' :: rest)) (ha : isAsciiAlpha a = true)
    (hpre : ∀ c ∈ pre, schemeChar c = true)
    (hsch : String.ofList ((a :: pre).map asciiLowerChar) = b.scheme)
    (hsp : b.isSpecial = true) (hbf : b.scheme ≠ "file")
    (hr : ∀ r2, rest ≠ '/' :: '/' :: r2)
    (h : run (some b) .relative rest { url := {}, toAscii } = .ok out) :
    basicUrlParse input (some b) toAscii = some out := by
  have hrun : run (some b) .schemeStart (a :: (pre ++ ':' :: rest)) { url := {}, toAscii }
      = run (some b) .relative rest { url := {}, toAscii } := by
    rw [run, step, if_pos ha, run_scheme_prefix (some b) pre _ _ hpre]
    rw [run, step]
    have hsch' : String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) = b.scheme := by
      simpa using hsch
    have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
      decide
    simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
      List.cons_append, hsch', hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
    have hsp' : isSpecialScheme b.scheme = true := hsp
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, Url.isSpecial, hsp', Bool.and_self,
      if_true]
    rw [if_neg (by simpa using hbf), run_specialRelativeOrAuthority_relative _ _ _ hr,
      run_relative_scheme_irrelevant b rest { url := {}, toAscii } b.scheme]
  unfold basicUrlParse
  rw [hp, hrun, h]

/-! ## 前処理した入力で書いた形

具体的な入力で使うための形。`c` と `t` を前処理の結果から取る。
-/

/-- path-relative 参照の始まり。空でなく、先頭が区切りでも `?` でも `#` でもない。 -/
def pathRefStart (special : Bool) : List Char → Bool
  | c :: _ => !isPathSep special c && c != '?' && c != '#'
  | [] => false

/-- absolute-path 参照の始まり。先頭が区切りで、次が区切りでない。 -/
def absRefStart (special : Bool) : List Char → Bool
  | c :: rest => isPathSep special c && (match rest with | d :: _ => !isPathSep special d | [] => true)
  | [] => false

theorem basicUrlParse_pathRef' {input : String} {b : Url} {Pb : List String}
    {toAscii : List Char → Option String}
    (hbp : b.path = .list Pb) (hbf : b.scheme ≠ "file")
    (hst : pathRefStart b.isSpecial (preprocess input) = true)
    (hs : ¬ HasScheme (preprocess input)) :
    basicUrlParse input (some b) toAscii
      = some (refResolved b
          (resolveSegs false (shorten false Pb) (pathSegments b.isSpecial (splitRef (preprocess input)).1))
          (splitRef (preprocess input)).2.1 (splitRef (preprocess input)).2.2) := by
  cases hp : preprocess input with
  | nil => rw [hp] at hst; simp [pathRefStart] at hst
  | cons c t =>
    rw [hp] at hst hs
    simp only [pathRefStart, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hst
    exact basicUrlParse_pathRef hbp hbf hp hs hst.1.1 hst.1.2 hst.2

theorem basicUrlParse_absRef' {input : String} {b : Url}
    {toAscii : List Char → Option String}
    (hop : b.hasOpaquePath = false) (hbf : b.scheme ≠ "file")
    (hst : absRefStart b.isSpecial (preprocess input) = true) :
    basicUrlParse input (some b) toAscii
      = some (refResolved b
          (resolveSegs false [] (pathSegments b.isSpecial (splitRef (preprocess input).tail).1))
          (splitRef (preprocess input).tail).2.1 (splitRef (preprocess input).tail).2.2) := by
  cases hp : preprocess input with
  | nil => rw [hp] at hst; simp [absRefStart] at hst
  | cons c rest =>
    rw [hp] at hst
    simp only [absRefStart, Bool.and_eq_true] at hst
    refine basicUrlParse_absRef hop hbf hp hst.1 ?_
    rintro d t rfl
    simpa using hst.2

/-! ## 証人：RFC 3986 §5.4 の例

base は `http://a/b/c/d;p?q`。どれも URL Standard でも同じ結果になる（WPT の `urltestdata.json` にも入っている）。
証明は解決の定理で関係の側へ移し、関係の側の関数を `decide` で計算する。parser は計算しない。
-/

private def rfcBase : Url :=
  { scheme := "http", host := some (.domain "a"), path := .list ["b", "c", "d;p"], query := some "q" }

private def rfcOut (path : List String) (q f : Option String := none) : Url :=
  { scheme := "http", host := some (.domain "a"), path := .list path, query := q, fragment := f }

/-- 具体的な path-relative 参照を解決の定理で閉じる。 -/
macro "path_ref" : tactic => `(tactic|
  (rw [basicUrlParse_pathRef' rfl (by decide) (by decide) (not_hasScheme_of_no_colon (by decide))]
   decide))

/-- 具体的な absolute-path 参照を解決の定理で閉じる。 -/
macro "abs_ref" : tactic => `(tactic|
  (rw [basicUrlParse_absRef' rfl (by decide) (by decide)]
   decide))

example : basicUrlParse "g" (some rfcBase) = some (rfcOut ["b", "c", "g"]) := by path_ref
example : basicUrlParse "./g" (some rfcBase) = some (rfcOut ["b", "c", "g"]) := by path_ref
example : basicUrlParse "g/" (some rfcBase) = some (rfcOut ["b", "c", "g", ""]) := by path_ref
example : basicUrlParse "/g" (some rfcBase) = some (rfcOut ["g"]) := by abs_ref
example : basicUrlParse "g?y" (some rfcBase) = some (rfcOut ["b", "c", "g"] (some "y")) := by
  path_ref
example : basicUrlParse "g#s" (some rfcBase) = some (rfcOut ["b", "c", "g"] none (some "s")) := by
  path_ref
example : basicUrlParse "g?y#s" (some rfcBase)
    = some (rfcOut ["b", "c", "g"] (some "y") (some "s")) := by path_ref
example : basicUrlParse ";x" (some rfcBase) = some (rfcOut ["b", "c", ";x"]) := by path_ref
example : basicUrlParse "." (some rfcBase) = some (rfcOut ["b", "c", ""]) := by path_ref
example : basicUrlParse "./" (some rfcBase) = some (rfcOut ["b", "c", ""]) := by path_ref
example : basicUrlParse ".." (some rfcBase) = some (rfcOut ["b", ""]) := by path_ref
example : basicUrlParse "../g" (some rfcBase) = some (rfcOut ["b", "g"]) := by path_ref
example : basicUrlParse "../.." (some rfcBase) = some (rfcOut [""]) := by path_ref
example : basicUrlParse "../../g" (some rfcBase) = some (rfcOut ["g"]) := by path_ref

/-! §5.4.2 の abnormal examples。`..` は path の根で止まり、`.` と `..` の形をした別の名前は畳まない。 -/

example : basicUrlParse "../../../g" (some rfcBase) = some (rfcOut ["g"]) := by path_ref
example : basicUrlParse "/./g" (some rfcBase) = some (rfcOut ["g"]) := by abs_ref
example : basicUrlParse "/../g" (some rfcBase) = some (rfcOut ["g"]) := by abs_ref
example : basicUrlParse "g." (some rfcBase) = some (rfcOut ["b", "c", "g."]) := by path_ref
example : basicUrlParse "..g" (some rfcBase) = some (rfcOut ["b", "c", "..g"]) := by path_ref
example : basicUrlParse "./g/." (some rfcBase) = some (rfcOut ["b", "c", "g", ""]) := by path_ref
example : basicUrlParse "g/../h" (some rfcBase) = some (rfcOut ["b", "c", "h"]) := by path_ref
example : basicUrlParse "g;x=1/../y" (some rfcBase) = some (rfcOut ["b", "c", "y"]) := by path_ref
example : basicUrlParse "g?y/./x" (some rfcBase) = some (rfcOut ["b", "c", "g"] (some "y/./x")) := by
  path_ref
example : basicUrlParse "g#s/../x" (some rfcBase)
    = some (rfcOut ["b", "c", "g"] none (some "s/../x")) := by path_ref

/-! URL Standard に固有のもの。`%2e` も dot として畳み、special な URL では `\` も区切りである。 -/

example : basicUrlParse "%2e%2E/g" (some rfcBase) = some (rfcOut ["b", "g"]) := by path_ref
example : basicUrlParse "g\\..\\h" (some rfcBase) = some (rfcOut ["b", "c", "h"]) := by path_ref
example : basicUrlParse "\\g" (some rfcBase) = some (rfcOut ["g"]) := by abs_ref

/--
`http:g` は base と同じ special scheme なので、`g` と同じに解決する（§5.4.1 の最後の例は
「strict な parser なら `http:g`、後方互換なら `http://a/b/c/g`」としていて、URL Standard は後者）。
-/
example : basicUrlParse "http:g" (some rfcBase) = some (rfcOut ["b", "c", "g"]) :=
  basicUrlParse_sameScheme (a := 'h') (pre := ['t', 't', 'p']) (rest := ['g']) (by decide) rfl
    (by decide) (by decide) rfl (by decide) (by intro r2 h; cases h)
    (by rw [run_relative_pathRef rfcBase ['g'] _ rfl (by decide) rfl rfl rfl rfl (by decide)
          (by decide) (by decide)]
        exact congrArg PResult.ok (by decide))

end Url.Spec
