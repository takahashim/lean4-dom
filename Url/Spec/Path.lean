import Url.Spec.Relative

/-!
# path の関係仕様（§4.4 path state と shorten）

path state は入力を一文字ずつ読み、buffer に percent-encode して積み、区切りで segment を確定させる。
確定のたびに `.` と `..` を畳む。ここでは同じものを、buffer も state も使わずに書く。

1. 入力を区切り（`/`、special なら `\` も）で割る（`splitSegs`）。割り方は一通りしかない
   （`SplitBy` が宣言的な条件、`splitSegs_iff` が一致）。
2. 各片を path percent-encode set で encode する（`encodeSeg`）。
3. 片の列を、最後の片だけ扱いを変えて畳む（`resolveSegs`）。最後の片は区切りでなく
   入力の終わり・`?`・`#` で終わったもので、`.` と `..` の後に空の segment を残す。

畳み込みの一歩（`segStep`）は path state 1.2-1.4 を、`shorten` は §4.4 shorten a URL's path を写す。
parser の `pathStepUrl`・`shortenPath`・`appendSegment` は呼ばない。共有するのは §4.4 冒頭の定義
（`isSingleDot`・`isDoubleDot`・`isWindowsDrive`・`isNormalizedWindowsDrive`）と §1.3 の percent-encode だけである。

`run_path_eof`・`run_path_query`・`run_path_fragment` が、path state はこの畳み込みで入力を読む、と言う。
-/

namespace Url.Spec

open Infra Url

/-! ## 区切りで割る -/

/-- §4.4 path state の区切り。`/`、special なら `\` も。 -/
def isPathSep (special : Bool) (c : Char) : Bool := c == '/' || (special && c == '\\')

/--
列を区切りで割る。区切りが `n` 個なら片は `n + 1` 個で、空の片もそのまま残す。

`SplitBy p l segs` は「片を区切りの文字を一つずつ挟んで並べると `l` に戻り、どの片にも区切りが無い」。
区切りの文字が何であったか（`/` か `\` か）は片の列に残らない。
-/
inductive SplitBy (p : Char → Bool) : List Char → List (List Char) → Prop
  | last {s : List Char} : (∀ c ∈ s, p c = false) → SplitBy p s [s]
  | sep {s r : List Char} {d : Char} {segs : List (List Char)} :
      (∀ c ∈ s, p c = false) → p d = true → SplitBy p r segs → SplitBy p (s ++ d :: r) (s :: segs)

/-- 区切りで割る関数。 -/
def splitBy (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: t =>
    if p c then [] :: splitBy p t
    else match splitBy p t with
      | s :: r => (c :: s) :: r
      | [] => [[c]]

/-- §4.4 path state の区切りで割る。 -/
def splitSegs (special : Bool) (l : List Char) : List (List Char) :=
  splitBy (isPathSep special) l

theorem splitBy_ne_nil (p : Char → Bool) : ∀ l, splitBy p l ≠ []
  | [] => by simp [splitBy]
  | c :: t => by
    unfold splitBy
    split
    · simp
    · split <;> simp

/-- 区切りの無い前置きは、最初の片の前に付くだけである。 -/
theorem splitBy_append_nosep (p : Char → Bool) : ∀ (s tail : List Char), (∀ c ∈ s, p c = false) →
    splitBy p (s ++ tail) = (splitBy p tail).modifyHead (s ++ ·)
  | [], tail, _ => by
    cases h : splitBy p tail with
    | nil => exact absurd h (splitBy_ne_nil p tail)
    | cons a r => simp [h]
  | c :: s, tail, h => by
    have hc : p c = false := h c (by simp)
    have ih := splitBy_append_nosep p s tail (fun x hx => h x (by simp [hx]))
    simp only [List.cons_append, splitBy, hc, Bool.false_eq_true, if_false, ih]
    cases h2 : splitBy p tail with
    | nil => exact absurd h2 (splitBy_ne_nil p tail)
    | cons a r => simp

/-- **関係を満たす片の列は `splitBy` の出力である。** -/
theorem SplitBy.eq_splitBy {p : Char → Bool} {l : List Char} {segs : List (List Char)}
    (h : SplitBy p l segs) : segs = splitBy p l := by
  induction h with
  | @last s hs =>
    have := splitBy_append_nosep p s [] hs
    simp only [List.append_nil] at this
    rw [this]; simp [splitBy]
  | @sep s r d segs hs hd _ ih =>
    rw [splitBy_append_nosep p s _ hs]
    simp [splitBy, hd, ← ih]

/-- **`splitBy` は `SplitBy` を満たす。** -/
theorem splitBy_spec (p : Char → Bool) : ∀ l, SplitBy p l (splitBy p l)
  | [] => .last (by simp)
  | c :: t => by
    have ih := splitBy_spec p t
    by_cases hc : p c = true
    · have := SplitBy.sep (s := []) (by simp) hc ih
      simpa [splitBy, hc] using this
    · have hc' : p c = false := by simpa using hc
      have := splitBy_append_nosep p [c] t (by simp [hc'])
      simp only [List.singleton_append] at this
      rw [this]
      revert ih
      cases splitBy p t with
      | nil => intro ih; cases ih
      | cons s r =>
        intro ih
        simp only [List.modifyHead_cons]
        cases ih with
        | last hs =>
          exact .last (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hc'
            · exact hs x hx)
        | sep hs hd hr =>
          have := SplitBy.sep (s := c :: _) (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hc'
            · exact hs x hx) hd hr
          simpa using this

/-- **割り方は一通りしかなく、`splitSegs` がそれを計算する。** -/
theorem splitSegs_iff {special : Bool} {l : List Char} {segs : List (List Char)} :
    SplitBy (isPathSep special) l segs ↔ splitSegs special l = segs :=
  ⟨fun h => h.eq_splitBy.symm, fun h => h ▸ splitBy_spec _ l⟩

/-- 区切りでない文字を先頭に足すと、最初の片の先頭に付く。 -/
theorem splitBy_cons_nosep {p : Char → Bool} {c : Char} (hc : p c = false) (t : List Char) :
    splitBy p (c :: t) = (splitBy p t).modifyHead (c :: ·) := by
  have := splitBy_append_nosep p [c] t (by simp [hc])
  simpa using this

/-! ## segment の畳み込み -/

/-- §1.3 path percent-encode set で一つの片を encode する。 -/
def encodeSeg (seg : List Char) : List Char := utf8PercentEncode pathSet seg

/-- 入力の path 部分を、encode した片の列にする。 -/
def pathSegments (special : Bool) (l : List Char) : List (List Char) :=
  (splitSegs special l).map encodeSeg

/--
§4.4 shorten a URL's path。

step 3：scheme が `file` で、path が一つだけで、それが normalized Windows drive letter なら何もしない。
step 4：そうでなければ最後の segment を落とす（空なら何もしない）。
-/
def shorten (isFile : Bool) (segs : List String) : List String :=
  if isFile && segs.length == 1 && isNormalizedWindowsDrive (segs.headD "").toList then segs
  else segs.dropLast

/-- path state 1.4.1 の Windows drive letter quirk。二文字目を `:` にする。 -/
def driveColon : List Char → List Char
  | [a, _] => [a, ':']
  | s => s

/--
path state 1.2-1.4：一つの片で path を更新する。`last` は、その片が区切りでなく
入力の終わり・`?`・`#` で終わったこと。

* double-dot なら shorten し、`last` なら空の segment を足す（1.2）。
* single-dot なら何もせず、`last` なら空の segment を足す（1.3）。
* それ以外は片を足す。`file` で path が空のときの Windows drive letter は `c:` に直す（1.4）。
-/
def segStep (isFile : Bool) (acc : List String) (seg : List Char) (last : Bool) : List String :=
  if isDoubleDot seg then shorten isFile acc ++ (if last then [""] else [])
  else if isSingleDot seg then acc ++ (if last then [""] else [])
  else acc ++ [String.ofList
    (if isFile && acc.isEmpty && isWindowsDrive seg then driveColon seg else seg)]

/-- 区切りで終わった片（最後以外）を順に畳む。 -/
def foldSegs (isFile : Bool) (acc : List String) (segs : List (List Char)) : List String :=
  segs.foldl (fun a s => segStep isFile a s false) acc

/-- **片の列で path を更新する。** 最後の片だけ `last` として扱う。 -/
def resolveSegs (isFile : Bool) (acc : List String) (segs : List (List Char)) : List String :=
  segStep isFile (foldSegs isFile acc segs.dropLast) (segs.getLast?.getD []) true

/-! ## path state との対応 -/

/-- parser の segment 確定は `segStep` である。 -/
theorem pathStepUrl_eq_segStep {u : Url} {P : List String} (hp : u.path = .list P)
    (slash : Bool) (buf : List Char) :
    pathStepUrl u slash buf = { u with path := .list (segStep (u.scheme == "file") P buf !slash) } := by
  have hsh : shortenPath u = { u with path := .list (shorten (u.scheme == "file") P) } := by
    unfold shortenPath shorten
    rw [hp]
    dsimp only
    have hgd : P.getD 0 "" = P.headD "" := by cases P <;> rfl
    rw [hgd]
    split
    · next h => rw [← hp]
    · rfl
  have happ : ∀ (v : Url) (Q : List String) (x : String), v.path = .list Q →
      appendSegment v x = { v with path := .list (Q ++ [x]) } := by
    intro v Q x hq; unfold appendSegment; rw [hq]
  have hwd : pathStepUrl.windowsDriveBuffer u buf =
      (if (u.scheme == "file") && P.isEmpty && isWindowsDrive buf then driveColon buf else buf) := by
    unfold pathStepUrl.windowsDriveBuffer
    rw [hp]
    cases P with
    | nil =>
      simp only [List.isEmpty_nil, Bool.and_true]
      by_cases h : (u.scheme == "file" && isWindowsDrive buf) = true
      · rw [if_pos (by simpa using h), if_pos h]
        rcases buf with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all [isWindowsDrive, driveColon]
      · rw [if_neg (by simpa using h), if_neg h]
    | cons x t => simp
  unfold pathStepUrl segStep
  by_cases hd : isDoubleDot buf = true
  · rw [if_pos hd, if_pos hd]
    cases slash
    · simp only [if_false, Bool.not_false, if_true, Bool.false_eq_true]
      rw [happ _ (shorten (u.scheme == "file") P) "" (by rw [hsh]), hsh]
    · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
      exact hsh
  · rw [if_neg hd, if_neg hd]
    by_cases hs : isSingleDot buf = true
    · rw [if_pos hs, if_pos hs]
      cases slash
      · simp only [if_false, Bool.not_false, if_true, Bool.false_eq_true]
        exact happ u P "" hp
      · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
        cases u; simp_all
    · rw [if_neg hs, if_neg hs, hwd]
      exact happ u P _ hp

/-- path state の区切り。segment を確定させて次の片へ進む。 -/
theorem run_path_sep (base : Option Url) {c : Char} (rest : List Char) (ctx : PCtx)
    (h : isPathSep ctx.url.isSpecial c = true) :
    run base .path (c :: rest) ctx
      = run base .path rest { ctx with url := pathStepUrl ctx.url true ctx.buffer, buffer := [] } := by
  simp only [isPathSep, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with rfl | ⟨hsp, rfl⟩
  · rw [run, step]; simp
  · rw [run, step]; simp [hsp]

/-- path state の区切りでない文字。percent-encode して buffer に積む。 -/
theorem run_path_plain (base : Option Url) {c : Char} (rest : List Char) (ctx : PCtx)
    (h : isPathSep ctx.url.isSpecial c = false) (hq : c ≠ '?') (hh : c ≠ '#') :
    run base .path (c :: rest) ctx
      = run base .path rest { ctx with buffer := ctx.buffer ++ (encChar pathSet c).toList } := by
  simp only [isPathSep, Bool.or_eq_false_iff, Bool.and_eq_false_imp, beq_eq_false_iff_ne] at h
  rw [run, step]
  rw [if_neg (by
    simp only [Bool.or_eq_true, beq_iff_eq, Option.some.injEq, reduceCtorEq, false_or,
      Bool.and_eq_true, not_or, not_and]
    refine ⟨⟨h.1, fun hs => h.2 hs⟩, fun _ => ⟨hq, hh⟩⟩)]

/-- path state の終わり。最後の片を確定させる。 -/
theorem run_path_end (base : Option Url) (ctx : PCtx) :
    run base .path [] ctx = .ok (pathStepUrl ctx.url false ctx.buffer) := by
  rw [run, step]; simp

/-- path state の `?`。最後の片を確定させて query state へ。 -/
theorem run_path_q (base : Option Url) (rest : List Char) (ctx : PCtx) (hov : ctx.over = none) :
    run base .path ('?' :: rest) ctx
      = run base .query rest
          { ctx with url := { pathStepUrl ctx.url false ctx.buffer with query := some "" },
                     buffer := [] } := by
  rw [run, step, if_pos (by simp [hov])]; simp

/-- path state の `#`。最後の片を確定させて fragment state へ。 -/
theorem run_path_h (base : Option Url) (rest : List Char) (ctx : PCtx) (hov : ctx.over = none) :
    run base .path ('#' :: rest) ctx
      = run base .fragment rest
          { ctx with url := { pathStepUrl ctx.url false ctx.buffer with fragment := some "" },
                     buffer := [] } := by
  rw [run, step, if_pos (by simp [hov])]; simp

theorem encodeSeg_cons (c : Char) (s : List Char) :
    encodeSeg (c :: s) = (encChar pathSet c).toList ++ encodeSeg s := by
  simp [encodeSeg, encChar, utf8PercentEncode]

/--
**path state は、区切りまでの片を `segStep` で畳みながら読む。** 最後の片は buffer に残る。

`tail` は何でもよい。読み終えた後の続きである。
-/
theorem run_path_read (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx) (P : List String),
    ctx.url.path = .list P → ctx.over = none → (∀ c ∈ l, c ≠ '?' ∧ c ≠ '#') →
    run base .path (l ++ tail) ctx
      = run base .path tail
          { ctx with
            url := { ctx.url with path := .list (foldSegs (ctx.url.scheme == "file") P
              ((pathSegments ctx.url.isSpecial l).modifyHead (ctx.buffer ++ ·)).dropLast) }
            buffer := ((pathSegments ctx.url.isSpecial l).modifyHead (ctx.buffer ++ ·)).getLast?.getD [] } := by
  intro l
  induction l with
  | nil =>
    intro tail ctx P hp _ _
    simp only [pathSegments, splitSegs, splitBy, List.map_cons, List.map_nil, encodeSeg,
      List.modifyHead_cons, List.dropLast_singleton, List.getLast?_singleton, Option.getD_some,
      List.nil_append, foldSegs, List.foldl_nil]
    have : utf8PercentEncode pathSet [] = [] := rfl
    rw [this, List.append_nil, ← hp]
  | cons c t ih =>
    intro tail ctx P hp hov hl
    have hc := hl c (by simp)
    have ht : ∀ x ∈ t, x ≠ '?' ∧ x ≠ '#' := fun x hx => hl x (by simp [hx])
    have hne := splitBy_ne_nil (isPathSep ctx.url.isSpecial) t
    by_cases hsep : isPathSep ctx.url.isSpecial c = true
    · rw [List.cons_append, run_path_sep base _ ctx hsep]
      have hu := pathStepUrl_eq_segStep hp true ctx.buffer
      rw [hu, Bool.not_true]
      refine Eq.trans (ih tail _ (segStep (ctx.url.scheme == "file") P ctx.buffer false) rfl hov ht) ?_
      simp only [pathSegments, splitSegs, Url.isSpecial] at hne hsep ⊢
      rw [show splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) (c :: t)
          = [] :: splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) t by simp [splitBy, hsep]]
      revert hne
      cases splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) t with
      | nil => intro h; exact absurd rfl h
      | cons x r =>
        intro _
        simp [foldSegs, encodeSeg, List.dropLast_cons_of_ne_nil, List.getLast?_cons,
          show utf8PercentEncode pathSet [] = [] from rfl]
    · have hsep' : isPathSep ctx.url.isSpecial c = false := by simpa using hsep
      rw [List.cons_append, run_path_plain base _ ctx hsep' hc.1 hc.2]
      refine Eq.trans (ih tail _ P hp hov ht) ?_
      simp only [pathSegments, splitSegs]
      rw [splitBy_cons_nosep hsep' t]
      revert hne
      cases splitBy (isPathSep ctx.url.isSpecial) t with
      | nil => intro h; exact absurd rfl h
      | cons x r =>
        intro _
        simp [encodeSeg_cons, List.append_assoc]

theorem modifyHead_nil_append (l : List (List Char)) : l.modifyHead ([] ++ ·) = l := by
  cases l <;> simp

/-- 片を読み切った後の path。buffer が空のところから始めたとき。 -/
theorem read_path_url {ctx : PCtx} {P : List String} (_hp : ctx.url.path = .list P)
    (hbuf : ctx.buffer = []) (l : List Char) :
    pathStepUrl { ctx.url with path := .list (foldSegs (ctx.url.scheme == "file") P
        ((pathSegments ctx.url.isSpecial l).modifyHead (ctx.buffer ++ ·)).dropLast) } false
      (((pathSegments ctx.url.isSpecial l).modifyHead (ctx.buffer ++ ·)).getLast?.getD [])
    = { ctx.url with path := .list (resolveSegs (ctx.url.scheme == "file") P
        (pathSegments ctx.url.isSpecial l)) } := by
  rw [pathStepUrl_eq_segStep rfl, hbuf, modifyHead_nil_append]
  rfl

/--
**path state が入力の終わりまで読むと、path は `resolveSegs` になる。**

`?` も `#` も含まない入力について。他の成分は変わらない。
-/
theorem run_path_spec (base : Option Url) (l : List Char) (ctx : PCtx) {P : List String}
    (hp : ctx.url.path = .list P) (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hl : ∀ c ∈ l, c ≠ '?' ∧ c ≠ '#') :
    run base .path l ctx
      = .ok { ctx.url with path := .list (resolveSegs (ctx.url.scheme == "file") P
          (pathSegments ctx.url.isSpecial l)) } := by
  have h := run_path_read base l [] ctx P hp hov hl
  rw [List.append_nil] at h
  rw [h, run_path_end]
  exact congrArg PResult.ok (read_path_url hp hbuf l)

/-- **`?` までを path として読み、query state へ渡す。** -/
theorem run_path_spec_query (base : Option Url) (l rest : List Char) (ctx : PCtx)
    {P : List String} (hp : ctx.url.path = .list P) (hov : ctx.over = none)
    (hbuf : ctx.buffer = []) (hl : ∀ c ∈ l, c ≠ '?' ∧ c ≠ '#') :
    run base .path (l ++ '?' :: rest) ctx
      = run base .query rest
          { ctx with
            url := { ctx.url with
              path := .list (resolveSegs (ctx.url.scheme == "file") P (pathSegments ctx.url.isSpecial l))
              query := some "" }
            buffer := [] } := by
  rw [run_path_read base l _ ctx P hp hov hl]
  rw [run_path_q base rest, read_path_url hp hbuf l]
  exact hov

/-- **`#` までを path として読み、fragment state へ渡す。** -/
theorem run_path_spec_fragment (base : Option Url) (l rest : List Char) (ctx : PCtx)
    {P : List String} (hp : ctx.url.path = .list P) (hov : ctx.over = none)
    (hbuf : ctx.buffer = []) (hl : ∀ c ∈ l, c ≠ '?' ∧ c ≠ '#') :
    run base .path (l ++ '#' :: rest) ctx
      = run base .fragment rest
          { ctx with
            url := { ctx.url with
              path := .list (resolveSegs (ctx.url.scheme == "file") P (pathSegments ctx.url.isSpecial l))
              fragment := some "" }
            buffer := [] } := by
  rw [run_path_read base l _ ctx P hp hov hl]
  rw [run_path_h base rest, read_path_url hp hbuf l]
  exact hov

end Url.Spec
