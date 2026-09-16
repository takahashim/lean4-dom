import Url.RoundtripPath

/-!
# special scheme の往復
-/

namespace Url

open Infra

/-! ## special

`http:` などの経路。scheme state から special authority slashes state へ入り、
`//` を読み飛ばして authority state に着く。path state では `\\` も区切りになる。
-/

/-- scheme state の `:`：special な scheme で base が無ければ special authority slashes へ。 -/
theorem run_scheme_specialAuthoritySlashes (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = true) :
    run none .scheme (':' :: rest) ctx
      = run none .specialAuthoritySlashes rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_pos (by simp [Url.isSpecial, hsp])]

/-- special authority slashes state：`//` を読み飛ばす。 -/
theorem run_specialAuthoritySlashes (base : Option Url) (rest2 : List Char) (ctx : PCtx) :
    run base .specialAuthoritySlashes ('/' :: '/' :: rest2) ctx
      = run base .specialAuthorityIgnoreSlashes rest2 ctx := by
  rw [run, step]

/-- special authority ignore slashes state：`/` でも `\` でもなければ authority へ。 -/
theorem run_specialAuthorityIgnoreSlashes (base : Option Url) (l : List Char) (ctx : PCtx)
    (h : ∀ c ∈ l.head?, ¬c = '/' ∧ ¬c = '\\') :
    run base .specialAuthorityIgnoreSlashes l ctx = run base .authority l ctx := by
  cases l with
  | nil => rw [run, step]
  | cons c t =>
    have hc := h c rfl
    rw [run, step]
    rw [if_neg (by simp [hc.1, hc.2])]

/-- path start state：special なら `/` を一つ落として path state へ。 -/
theorem run_pathStart_slash_special (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_pos (by simp [hsp])]
  simp

/-- path state の `?`。最後の segment を確定させて query state へ渡す。 -/
theorem run_path_question (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) :
    run base .path ('?' :: rest) ctx
      = run base .query rest
          { ctx with
            url := { pathStepUrl ctx.url false ctx.buffer with query := some "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_pos (by simp [hov])]
  simp

/-- path state の `#`。最後の segment を確定させて fragment state へ渡す。 -/
theorem run_path_hash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) :
    run base .path ('#' :: rest) ctx
      = run base .fragment rest
          { ctx with
            url := { pathStepUrl ctx.url false ctx.buffer with fragment := some "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_pos (by simp [hov])]
  simp

/-- path state が path と query と fragment を読み切る。 -/
theorem run_path_full (base : Option Url) (sp : Bool) (segs : List String) (q f : Option String)
    (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none)
    (hpath : ctx.url.path = .list []) (hb : ctx.buffer = [])
    (hwd : ∀ x, segs.head? = some x → pathStepUrl.windowsDriveBuffer ctx.url x.toList = x.toList)
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hne : segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .path (intercal segs ++ qfList q f) ctx
      = .ok { ctx.url with path := .list segs, query := q, fragment := f } := by
  cases hseg : segs with
  | nil => exact absurd hseg hne
  | cons x t =>
    rw [run_path_segs base sp (x :: t) (qfList q f) ctx [] ?p1 ?p2 ?p3 ?p4 ?p5 ?p6]
    case p1 => exact hpath
    case p2 => exact hb
    case p3 => exact hsp
    case p4 => exact hov
    case p5 => rw [← hseg]; exact hwd
    case p6 => rw [← hseg]; exact hall
    cases hlast : (x :: t).getLast? with
    | none => simp at hlast
    | some last =>
      have hlmem : last ∈ (x :: t) := List.mem_of_mem_getLast? hlast
      have hlall := hall last (by rw [hseg]; exact hlmem)
      have hdl : (x :: t).dropLast ++ [last] = x :: t := by
        have := dropLast_getLast? (x :: t) (by simp)
        rw [hlast] at this
        simpa using this
      -- 最後の segment を確定させる。ここから先は query と fragment の有無で分かれる。
      have hwdlast : pathStepUrl.windowsDriveBuffer
          { ctx.url with path := Path.list (x :: t).dropLast } last.toList = last.toList := by
        cases hdl2 : (x :: t).dropLast with
        | cons y u => exact windowsDriveBuffer_of_path_ne rfl (by simp)
        | nil =>
          rw [hdl2, List.nil_append] at hdl
          simp only [List.cons.injEq] at hdl
          rw [hdl.1]
          rw [show ({ ctx.url with path := Path.list [] } : Url) = ctx.url from by rw [← hpath]]
          exact hwd x (by rw [hseg]; rfl)
      have hcommit : pathStepUrl
          { ctx.url with path := Path.list (x :: t).dropLast } false last.toList
          = { ctx.url with path := Path.list (x :: t) } := by
        rw [pathStepUrl_append (pre := (x :: t).dropLast) rfl hwdlast
          hlall.2.1 hlall.2.2]
        rw [hdl]
      simp only [Option.getD_some]
      cases q with
      | none =>
        cases f with
        | none =>
          simp only [qfList, List.append_nil, List.nil_append]
          rw [run_path_eof]
          dsimp only
          rw [hcommit]
          simp [hq0, hf0]
        | some fs =>
          simp only [qfList, List.nil_append]
          rw [run_path_hash base fs.toList _ ?h1]
          case h1 => exact hov
          dsimp only
          rw [hcommit]
          rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
          simp [hq0]
      | some qs =>
        simp only [qfList, List.cons_append, List.nil_append]
        rw [run_path_question base _ _ ?h3]
        case h3 => exact hov
        dsimp only
        rw [hcommit]
        dsimp only
        rw [run_query_full base qs f _ _ ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6]
        case g0 => rfl
        case g1 => simp [hov]
        case g2 => rfl
        case g3 => rfl
        case g4 => simpa using hf0
        case g5 => exact hqc qs rfl
        case g6 => exact hfc

/--
path state の `./`。single-dot segment は何も足さずに消える。

serializer が host の無い URL の先頭に付ける `/.` を読み直すところである。
-/
theorem run_path_dot (base : Option Url) (rest : List Char) (ctx : PCtx) (hb : ctx.buffer = []) :
    run base .path ('.' :: '/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_neg (by simp)]
  rw [run, step]
  rw [if_pos (by simp)]
  have henc : (encChar pathSet '.').toList = ['.'] := by decide
  have hstep : pathStepUrl ctx.url true ['.'] = ctx.url := by
    unfold pathStepUrl
    rw [if_neg (by decide), if_pos (by decide)]
    simp
  simp only [hb, List.nil_append, henc]
  split
  · next he => simp at he
  · next he => simp at he
  · next he => simp at he
  · simp only [beq_self_eq_true, Bool.true_or, hstep]
    rw [← hb]

/-- host の無い URL で、先頭 segment が空のときに serializer が足す `/.`。 -/
def dotPrefix (segs : List String) : List Char :=
  match segs with
  | seg :: _ :: _ => if seg.isEmpty then ['/', '.'] else []
  | _ => []

/--
**`/` で始まる path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、host を持たない非 special な URL の経路
（scheme start → scheme → path or authority → path）である。
先頭 segment が空で segment が二つ以上のときは serializer が `/.` を前置するが、
parse がそれを single-dot segment として落とすので、そこも入っている。
-/
theorem roundtrip_path {s : String} {segs : List String} {q f : Option String}
    {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (hne : segs ≠ [])
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList, querySet c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false)
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ ¬c = '/' ∧ ¬c = '?' ∧ ¬c = '#') ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false) :
    basicUrlParse (urlSerializer
        { scheme := s, path := .list segs, query := q, fragment := f }) none
      = some { scheme := s, path := .list segs, query := q, fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hterm : ∀ x ∈ segs, ∀ c ∈ x.toList, isTerminator false (some c) = false := by
    intro x hx c hc
    have := (hall x hx).1 c hc
    exact isTerminator_false this.2.1 this.2.2.1 this.2.2.2 (by simp)
  have hall' : ∀ x ∈ segs,
      (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator false (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false :=
    fun x hx => ⟨fun c hc => ⟨((hall x hx).1 c hc).1, hterm x hx c hc⟩,
      (hall x hx).2.1, (hall x hx).2.2⟩
  have hstr : (urlSerializer
      { scheme := s, path := .list segs, query := q, fragment := f }).toList
      = s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)) := by
    have hout : (serializerTail
        { scheme := s, path := .list segs, query := q, fragment := f } false).toList
        = dotPrefix segs ++ (pathChars segs ++ qfList q f) := by
      simp only [serializerTail, dotPrefix, qfList]
      cases segs with
      | nil => exact absurd rfl hne
      | cons x t =>
        cases t with
        | nil => cases q <;> cases f <;> simp [pathSerializer_pathChars]
        | cons y u =>
          cases hx : x.isEmpty with
          | true =>
            cases q <;> cases f <;>
              simp [hx, String.toList_append, pathSerializer_pathChars]
          | false => cases q <;> cases f <;> simp [hx, pathSerializer_pathChars]
    simp only [urlSerializer, String.toList_append, hout]
    simp
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  have hallc : ∀ c ∈ s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)),
      isC0ControlOrSpace c = false := by
    intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · rw [hs] at hcm
      rcases List.mem_cons.mp hcm with rfl | hcm
      · simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
        simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
        omega
      · exact ne_c0_of_schemeChar (hr c hcm)
    · rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · rcases List.mem_append.mp hcm with hcm | hcm
        · unfold dotPrefix at hcm
          split at hcm
          · split at hcm
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
              rcases hcm with rfl | rfl <;> decide
            · simp at hcm
          · simp at hcm
        · rcases List.mem_append.mp hcm with hcm | hcm
          · cases segs with
            | nil => exact absurd rfl hne
            | cons x t =>
              rcases List.mem_cons.mp hcm with rfl | hcm
              · decide
              · rcases intercal_mem (x :: t) c hcm with rfl | ⟨y, hy, hc⟩
                · decide
                · exact ne_c0_of_c0Set (c0Set_of_pathSet ((hall y hy).1 c hc).1)
                    (ne_space_of_pathSet ((hall y hy).1 c hc).1)
          · exact qfList_c0 hqc hfc c hcm
  have hpre : preprocess (urlSerializer
      { scheme := s, path := .list segs, query := q, fragment := f })
      = s.toList ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f)) := by
    rw [preprocess_eq_self ?head ?last ?tab, hstr]
    case head =>
      intro c hcm
      rw [hstr] at hcm
      exact hallc c (List.mem_of_mem_head? hcm)
    case last =>
      intro c hcm
      rw [hstr, List.head?_reverse] at hcm
      exact hallc c (List.mem_of_mem_getLast? hcm)
    case tab =>
      intro c hcm
      rw [hstr] at hcm
      have := hallc c hcm
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le] at this
      omega
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a
    (rest ++ ':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f))) haa]
  rw [run_scheme_prefix none rest (':' :: (dotPrefix segs ++ (pathChars segs ++ qfList q f))) _ hr]
  -- 先頭 segment が空で二つ以上あるときは serializer が `/.` を足す。
  have hdot : ∀ (c2 : PCtx), c2.url.isSpecial = false → c2.over = none →
      c2.url.path = .list [] → c2.buffer = [] → ¬c2.url.scheme = "file" →
      c2.url.query = none → c2.url.fragment = none →
      run none .path (intercal segs ++ qfList q f) c2
        = .ok { c2.url with path := .list segs, query := q, fragment := f } :=
    fun c2 h1 h2 h3 h4 h5 h6 h7 =>
      run_path_full none false segs q f c2 h1 h2 h3 h4
        (fun _ _ => windowsDriveBuffer_of_not_file h5) h6 h7 hne hall'
        (fun x hx c hc => by rw [if_neg (by simp [h1])]; exact hqc x hx c hc) hfc
  cases hseg : segs with
  | nil => exact absurd hseg hne
  | cons x t =>
    have hpc : pathChars (x :: t) = '/' :: intercal (x :: t) := rfl
    by_cases hdp : dotPrefix (x :: t) = []
    · -- `/.` は付かない。先頭 segment は空でないか、segment が一つしかない。
      have hheadx : ∀ c ∈ (intercal (x :: t) ++ qfList q f).head?, ¬c = '/' := by
        intro c hc
        cases hi : intercal (x :: t) with
        | nil =>
          rw [hi, List.nil_append] at hc
          unfold qfList at hc
          cases q with
          | some qs =>
            simp only [List.cons_append, List.head?_cons, Option.mem_def,
              Option.some.injEq] at hc
            rw [← hc]; decide
          | none =>
            cases f with
            | some fs =>
              simp only [List.nil_append, List.head?_cons, Option.mem_def,
                Option.some.injEq] at hc
              rw [← hc]; decide
            | none => simp at hc
        | cons d u =>
        rw [hi, List.cons_append, List.head?_cons] at hc
        refine intercal_head_ne_slash (x :: t) c ?_ ?_ (by rw [hi]; exact hc)
        · intro y u hu hune
          simp only [List.cons.injEq] at hu
          rw [← hu.1]
          cases hxe : x.isEmpty with
          | true =>
            exfalso
            have hd2 : dotPrefix (x :: t) = ['/', '.'] := by
              unfold dotPrefix
              cases t with
              | nil => exact absurd hu.2.symm hune
              | cons z w => simp [hxe]
            rw [hd2] at hdp
            simp at hdp
          | false => simpa using hxe
        · exact fun y hy d hd => ((hall y (by rw [hseg]; exact hy)).1 d hd).2.1
      rw [hdp, List.nil_append, hpc, List.cons_append]
      rw [run_scheme_pathOrAuthority none (intercal (x :: t) ++ qfList q f) _ rfl
        (by rw [hbuf, String.ofList_toList]; exact hfile)
        (by rw [hbuf, String.ofList_toList]; exact hsp)]
      rw [hbuf, String.ofList_toList]
      rw [run_pathOrAuthority_path none (intercal (x :: t) ++ qfList q f) _ hheadx]
      rw [show intercal (x :: t) = intercal segs from by rw [hseg]]
      rw [hdot _ (by simp [Url.isSpecial, hsp]) rfl rfl rfl (by simpa using hfile) rfl rfl]
      simp [hseg]
    · -- `/.` が付く。`.` は single-dot segment なので消える。
      have hdp2 : dotPrefix (x :: t) = ['/', '.'] := by
        unfold dotPrefix at hdp ⊢
        cases t with
        | nil => exact absurd rfl hdp
        | cons z w =>
          cases hxe : x.isEmpty with
          | true => simp [hxe]
          | false => exact absurd (by simp [hxe]) hdp
      rw [hdp2]
      rw [show (['/', '.'] ++ (pathChars (x :: t) ++ qfList q f))
          = '/' :: '.' :: (pathChars (x :: t) ++ qfList q f) from rfl]
      rw [run_scheme_pathOrAuthority none ('.' :: (pathChars (x :: t) ++ qfList q f)) _ rfl
        (by rw [hbuf, String.ofList_toList]; exact hfile)
        (by rw [hbuf, String.ofList_toList]; exact hsp)]
      rw [hbuf, String.ofList_toList]
      rw [run_pathOrAuthority_path none ('.' :: (pathChars (x :: t) ++ qfList q f)) _ (by simp)]
      rw [hpc, List.cons_append]
      rw [run_path_dot none (intercal (x :: t) ++ qfList q f) _ rfl]
      rw [show intercal (x :: t) = intercal segs from by rw [hseg]]
      rw [hdot _ (by simp [Url.isSpecial, hsp]) rfl rfl rfl (by simpa using hfile) rfl rfl]
      simp [hseg]

/-- 先頭 segment が空でも往復する。serializer が `/.` を足し、parse が single dot で落とす。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list ["", "x"] }) none
    = some { scheme := "sc", path := .list ["", "x"] } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by decide)

/-- 仮定が空でないことの確認。`sc:/a/b` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer { scheme := "sc", path := .list ["a", "b"] }) none
    = some { scheme := "sc", path := .list ["a", "b"] } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by decide)

/-- path の側でも query と fragment が往復する。`sc:/a?q#f` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", path := .list ["a"], query := some "q", fragment := some "f" }) none
    = some { scheme := "sc", path := .list ["a"], query := some "q", fragment := some "f" } :=
  roundtrip_path (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp; decide) (by simp; decide) (by decide)

end Url
