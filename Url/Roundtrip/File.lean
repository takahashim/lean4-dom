import Url.Roundtrip.Ipv6Host

/-!
# `file:` の往復
-/

namespace Url

open Infra

/-! ## `file:`

`file:` は authority state を通らない。scheme state から file state へ入り、
`//` を二つの state で読み飛ばして file host state に着く。
host が空でも `//` は書かれるので、file host state は空の buffer も受ける。
-/

/-- scheme state の `:`。buffer が `file` なら file state へ。 -/
theorem run_scheme_file (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hf : String.ofList ctx.buffer = "file") :
    run base .scheme (':' :: rest) ctx
      = run base .file rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_pos (by simpa using hf)]

/-- file state の `/`。host を空にして file slash state へ。 -/
theorem run_file_slash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .file ('/' :: rest) ctx
      = run base .fileSlash rest
          { ctx with url := { ctx.url with scheme := "file", host := some Host.empty } } := by
  rw [run, step.eq_def]
  simp only []
  rw [if_pos (by decide)]

/-- file slash state の `/`。file host state へ。 -/
theorem run_fileSlash_slash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .fileSlash ('/' :: rest) ctx = run base .fileHost rest ctx := by
  rw [run, step.eq_def]
  simp only []
  rw [if_pos (by decide)]

/-- 区切りの文字は file host state の出口の条件を満たす。並べる順が違うだけである。 -/
theorem fileHost_terminator {d : Char} (h : isTerminator true (some d) = true) :
    (some d == (none : Cp) || some d == some '/' || some d == some '\\' ||
      some d == some '?' || some d == some '#') = true := by
  simp only [isTerminator, Bool.or_eq_true, beq_iff_eq, Bool.true_and] at h
  simp only [Bool.or_eq_true, beq_iff_eq, Option.some.injEq, reduceCtorEq, false_or]
  rcases h with ((h | h) | h) | h <;> simp [h]

/-- file host state が区切りでない文字を読み切る。 -/
theorem run_fileHost_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx),
    (∀ c ∈ l, isTerminator true (some c) = false) →
    run base .fileHost (l ++ tail) ctx
      = run base .fileHost tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _; simp
  | cons c l' ih =>
    intro tail ctx h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step.eq_def]
    simp only []
    have hc' : ((¬c = '/' ∧ ¬c = '?') ∧ ¬c = '#') ∧ ¬c = '\\' := by
      simpa [isTerminator] using hc
    rw [if_neg (by simp [hc'.1.1.1, hc'.1.1.2, hc'.1.2, hc'.2])]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } (fun x hx => h x (by simp [hx]))]
    simp

/-- file host state の区切り。buffer が空なら host は空のままである。 -/
theorem run_fileHost_empty (base : Option Url) (tail : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hb : ctx.buffer = [])
    (ht : ∀ c ∈ tail.head?, isTerminator true (some c) = true) :
    run base .fileHost tail ctx
      = run base .pathStart tail
          { ctx with url := { ctx.url with host := some Host.empty } } := by
  cases tail with
  | nil =>
    rw [run, step.eq_def]
    simp only []
    rw [if_pos (by simp)]
    rw [if_neg (by simp [hb, isWindowsDrive])]
    rw [if_pos (by simp [hb])]
    simp [hov]
  | cons d t =>
    rw [run, step.eq_def]
    simp only []
    rw [if_pos (fileHost_terminator (ht d rfl))]
    rw [if_neg (by simp [hb, isWindowsDrive])]
    rw [if_pos (by simp [hb])]
    simp [hov]

/-- file host state の区切り。buffer を host parser に渡す。 -/
theorem run_fileHost_pathStart (base : Option Url) (tail : List Char) (ctx : PCtx) (hst : Host)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = true)
    (ht : ∀ c ∈ tail.head?, isTerminator true (some c) = true)
    (hne : ¬ctx.buffer = []) (hnd : isWindowsDrive ctx.buffer = false)
    (hp : hostParser ctx.toAscii ctx.buffer false = some hst)
    (hloc : ¬(hostSerializer hst = "localhost")) :
    run base .fileHost tail ctx
      = run base .pathStart tail
          { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
  have hbe : ctx.buffer.isEmpty = false := by
    cases hb : ctx.buffer with
    | nil => exact absurd hb hne
    | cons d t => simp
  have hstep : ∀ (c : Cp) (rest inp : List Char),
      (c == none || c == some '/' || c == some '\\' || c == some '?' || c == some '#') = true →
      step base .fileHost c rest inp ctx
        = run base .pathStart inp
            { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
    intro c rest inp hcond
    rw [step.eq_def]
    simp only []
    rw [if_pos hcond]
    rw [if_neg (by simp [hnd])]
    rw [if_neg (by simp [hbe])]
    simp only [hsp, Bool.not_true, hp]
    simp [hov, hloc]
  cases tail with
  | nil => rw [run]; exact hstep none [] [] (by simp)
  | cons d t =>
    rw [run]
    exact hstep (some d) t (d :: t) (fileHost_terminator (ht d rfl))

/--
**`file:` URL は serialize して parse し直すと元に戻る。**

host が空なら `file:///a`、あれば `file://h/a` の形である。
-/
theorem roundtrip_file {hst : Host} {segs : List String} {q f : Option String}
    (hcan : hst = Host.empty ∨
      hostParser asciiDomainToASCII (hostSerializer hst).toList false = some hst)
    (hok : hostReadable true hst)
    (hnc : ∀ c ∈ (hostSerializer hst).toList, isC0ControlOrSpace c = false)
    (hdrv : isWindowsDrive (hostSerializer hst).toList = false)
    (hloc : ¬hostSerializer hst = "localhost")
    (hne : segs ≠ [])
    (hdrive : ∀ x, segs.head? = some x →
      isWindowsDrive x.toList = false ∨ isNormalizedWindowsDrive x.toList = true)
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator true (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList, specialQuerySet c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    basicUrlParse (urlSerializer
        { scheme := "file"
          host := some hst
          path := .list segs
          query := q
          fragment := f }) none
      = some
        { scheme := "file"
          host := some hst
          path := .list segs
          query := q
          fragment := f } := by
  have hstr : (urlSerializer
      { scheme := "file", host := some hst, path := .list segs,
        query := q, fragment := f }).toList
      = "file".toList ++ ':' :: '/' :: '/'
        :: ((hostSerializer hst).toList ++ (pathChars segs ++ qfList q f)) := by
    simp only [urlSerializer, String.toList_append, serializerTail_authority]
    simp [credChars, portChars]
  have hallc : ∀ c ∈ "file".toList ++ ':' :: '/' :: '/'
      :: ((hostSerializer hst).toList ++ (pathChars segs ++ qfList q f)),
      isC0ControlOrSpace c = false := by
    intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · rw [show ("file" : String).toList = ['f', 'i', 'l', 'e'] from rfl] at hcm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl <;> decide
    · rcases List.mem_cons.mp hcm with rfl | hcm
      · decide
      · rcases List.mem_cons.mp hcm with rfl | hcm
        · decide
        · rcases List.mem_cons.mp hcm with rfl | hcm
          · decide
          · rcases List.mem_append.mp hcm with hcm | hcm
            · exact hnc c hcm
            · rcases List.mem_append.mp hcm with hcm | hcm
              · cases hseg : segs with
                | nil => exact absurd hseg hne
                | cons x t =>
                  rw [hseg] at hcm
                  rcases List.mem_cons.mp hcm with rfl | hcm
                  · decide
                  · rcases intercal_mem (x :: t) c hcm with rfl | ⟨y, hy, hcy⟩
                    · decide
                    · exact ne_c0_of_c0Set
                        (c0Set_of_pathSet ((hall y (by rw [hseg]; exact hy)).1 c hcy).1)
                        (ne_space_of_pathSet ((hall y (by rw [hseg]; exact hy)).1 c hcy).1)
              · exact qfList_c0
                  (fun x hx c hc => querySet_of_specialQuerySet (hqc x hx c hc)) hfc c hcm
  have hpre : preprocess (urlSerializer
      { scheme := "file", host := some hst, path := .list segs,
        query := q, fragment := f })
      = "file".toList ++ ':' :: '/' :: '/'
        :: ((hostSerializer hst).toList ++ (pathChars segs ++ qfList q f)) := by
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
  have hterm : ∀ c ∈ (pathChars segs ++ qfList q f).head?,
      isTerminator true (some c) = true := by
    intro c hc
    cases hseg : segs with
    | nil => exact absurd hseg hne
    | cons x t =>
      rw [hseg] at hc
      simp only [pathChars, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hc
      rw [← hc]
      decide
  unfold basicUrlParse
  rw [hpre]
  rw [show ("file" : String).toList = 'f' :: ['i', 'l', 'e'] from rfl, List.cons_append]
  rw [run_schemeStart_step none _ 'f' _ (by decide)]
  rw [run_scheme_prefix none ['i', 'l', 'e'] _ _ (by decide)]
  rw [run_scheme_file none _ _ rfl (by decide)]
  rw [show String.ofList ([] ++ [asciiLowerChar 'f'] ++ List.map asciiLowerChar ['i', 'l', 'e'])
      = "file" from by decide]
  rw [run_file_slash, run_fileSlash_slash]
  rw [run_fileHost_chunk none (hostSerializer hst).toList (pathChars segs ++ qfList q f) _
    (fun c hc => (hostReadable_auth hok c hc).2)]
  have hpath : ∀ x, segs.head? = some x →
      ∀ u : Url, pathStepUrl.windowsDriveBuffer u x.toList = x.toList := by
    intro x hx u
    rcases hdrive x hx with h | h
    · exact windowsDriveBuffer_of_not_drive h
    · exact windowsDriveBuffer_of_normalized h
  rcases hcan with rfl | hcan
  · rw [show (hostSerializer Host.empty).toList = [] from rfl]
    rw [run_fileHost_empty none _ _ rfl (by simp) hterm]
    rw [run_pathStart_path none true segs q f _ ?a1 rfl rfl (by simp)
      (fun x hx => hpath x hx _) rfl rfl (fun _ => hne) hall ?a2 hfc]
    case a1 => simp [Url.isSpecial, isSpecialScheme]
    case a2 =>
      intro x hx c hc
      rw [if_pos (by simp [Url.isSpecial, isSpecialScheme])]
      exact hqc x hx c hc
  · have hbne : ¬((hostSerializer hst).toList = []) := by
      intro he
      rw [he] at hcan
      simp [hostParser] at hcan
    rw [run_fileHost_pathStart none _ _ hst rfl ?b1 hterm ?b2 ?b3 ?b4 hloc]
    case b1 => simp [Url.isSpecial, isSpecialScheme]
    case b2 => simpa using hbne
    case b3 => simpa using hdrv
    case b4 => simpa using hcan
    rw [run_pathStart_path none true segs q f _ ?c1 rfl rfl rfl
      (fun x hx => hpath x hx _) rfl rfl (fun _ => hne) hall ?c2 hfc]
    case c1 => simp [Url.isSpecial, isSpecialScheme]
    case c2 =>
      intro x hx c hc
      rw [if_pos (by simp [Url.isSpecial, isSpecialScheme])]
      exact hqc x hx c hc

/-- host が空でも往復する。`file:///a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "file", host := some .empty, path := .list ["a"] }) none
    = some { scheme := "file", host := some .empty, path := .list ["a"] } :=
  roundtrip_file (Or.inl rfl) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp; decide) (by decide) (by simp) (by simp)

/-- IPv6 host を持つ `file:` も往復する。`file://[::]/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "file", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
        path := .list ["a"] }) none
    = some { scheme := "file", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
             path := .list ["a"] } :=
  roundtrip_file (Or.inr (by decide)) (hostReadable_ipv6 _ _) (ipv6_no_c0 _) (by decide)
    (by decide) (by decide) (by simp; decide) (by decide) (by simp) (by simp)

end Url
