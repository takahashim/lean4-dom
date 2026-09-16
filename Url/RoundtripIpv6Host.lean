import Url.RoundtripHostRun

/-!
# authority の走行と host の往復
-/

namespace Url

open Infra

/--
authority state から先（host と port と path）を読み切る。

credentials の有無で入口の `ctx` が変わるので、そこから先をこの補題にまとめてある。
-/
theorem run_authority_hostpath (base : Option Url) (sp : Bool) (hst : Host) (port : Option Nat)
    (segs : List String) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) (hb : ctx.buffer = [])
    (hib : ctx.insideBrackets = false) (hpath : ctx.url.path = .list [])
    (hport0 : ctx.url.port = none) (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hok : hostReadable sp hst)
    (hhne : sp = true ∨ ctx.atSignSeen = true ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hcan : hostParser ctx.toAscii (hostSerializer hst).toList (!sp) = some hst)
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf ctx.url.scheme p = some p)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .authority
        ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))) ctx
      = .ok { ctx.url with
              host := some hst
              port := port
              path := .list segs
              query := q
              fragment := f } := by
  have htail : ∀ c ∈ (pathChars segs ++ qfList q f).head?,
      isTerminator sp (some c) = true := by
    intro c hc
    cases segs with
    | nil =>
      simp only [pathChars, List.nil_append] at hc
      unfold qfList at hc
      cases q with
      | some qs =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
        rw [← hc]
        cases sp <;> decide
      | none =>
        cases f with
        | some fs =>
          simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
          rw [← hc]
          cases sp <;> decide
        | none => simp at hc
    | cons x t =>
      simp only [pathChars, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hc
      rw [← hc]
      cases sp <;> decide
  have hportc : ∀ c ∈ portChars port, ¬c = '@' ∧ isTerminator sp (some c) = false := by
    intro c hc
    cases hp : port with
    | none => rw [hp] at hc; simp [portChars] at hc
    | some p =>
      rw [hp] at hc
      simp only [portChars, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨by decide, by cases sp <;> decide⟩
      · have := toString_digits p c hc
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
        refine ⟨?_, isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
          (intro he; rw [he] at this; revert this; decide)
  -- authority state は区切りまで（host と port）を buffer に積んで host state へ返す
  rw [← List.append_assoc]
  rw [run_authority_host base sp ((hostSerializer hst).toList ++ portChars port)
    (pathChars segs ++ qfList q f) ctx hsp
    (fun h => by
      rw [hb, List.nil_append]
      intro he
      exact hhne (Or.inr (Or.inl h)) (List.append_eq_nil_iff.mp he).1)
    (fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact hostReadable_auth hok c hc
      · exact hportc c hc) htail]
  rw [hb, List.nil_append, List.append_assoc]
  rw [run_host_serialized base sp hst (portChars port ++ (pathChars segs ++ qfList q f))
    { ctx with buffer := [] } hov hsp hib hok]
  cases hp : port with
  | none =>
    rw [show portChars none = [] from rfl, List.nil_append]
    rw [run_host_pathStart base sp (pathChars segs ++ qfList q f)
      { ctx with buffer := [] ++ (hostSerializer hst).toList } hst hov hsp
      (fun h => by simpa using hhne (Or.inl h))
      (fun c hc => ⟨htail c hc, by
        have := htail c hc
        intro he
        rw [he] at this
        cases sp <;> simp [isTerminator] at this⟩)
      (by simpa using hcan)]
    rw [run_pathStart_path base sp segs q f _ ?n1 ?n2 ?n3 rfl ?n4 ?n5 ?n6 hsegs hall ?n7 hfc]
    · rw [← hport0]
    case n1 => exact hsp
    case n2 => exact hov
    case n3 => exact hpath
    case n4 => exact fun _ _ => windowsDriveBuffer_of_not_file hnf
    case n5 => exact hq0
    case n6 => exact hf0
    case n7 => exact hqc
  | some p =>
    obtain ⟨hle, hpo⟩ := hport p hp
    rw [show portChars (some p) = ':' :: (toString p).toList from rfl, List.cons_append]
    rw [run_host_port base sp ((toString p).toList ++ (pathChars segs ++ qfList q f))
      { ctx with buffer := [] ++ (hostSerializer hst).toList } hst hov hsp hib
      (by simpa using hhne (Or.inr (Or.inr (by rw [hp]; simp))))
      (by simpa using hcan)]
    rw [run_port_chunk base sp (toString p).toList (pathChars segs ++ qfList q f) _ ?d1 (toString_digits p)]
    case d1 => exact hsp
    rw [run_port_pathStart base sp (pathChars segs ++ qfList q f) _ ?d2 ?d3 ?d4 ?d5 htail]
    case d2 => exact hov
    case d3 => exact hsp
    case d4 => simp
    case d5 => simp only [List.nil_append, portValue_toString]; exact hle
    simp only [portSet, List.nil_append, portValue_toString, hpo]
    rw [run_pathStart_path base sp segs q f _ ?m1 ?m2 ?m3 rfl ?m4 ?m5 ?m6 hsegs hall ?m7 hfc]
    case m1 => exact hsp
    case m2 => exact hov
    case m3 => exact hpath
    case m4 => exact fun _ _ => windowsDriveBuffer_of_not_file hnf
    case m5 => exact hq0
    case m6 => exact hf0
    case m7 => exact hqc

/--
authority state から先を、credentials も込めて読み切る。

credentials が無ければそのまま host へ、あれば `@` までを username と password に振り分ける。
-/
theorem run_authority_full (base : Option Url) (sp : Bool) (user pass : String) (hst : Host)
    (port : Option Nat) (segs : List String) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) (has : ctx.atSignSeen = false)
    (hb : ctx.buffer = []) (hib : ctx.insideBrackets = false) (hpt : ctx.passwordTokenSeen = false)
    (hpath : ctx.url.path = .list []) (hport0 : ctx.url.port = none)
    (hnf : ¬ctx.url.scheme = "file")
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hu0 : ctx.url.username = "") (hp0 : ctx.url.password = "")
    (hu : ∀ c ∈ user.toList, userinfoSet c = false)
    (hp : ∀ c ∈ pass.toList, userinfoSet c = false)
    (hok : hostReadable sp hst)
    (hhne : sp = true ∨ (user.isEmpty && pass.isEmpty) = false ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hcan : hostParser ctx.toAscii (hostSerializer hst).toList (!sp) = some hst)
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf ctx.url.scheme p = some p)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .authority
        (credChars user pass ++ ((hostSerializer hst).toList
          ++ (portChars port ++ (pathChars segs ++ qfList q f)))) ctx
      = .ok { ctx.url with
              username := user
              password := pass
              host := some hst
              port := port
              path := .list segs
              query := q
              fragment := f } := by
  unfold credChars
  cases hc : (user.isEmpty && pass.isEmpty) with
  | true =>
    have hue : user = "" := by simp_all
    have hpe : pass = "" := by simp_all
    simp only [if_true, List.nil_append]
    rw [run_authority_hostpath base sp hst port segs q f ctx hsp hov hb hib hpath hport0 hnf
      hq0 hf0 hok
      (fun h => hhne (by
        rcases h with h | h | h
        · exact Or.inl h
        · rw [has] at h
          exact absurd h (by simp)
        · exact Or.inr (Or.inr h)))
      hcan hport hsegs hall hqc hfc]
    simp [hue, hpe, hu0, hp0]
  | false =>
    -- credentials がある。`@` までを buffer に積んでから振り分ける。
    have hchunk : ∀ c ∈ user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList),
        ¬c = '@' ∧ isTerminator sp (some c) = false := by
      intro c hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact ⟨(not_userinfoSet (hu c hcm)).1, (not_userinfoSet (hu c hcm)).2.2 sp⟩
      · cases hpc : pass.isEmpty with
        | true => rw [hpc] at hcm; simp at hcm
        | false =>
          rw [hpc] at hcm
          simp only [Bool.false_eq_true, if_false, List.mem_cons] at hcm
          rcases hcm with rfl | hcm
          · exact ⟨by decide, by cases sp <;> decide⟩
          · exact ⟨(not_userinfoSet (hp c hcm)).1, (not_userinfoSet (hp c hcm)).2.2 sp⟩
    simp only [Bool.false_eq_true, if_false]
    rw [List.append_assoc (user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList))
      ['@'] ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))),
      List.singleton_append]
    rw [run_authority_chunk base sp
      (user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList))
      ('@' :: ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) ctx hsp hchunk]
    rw [run_authority_at base _ _ ?a1]
    case a1 => exact has
    rw [hb, List.nil_append, hpt]
    cases hpe : pass.isEmpty with
    | true =>
      have hpe' : pass = "" := by simp_all
      simp only [if_true, List.append_nil]
      rw [userinfoFold_user user.toList ctx.url hu]
      rw [run_authority_hostpath base sp hst port segs q f _ ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7
        ?b11 ?b12 hok ?b8 ?b9 ?b10 hsegs hall ?b13 hfc]
      case b1 => exact hsp
      case b2 => exact hov
      case b3 => rfl
      case b4 => exact hib
      case b5 => exact hpath
      case b6 => exact hport0
      case b7 => exact hnf
      case b8 => intro _; exact hhne (Or.inr (Or.inl hc))
      case b9 => exact hcan
      case b10 => exact hport
      case b11 => exact hq0
      case b12 => exact hf0
      case b13 => exact hqc
      simp [hu0, hpe', String.ofList_toList, hp0]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [userinfoFold_split ctx.url user.toList pass.toList hu hp]
      rw [run_authority_hostpath base sp hst port segs q f _ ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
        ?c11 ?c12 hok ?c8 ?c9 ?c10 hsegs hall ?c13 hfc]
      case c1 => exact hsp
      case c2 => exact hov
      case c3 => rfl
      case c4 => exact hib
      case c5 => exact hpath
      case c6 => exact hport0
      case c7 => exact hnf
      case c8 => intro _; exact hhne (Or.inr (Or.inl hc))
      case c9 => exact hcan
      case c10 => exact hport
      case c11 => exact hq0
      case c12 => exact hf0
      case c13 => exact hqc
      simp [hu0, hp0, String.ofList_toList]

/--
host を持つ URL の serialize は、`//` と credentials と host と port と path、
それに query と fragment を並べたもの。
-/
theorem serializerTail_authority (s user pass : String) (hst : Host) (port : Option Nat)
    (segs : List String) (q f : Option String) :
    (serializerTail
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f } false).toList
      = '/' :: '/' :: (credChars user pass
          ++ ((hostSerializer hst).toList
            ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
  have hcred :
      ({ scheme := s
         username := user
         password := pass
         host := some hst
         port := port
         path := .list segs
         query := q
         fragment := f } : Url).includesCredentials
        = !(user.isEmpty && pass.isEmpty) := by
    simp [Url.includesCredentials, String.isEmpty]
  simp only [serializerTail, hcred, credChars, portChars, qfList]
  cases hc : (user.isEmpty && pass.isEmpty) <;> cases hp : pass.isEmpty <;> cases hpo : port <;>
    cases hq : q <;> cases hf : f <;>
    simp [String.toList_append, pathSerializer_pathChars]

/-- userinfo set に入らない文字は C0 control でも space でもない。 -/
theorem ne_c0_of_userinfoSet {c : Char} (h : userinfoSet c = false) :
    isC0ControlOrSpace c = false := by
  refine ne_c0_of_c0Set ?_ ?_
  · simp only [userinfoSet, pathSet, querySet, Bool.or_eq_false_iff] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  · intro he; rw [he] at h; revert h; decide

/-- credentials の先頭の文字は `/` でも `\\` でもない。 -/
theorem credChars_head {user pass : String} {c : Char}
    (hu : ∀ x ∈ user.toList, userinfoSet x = false)
    (h : c ∈ (credChars user pass).head?) : ¬c = '/' ∧ ¬c = '\\' := by
  unfold credChars at h
  split at h
  · simp at h
  · cases hux : user.toList with
    | nil =>
      rw [hux] at h
      cases hpx : pass.isEmpty with
      | true =>
        rw [hpx] at h
        simp only [List.nil_append, if_true, List.head?_cons, Option.mem_def,
          Option.some.injEq] at h
        rw [← h]
        exact ⟨by decide, by decide⟩
      | false =>
        rw [hpx] at h
        simp only [List.nil_append, Bool.false_eq_true, if_false, List.cons_append,
          List.head?_cons, Option.mem_def, Option.some.injEq] at h
        rw [← h]
        exact ⟨by decide, by decide⟩
    | cons d t =>
      rw [hux] at h
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at h
      have := not_userinfoSet (hu d (by rw [hux]; simp))
      rw [← h]
      exact ⟨by
          have h2 := this.2.2 false
          intro he; rw [he] at h2; revert h2; decide,
        by
          have h2 := hu d (by rw [hux]; simp)
          intro he; rw [he] at h2; revert h2; decide⟩

/-- credentials に現れる文字は、username か password の文字か `:` か `@` である。 -/
theorem credChars_mem {user pass : String} {c : Char} (h : c ∈ credChars user pass) :
    c ∈ user.toList ∨ c ∈ pass.toList ∨ c = ':' ∨ c = '@' := by
  unfold credChars at h
  split at h
  · simp at h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · split at h
        · simp at h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inl h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inr (Or.inr h))

/-- scheme state の `:` から authority state まで。special かどうかで経路が違うが行き先は同じ。 -/
theorem run_scheme_authority (sp : Bool) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = sp)
    (hhead : sp = true → ∀ c ∈ rest.head?, ¬c = '/' ∧ ¬c = '\\') :
    run none .scheme (':' :: '/' :: '/' :: rest) ctx
      = run none .authority rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  cases sp with
  | false =>
    rw [run_scheme_pathOrAuthority none ('/' :: rest) ctx hov hf (by simpa using hsp)]
    rw [run_pathOrAuthority_authority]
  | true =>
    rw [run_scheme_specialAuthoritySlashes ('/' :: '/' :: rest) ctx hov hf (by simpa using hsp)]
    rw [run_specialAuthoritySlashes]
    rw [run_specialAuthorityIgnoreSlashes none rest _ (hhead rfl)]

/--
**host を持つ URL は、serialize して parse し直すと元に戻る。**

special かどうかを `sp` で持つので、`sc://h/a` も `http://h/a/b` もこれ一つで済む。
credentials も扱う。除いてあるのは `file:`、port、IPv6 host、
それと host が空で path が空でない場合（serialize すると `//` が続いてしまう）である。
-/
theorem roundtrip_host {s user pass : String} {sp : Bool} {hst : Host} {port : Option Nat}
    {segs : List String} {q f : Option String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = sp) (hfile : ¬s = "file")
    (hu : ∀ c ∈ user.toList, userinfoSet c = false)
    (hp : ∀ c ∈ pass.toList, userinfoSet c = false)
    (hcan : hostParser asciiDomainToASCII (hostSerializer hst).toList (!sp) = some hst)
    (hok : hostReadable sp hst)
    (hnc : ∀ c ∈ (hostSerializer hst).toList, isC0ControlOrSpace c = false)
    (hhead : sp = true →
      ∀ c ∈ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))).head?,
      ¬c = '/' ∧ ¬c = '\\')
    (hhne : sp = true ∨ (user.isEmpty && pass.isEmpty) = false ∨ port ≠ none →
      (hostSerializer hst).toList ≠ [])
    (hport : ∀ p, port = some p → p ≤ 65535 ∧ portOf s p = some p)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if isSpecialScheme s then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false) :
    basicUrlParse (urlSerializer
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f }) none
      = some
        { scheme := s
          username := user
          password := pass
          host := some hst
          port := port
          path := .list segs
          query := q
          fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hstr : (urlSerializer
      { scheme := s
        username := user
        password := pass
        host := some hst
        port := port
        path := .list segs
        query := q
        fragment := f }).toList
      = s.toList ++ ':' :: '/' :: '/'
        :: (credChars user pass
          ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
    simp only [urlSerializer, String.toList_append, serializerTail_authority]
    simp
  have hallc : ∀ c ∈ s.toList ++ ':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))),
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
      · rcases List.mem_cons.mp hcm with rfl | hcm
        · decide
        · rcases List.mem_cons.mp hcm with rfl | hcm
          · decide
          · rcases List.mem_append.mp hcm with hcm | hcm
            · rcases credChars_mem hcm with h | h | rfl | rfl
              · exact ne_c0_of_userinfoSet (hu c h)
              · exact ne_c0_of_userinfoSet (hp c h)
              · decide
              · decide
            · rcases List.mem_append.mp hcm with hcm | hcm
              · exact hnc c hcm
              · rcases List.mem_append.mp hcm with hcm | hcm
                · cases hpo : port with
                  | none => rw [hpo] at hcm; simp [portChars] at hcm
                  | some p =>
                    rw [hpo] at hcm
                    simp only [portChars, List.mem_cons] at hcm
                    rcases hcm with rfl | hcm
                    · decide
                    · have := toString_digits p c hcm
                      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
                      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
                      omega
                · rcases List.mem_append.mp hcm with hcm | hcm
                  · cases segs with
                    | nil => simp [pathChars] at hcm
                    | cons x t =>
                      rcases List.mem_cons.mp hcm with rfl | hcm
                      · decide
                      · rcases intercal_mem (x :: t) c hcm with rfl | ⟨y, hy, hcy⟩
                        · decide
                        · exact ne_c0_of_c0Set (c0Set_of_pathSet ((hall y hy).1 c hcy).1)
                            (ne_space_of_pathSet ((hall y hy).1 c hcy).1)
                  · exact qfList_c0 (fun x hx c hc => querySet_of_ite (hqc x hx c hc)) hfc c hcm
  have hpre : preprocess (urlSerializer
      { scheme := s
        username := user
        password := pass
        host := some hst
        port := port
        path := .list segs
        query := q
        fragment := f })
      = s.toList ++ ':' :: '/' :: '/'
        :: (credChars user pass
          ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) := by
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
  have hhead2 : sp = true → ∀ c ∈ (credChars user pass
      ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))).head?,
      ¬c = '/' ∧ ¬c = '\\' := by
    intro hspv c hc
    cases hcc : credChars user pass with
    | nil =>
      rw [hcc, List.nil_append] at hc
      exact hhead hspv c hc
    | cons d t =>
      rw [hcc] at hc
      simp only [List.cons_append, List.head?_cons] at hc
      exact credChars_head hu (by rw [hcc]; simpa using hc)
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a
    (rest ++ ':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))))) haa]
  rw [run_scheme_prefix none rest
    (':' :: '/' :: '/'
      :: (credChars user pass
        ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f))))) _ hr]
  rw [run_scheme_authority sp
    (credChars user pass
      ++ ((hostSerializer hst).toList ++ (portChars port ++ (pathChars segs ++ qfList q f)))) _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp) hhead2]
  rw [hbuf, String.ofList_toList]
  rw [run_authority_full none sp user pass hst port segs q f _ ?j1 rfl rfl rfl rfl rfl rfl rfl ?j2
    rfl rfl rfl rfl hu hp hok ?j3 ?j4 ?j5 hsegs hall ?j6 hfc]
  case j1 => simp [Url.isSpecial, hsp]
  case j2 => simpa using hfile
  case j3 => exact hhne
  case j4 => simpa using hcan
  case j5 => exact hport
  case j6 => exact hqc

/-- 仮定が空でないことの確認。`sc://h/a` は実際にこの形である。 -/
example : basicUrlParse
      (urlSerializer { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- host が空でも往復する。`sc:///a` の形である。 -/
example : basicUrlParse
      (urlSerializer { scheme := "sc", host := some .empty, path := .list ["a"] }) none
    = some { scheme := "sc", host := some .empty, path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- port が付いていても往復する。`sc://h:8080/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.opaque "h"), port := some 8080,
        path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.opaque "h"), port := some 8080,
             path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := some 8080) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- query と fragment が付いていても往復する。`sc://h/a?q#f` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.opaque "h"), path := .list ["a"],
        query := some "q", fragment := some "f" }) none
    = some { scheme := "sc", host := some (.opaque "h"), path := .list ["a"],
             query := some "q", fragment := some "f" } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by simp; decide) (by simp; decide) (by decide) (by decide)

/-- IPv6 host も往復する。`sc://[::]/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
        path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
             path := .list ["a"] } :=
  roundtrip_host (a := 's') (rest := ['c']) (user := "") (pass := "") (sp := false)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hostReadable_ipv6 _ _) (ipv6_no_c0 _)
    (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-- special な URL の IPv6 host も往復する。`http://[::]/a` の形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "http", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
        path := .list ["a"] }) none
    = some { scheme := "http", host := some (.ipv6 [0, 0, 0, 0, 0, 0, 0, 0]),
             path := .list ["a"] } :=
  roundtrip_host (a := 'h') (rest := ['t', 't', 'p']) (user := "") (pass := "") (sp := true)
    (port := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hostReadable_ipv6 _ _) (ipv6_no_c0 _)
    (by decide) (by decide)
    (by decide) (by simp) (by simp) (by decide) (by decide)

/-!
`http://h/a` がこの形であることは `decide` では確かめられない。
host parser が domain parser を通り、そこが UTF-8 の encode / decode（well-founded 再帰）を
呼ぶので、`Decidable` 実体が簡約しないためである（`#audit_axioms` の制約でもある）。
`#eval` では `hostParser asciiDomainToASCII "h".toList false = some (.domain "h")` になり、
`UrlMain.lean` の ROUNDTRIP と CANONICAL が WPT の 820 件で同じことを見ている。

IPv6 host は host parser が `[` の分岐へ行き domain parser を通らないので、
`http://[::]/a` の方は `decide` で確かめられる。ただし `toHexString` は well-founded 再帰で
簡約しないので、0 以外の piece を持つ address（`[::1]` など）は例に書けない。
-/

end Url
