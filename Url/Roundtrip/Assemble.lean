import Url.Roundtrip.Special

/-!
# 組み立て
-/

namespace Url

open Infra

/-! ## 組み立て -/

/--
opaque path state が区切りまでの文字を読み切る。

`?` と `#` は出口なので入力に無いこととした。space はそのまま積まれるが、
**末尾の space だけは別**である（次が `?` か `#` なら `%20` になる）。
parser はそういう opaque path を作らないので、無いことを仮定する。
-/
theorem run_opaquePath_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx) (p : String),
    ctx.url.path = .opaque p →
    (∀ c ∈ l, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#') →
    (∀ c ∈ l.getLast?, ¬c = ' ') →
    run base .opaquePath (l ++ tail) ctx
      = run base .opaquePath tail
          { ctx with url := { ctx.url with path := .opaque (p ++ String.ofList l) } } := by
  intro l
  induction l with
  | nil =>
    intro tail ctx p hp _ _
    simp only [List.nil_append, String.ofList_nil]
    have h1 : ({ ctx.url with path := Path.opaque (p ++ "") } : Url)
        = { ctx.url with path := ctx.url.path } := by rw [hp]; simp
    rw [h1]
  | cons c l' ih =>
    intro tail ctx p hp hd hend
    have hc := hd c (by simp)
    have henc : encChar c0ControlSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    have hend' : ∀ x ∈ l'.getLast?, ¬x = ' ' := by
      intro x hx
      refine hend x ?_
      cases l' with
      | nil => simp at hx
      | cons d t => rw [List.getLast?_cons_cons]; exact hx
    have hstep : run base .opaquePath ((c :: l') ++ tail) ctx
        = run base .opaquePath (l' ++ tail)
            { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) } := by
      by_cases hsp : c = ' '
      · subst hsp
        rw [List.cons_append, run, step]
        cases hl : l' with
        | nil =>
          exact absurd (hend ' ' (by rw [hl]; rfl)) (by simp)
        | cons d t =>
          have h1 : ¬d = '?' := (hd d (by rw [hl]; simp)).2.1
          have h2 : ¬d = '#' := (hd d (by rw [hl]; simp)).2.2
          simp only [List.cons_append, List.head?_cons]
          split
          · next hq => exact absurd (Option.some.inj hq) h1
          · next hq => exact absurd (Option.some.inj hq) h2
          · simp [henc]
      · rw [List.cons_append, run, step]
        all_goals first
          | rfl
          | (intro he; exact absurd he hc.2.1)
          | (intro he; exact absurd he hc.2.2)
          | (intro he; exact absurd he hsp)
    rw [hstep]
    rw [ih tail { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) }
      (p ++ encChar c0ControlSet c) (by simp [appendOpaque, hp])
      (fun x hx => hd x (by simp [hx])) hend']
    simp only [appendOpaque, hp, henc]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- 末尾の一文字。区切りの後ろが空なら区切り自身が最後になる。 -/
theorem getLast?_mid (l1 : List Char) (c : Char) (l2 : List Char) :
    (l1 ++ c :: l2).getLast? = if l2.isEmpty then some c else l2.getLast? := by
  rw [← List.head?_reverse, reverse_head_mid]
  cases l2 with
  | nil => simp
  | cons d t => exact List.head?_reverse

/--
**opaque path を持つ URL は、serialize して parse し直すと元に戻る。**

`parse ∘ serialize = id` のうち、いちばん短い経路
（scheme start → scheme → opaque path → query → fragment）を閉じたものである。
仮定はその経路を通る形であること、つまり `canonicalUrl` のうち
scheme・opaque path・query・fragment に当たる分である。
-/
theorem roundtrip_opaque {s o : String} {q f : Option String} {a : Char} {rest : List Char}
    (hs : s.toList = a :: rest) (ha : isAsciiLowerAlpha a = true)
    (hr : ∀ c ∈ rest, schemeChar c = true)
    (hlow : s.toList.map asciiLowerChar = s.toList)
    (hsp : isSpecialScheme s = false)
    (ho : ∀ c ∈ o.toList, c0ControlSet c = false ∧ ¬c = '?' ∧ ¬c = '#')
    (hlast : ∀ c ∈ o.toList.getLast?, ¬c = ' ')
    (hhead : ∀ c ∈ o.toList.head?, ¬c = '/')
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList, querySet c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    basicUrlParse
        (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f }) none
      = some { scheme := s, path := .opaque o, query := q, fragment := f } := by
  have haa : isAsciiAlpha a = true := by
    simp only [isAsciiAlpha, Bool.or_eq_true]; exact Or.inr ha
  have hstr : (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f }).toList
      = s.toList ++ ':' :: (o.toList ++ qfList q f) := by
    cases q <;> cases f <;>
      simp [urlSerializer, serializerTail, pathSerializer, qfList]
  have hbuf : ([] : List Char) ++ [asciiLowerChar a] ++ rest.map asciiLowerChar = s.toList := by
    rw [List.nil_append, List.singleton_append, ← List.map_cons, ← hs, hlow]
  have hfile : ¬s = "file" := by
    intro he; rw [he] at hsp; exact absurd hsp (by decide)
  -- 前処理が何もしないこと。前後の一文字と、tab / newline が無いことを見る。
  have hpre : preprocess (urlSerializer { scheme := s, path := .opaque o, query := q, fragment := f })
      = s.toList ++ ':' :: (o.toList ++ qfList q f) := by
    rw [preprocess_eq_self ?head ?last ?tab, hstr]
    case head =>
      intro c hcm
      rw [hstr, hs] at hcm
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hcm
      subst hcm
      simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
      omega
    case last =>
      intro c hcm
      rw [hstr, List.head?_reverse, getLast?_mid] at hcm
      cases hB : (o.toList ++ qfList q f).isEmpty with
      | true =>
        rw [hB] at hcm
        simp at hcm
        subst hcm; decide
      | false =>
        rw [hB] at hcm
        -- 最後の成分で場合分けする。
        cases f with
        | some fs =>
          rw [show o.toList ++ qfList q (some fs) = (o.toList ++ (match q with
                | none => [] | some x => '?' :: x.toList)) ++ '#' :: fs.toList from by
              unfold qfList; cases q <;> simp, getLast?_mid] at hcm
          cases hfs : fs.toList.isEmpty with
          | true =>
            rw [hfs] at hcm
            simp at hcm
            subst hcm; decide
          | false =>
            rw [hfs] at hcm
            exact ne_c0_of_c0Set
              (c0Set_of_fragmentSet (hfc fs rfl c (List.mem_of_mem_getLast? hcm)))
              (ne_space_of_fragmentSet (hfc fs rfl c (List.mem_of_mem_getLast? hcm)))
        | none =>
          cases q with
          | some qs =>
            rw [show o.toList ++ qfList (some qs) none = o.toList ++ '?' :: qs.toList from by
                simp [qfList], getLast?_mid] at hcm
            cases hqs : qs.toList.isEmpty with
            | true =>
              rw [hqs] at hcm
              simp at hcm
              subst hcm; decide
            | false =>
              rw [hqs] at hcm
              exact ne_c0_of_c0Set
                (c0Set_of_querySet (hqc qs rfl c (List.mem_of_mem_getLast? hcm)))
                (ne_space_of_querySet (hqc qs rfl c (List.mem_of_mem_getLast? hcm)))
          | none =>
            rw [show o.toList ++ qfList (none : Option String) (none : Option String)
                = o.toList from by unfold qfList; simp] at hcm
            exact ne_c0_of_c0Set (ho c (List.mem_of_mem_getLast? hcm)).1 (hlast c hcm)
    case tab =>
      intro c hcm
      rw [hstr] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · rw [hs] at hcm
        rcases List.mem_cons.mp hcm with rfl | hcm
        · simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
          omega
        · exact schemeChar_ne_tab (hr c hcm)
      · rcases List.mem_cons.mp hcm with rfl | hcm
        · decide
        · rcases List.mem_append.mp hcm with hcm | hcm
          · exact ne_tab_of_c0Set (ho c hcm).1
          · unfold qfList at hcm
            rcases List.mem_append.mp hcm with hcm | hcm
            · cases q with
              | none => simp at hcm
              | some qs =>
                rcases List.mem_cons.mp hcm with rfl | hcm
                · decide
                · exact ne_tab_of_c0Set (c0Set_of_querySet (hqc qs rfl c hcm))
            · cases f with
              | none => simp at hcm
              | some fs =>
                rcases List.mem_cons.mp hcm with rfl | hcm
                · decide
                · exact ne_tab_of_c0Set (c0Set_of_fragmentSet (hfc fs rfl c hcm))
  unfold basicUrlParse
  rw [hpre, hs, List.cons_append]
  rw [run_schemeStart_step none _ a (rest ++ ':' :: (o.toList ++ qfList q f)) haa]
  rw [run_scheme_prefix none rest (':' :: (o.toList ++ qfList q f)) _ hr]
  rw [run_scheme_opaque none (o.toList ++ qfList q f) _ rfl
    (by rw [hbuf, String.ofList_toList]; exact hfile)
    (by rw [hbuf, String.ofList_toList]; exact hsp)
    (by intro r hrr
        cases hoo : o.toList with
        | nil =>
          rw [hoo] at hrr
          simp only [List.nil_append] at hrr
          unfold qfList at hrr
          cases q with
          | some qs => simp at hrr; rw [← hrr]; decide
          | none =>
            cases f with
            | some fs => simp at hrr; rw [← hrr]; decide
            | none => simp at hrr
        | cons d t =>
          rw [hoo] at hrr
          simp only [List.cons_append, List.head?_cons, Option.mem_def,
            Option.some.injEq] at hrr
          subst hrr
          exact hhead d (by rw [hoo]; rfl))]
  rw [hbuf, String.ofList_toList]
  rw [run_opaquePath_chunk none o.toList (qfList q f) _ "" rfl ho hlast]
  rw [run_opaquePath_qf none _ q f rfl rfl rfl rfl
    (fun x hx c hc => by simpa [Url.isSpecial, hsp] using hqc x hx c hc)
    (fun x hx c hc => hfc x hx c hc)]
  simp

/-- 仮定が空でないことの確認。`sc:x?a#b` は実際にこの形である。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", path := .opaque "x", query := some "a", fragment := some "b" }) none
    = some { scheme := "sc", path := .opaque "x", query := some "a", fragment := some "b" } :=
  roundtrip_opaque (a := 's') (rest := ['c']) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Url
