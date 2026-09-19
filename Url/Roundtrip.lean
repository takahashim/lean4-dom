import Url.Roundtrip.Host

/-!
# **URL の往復**

serialize して parse すると元に戻ることの、最後の組み立て。

一つの file が 3,600 行を超えていたので節ごとに切り分けた。中身は次の file にある。

| file | 内容 |
| --- | --- |
| `Url/Roundtrip/Canonical.lean` | canonical form と正規形の道具 |
| `Url/Roundtrip/Query.lean` | query と fragment の往復 |
| `Url/Roundtrip/Chars.lean` | 文字の性質 |
| `Url/Roundtrip/Path.lean` | path の往復 |
| `Url/Roundtrip/Special.lean` | special scheme の往復 |
| `Url/Roundtrip/Assemble.lean` | 組み立て |
| `Url/Roundtrip/Port.lean` | port の往復 |
| `Url/Roundtrip/Authority.lean` | authority の往復 |
| `Url/Roundtrip/Ipv6Chars.lean` | IPv6 serializer が出す文字 |
| `Url/Roundtrip/HostRun.lean` | host state の走行 |
| `Url/Roundtrip/Ipv6Host.lean` | authority の走行と host の往復 |
| `Url/Roundtrip/File.lean` | `file:` の往復 |
| `Url/Roundtrip/Host.lean` | host の条件 |
-/

namespace Url

open Infra

/-! ## まとめ

四つの経路を `canonicalUrl` から選び分けて一つの定理にする。
-/

/-- canonical な scheme の文字は、小文字にしても変わらない。 -/
theorem asciiLowerChar_of_schemeChar {c : Char}
    (h : isAsciiLowerAlpha c = true ∨ schemeChar c = true ∧ isAsciiUpperAlpha c = false) :
    asciiLowerChar c = c := by
  unfold asciiLowerChar
  rcases h with h | h
  · rw [if_neg ?_]
    simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le]
    omega
  · rw [if_neg (by simp [h.2])]

/-- canonical な scheme の残りの文字は scheme の文字で、大文字ではない。 -/
theorem schemeChar_of_canonical {c : Char}
    (h : (isAsciiDigit c || isAsciiLowerAlpha c || c == '+' || c == '-' || c == '.') = true) :
    schemeChar c = true ∧ isAsciiUpperAlpha c = false := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  simp only [schemeChar, isAsciiAlphanumeric, isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha,
    isAsciiDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.eq_false_iff, ne_eq, not_and, Nat.not_le] at *
  rcases h with (((h | h) | h) | h) | h <;> simp_all <;> omega

/-- canonical な scheme は、先頭が小文字 alpha、残りが scheme の文字で、すでに小文字である。 -/
theorem canonicalScheme_shape {s : String} (h : canonicalScheme s = true) :
    ∃ a rest, s.toList = a :: rest ∧ isAsciiLowerAlpha a = true ∧
      (∀ c ∈ rest, schemeChar c = true) ∧ s.toList.map asciiLowerChar = s.toList := by
  unfold canonicalScheme at h
  match hsl : s.toList, h with
  | [], h => simp at h
  | a :: rest, h =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨a, rest, rfl, h.1, fun c hc => (schemeChar_of_canonical (h.2 c hc)).1, ?_⟩
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨asciiLowerChar_of_schemeChar (Or.inl h.1), ?_⟩
    exact map_self_of_mem
      (fun c hc => asciiLowerChar_of_schemeChar (Or.inr (schemeChar_of_canonical (h.2 c hc))))

/-- `encodedWith` から文字ごとの条件を取り出す。 -/
theorem encodedWith_mem {set : Char → Bool} {s : String} (h : encodedWith set s = true) :
    ∀ c ∈ s.toList, set c = false := by
  unfold encodedWith at h
  simp only [List.all_eq_true, Bool.not_eq_true'] at h
  exact h

/-- 空の入力を opaque host として読むと empty host になる。 -/
theorem hostParser_nil_opaque {f : List Char → Option String} :
    hostParser f [] true = some Host.empty := rfl

/-- 空の入力を domain として読むことはできない。 -/
theorem hostParser_nil_domain {f : List Char → Option String} :
    hostParser f [] false = none := rfl

/-- host を serialize した文字列は Windows drive letter にならない。 -/
theorem not_drive_of_hostReadable {sp : Bool} {h : Host} (hok : hostReadable sp h) :
    isWindowsDrive (hostSerializer h).toList = false := by
  rcases hok with hf | ⟨inner, he, _⟩
  · unfold isWindowsDrive
    split
    · rename_i a b hb
      have hb2 := hf b (by rw [hb]; simp)
      have hne1 : ¬b = ':' := by intro hx; rw [hx] at hb2; revert hb2; decide
      have hne2 : ¬b = '|' := by intro hx; rw [hx] at hb2; revert hb2; decide
      simp [hne1, hne2]
    · rfl
  · rw [he]
    unfold isWindowsDrive
    split
    · rename_i a b hb
      simp only [List.cons.injEq] at hb
      rw [← hb.1]
      simp [isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha]
    · rfl

/-- path set に入らない文字は `?` でも `#` でもない。 -/
theorem ne_qh_of_pathSet {c : Char} (h : pathSet c = false) : ¬c = '?' ∧ ¬c = '#' := by
  constructor <;> (intro he; rw [he] at h; revert h; decide)

/--
**canonical な record は、serialize して parse し直すと元に戻る。**

`ValidUrl`（§4.1 の不変条件）と `canonicalUrl`（parser の出力の形）だけを仮定する。
path の形で四つの経路を選び分け、それぞれの仮定を二つの述語から出す。
-/
theorem roundtrip_canonical {u : Url} (hv : ValidUrl u) (hc : canonicalUrl u = true) :
    basicUrlParse (urlSerializer u) none = some u := by
  simp only [canonicalUrl, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩ := hc
  obtain ⟨a, rest, hs, ha, hr, hlow⟩ := canonicalScheme_shape c1
  obtain ⟨sc, un, pw, ho, po, pa, qu, fr⟩ := u
  cases pa with
  | «opaque» o =>
    have hop : Url.hasOpaquePath ⟨sc, un, pw, ho, po, Path.opaque o, qu, fr⟩ = true := rfl
    have hsp : isSpecialScheme sc = false := by
      have h2 := hv.specialHasList
      cases hx : isSpecialScheme sc with
      | false => rfl
      | true =>
        rw [hop] at h2
        simp [Url.isSpecial, hx] at h2
    have hcred := hv.opaqueNoCredentials hop
    have hport := hv.opaqueNoPort hop
    have hhost := hv.opaqueNoHost hop
    simp only [Url.includesCredentials, Bool.or_eq_false_iff, Bool.not_eq_false',
      String.isEmpty_iff] at hcred
    simp only at hcred hport hhost
    obtain ⟨hu0, hp0⟩ := hcred
    subst hu0
    subst hp0
    subst hport
    subst hhost
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      List.all_eq_true] at c7
    refine roundtrip_opaque hs ha hr hlow hsp ?ho ?hlast ?hhead ?hqc ?hfc
    case ho =>
      intro c hcm
      have h2 := c7.1.2 c hcm
      simp only [bne_iff_ne, ne_eq] at h2
      exact ⟨encodedWith_mem c7.1.1.1 c hcm, h2.1, h2.2⟩
    case hlast =>
      intro c hcm he
      simp only [Option.mem_def] at hcm
      exact c7.1.1.2 (by rw [← he]; exact hcm)
    case hhead =>
      intro c hcm he
      simp only [Option.mem_def] at hcm
      exact c7.2 (by rw [← he]; exact hcm)
    case hqc =>
      intro x hx c hcm
      simp only at c5
      rw [hx] at c5
      rw [if_neg (by simp [Url.isSpecial, hsp])] at c5
      exact encodedWith_mem c5 c hcm
    case hfc =>
      intro x hx c hcm
      simp only at c6
      rw [hx] at c6
      exact encodedWith_mem c6 c hcm
  | list segs =>
    have hps := hv.pathSegs
    simp only [pathSegsOk_list, List.all_eq_true] at hps
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at c7
    have hseg : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false) ∧
        isSingleDot x.toList = false ∧ isDoubleDot x.toList = false ∧
        (∀ c ∈ x.toList, ¬c = '/') ∧
        (isSpecialScheme sc = true → ∀ c ∈ x.toList, ¬c = '\\') := by
      intro x hx
      have h2 := c7 x hx
      refine ⟨encodedWith_mem h2.1.1.1, h2.1.1.2, h2.1.2,
        fun c hc => noSlash_mem (hps x hx) hc, ?_⟩
      intro hsv c hc
      have h3 := h2.2
      simp only [Url.isSpecial, hsv, Bool.not_true, Bool.false_or, List.all_eq_true,
        bne_iff_ne, ne_eq] at h3
      exact h3 c hc
    cases ho with
    | none =>
      have hsp : isSpecialScheme sc = false := by
        cases hx : isSpecialScheme sc with
        | false => rfl
        | true => simp [Url.isSpecial, hx] at c13
      have hcred := hv.nullHostNoCredentials rfl
      have hport := hv.nullHostNoPort rfl
      simp only [Url.includesCredentials, Bool.or_eq_false_iff, Bool.not_eq_false',
        String.isEmpty_iff] at hcred
      simp only at hcred hport
      obtain ⟨hu0, hp0⟩ := hcred
      subst hu0
      subst hp0
      subst hport
      have hne : segs ≠ [] := by
        cases segs with
        | nil => simp at c8
        | cons x t => simp
      refine roundtrip_path hs ha hr hlow hsp hne ?hqc ?hfc ?hall
      case hqc =>
        intro x hx c hcm
        simp only at c5
        rw [hx] at c5
        rw [if_neg (by simp [Url.isSpecial, hsp])] at c5
        exact encodedWith_mem c5 c hcm
      case hfc =>
        intro x hx c hcm
        simp only at c6
        rw [hx] at c6
        exact encodedWith_mem c6 c hcm
      case hall =>
        intro x hx
        obtain ⟨h1, h2, h3, h4, _⟩ := hseg x hx
        exact ⟨fun c hc => ⟨h1 c hc, h4 c hc, (ne_qh_of_pathSet (h1 c hc)).1,
          (ne_qh_of_pathSet (h1 c hc)).2⟩, h2, h3⟩
    | some hst =>
      have hcan : hst = Host.empty ∨
          hostParser asciiDomainToASCII (hostSerializer hst).toList
            (!Url.isSpecial ⟨sc, un, pw, some hst, po, Path.list segs, qu, fr⟩) = some hst := by
        cases hst with
        | empty => exact Or.inl rfl
        | domain d => exact Or.inr (by simpa using c10)
        | ipv4 x => exact Or.inr (by simpa using c10)
        | ipv6 x => exact Or.inr (by simpa using c10)
        | «opaque» o => exact Or.inr (by simpa using c10)
      obtain ⟨hok, hnc⟩ := hostReadable_of_canonical hcan
      by_cases hfile : sc = "file"
      · subst hfile
        have hcred := hv.fileNoCredentials rfl
        have hport := hv.fileNoPort rfl
        simp only [Url.includesCredentials, Bool.or_eq_false_iff, Bool.not_eq_false',
          String.isEmpty_iff] at hcred
        simp only at hcred hport
        obtain ⟨hu0, hp0⟩ := hcred
        subst hu0
        subst hp0
        subst hport
        have hsp : Url.isSpecial ⟨"file", "", "", some hst, none, Path.list segs, qu, fr⟩
            = true := rfl
        rw [hsp] at hcan hok
        have hne : segs ≠ [] := by
          cases segs with
          | nil => simp [Url.isSpecial, isSpecialScheme] at c9
          | cons x t => simp
        refine roundtrip_file (by simpa using hcan) hok hnc
          (not_drive_of_hostReadable hok) ?hloc hne ?hdrive ?hall ?hqc ?hfc
        case hloc =>
          simp only [bne_iff_ne, ne_eq, Bool.or_eq_true] at c11
          rcases c11 with h | h
          · exact absurd trivial h
          · exact h
        case hdrive =>
          intro x hx
          cases segs with
          | nil => exact absurd rfl hne
          | cons y t =>
            simp only [List.head?_cons, Option.some.injEq] at hx
            subst hx
            simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at c12
            rcases c12 with (h | h) | h
            · exact absurd trivial h
            · exact Or.inl h
            · exact Or.inr h
        case hall =>
          intro x hx
          obtain ⟨h1, h2, h3, h4, h5⟩ := hseg x hx
          exact ⟨fun c hc => ⟨h1 c hc, isTerminator_false (h4 c hc)
            (ne_qh_of_pathSet (h1 c hc)).1 (ne_qh_of_pathSet (h1 c hc)).2
            (fun _ => h5 (by decide) c hc)⟩, h2, h3⟩
        case hqc =>
          intro x hx c hcm
          simp only at c5
          rw [hx] at c5
          rw [if_pos (show Url.isSpecial ⟨"file", "", "", some hst, none, Path.list segs,
            some x, fr⟩ = true from rfl)] at c5
          exact encodedWith_mem c5 c hcm
        case hfc =>
          intro x hx c hcm
          simp only at c6
          rw [hx] at c6
          exact encodedWith_mem c6 c hcm
      · have hok' : hostReadable (isSpecialScheme sc) hst := by
          simpa [Url.isSpecial] using hok
        have hkind := hv.hostKind
        have hempty : (hostSerializer hst).toList = [] → hst = Host.empty := by
          intro he
          rcases hcan with h | h
          · exact h
          · rw [he] at h
            cases hsx : isSpecialScheme sc with
            | false =>
              rw [show Url.isSpecial ⟨sc, un, pw, some hst, po, Path.list segs, qu, fr⟩ = false from
                by simp [Url.isSpecial, hsx]] at h
              rw [Bool.not_false, hostParser_nil_opaque] at h
              exact (Option.some.injEq _ _ ▸ h).symm
            | true =>
              rw [show Url.isSpecial ⟨sc, un, pw, some hst, po, Path.list segs, qu, fr⟩ = true from
                by simp [Url.isSpecial, hsx]] at h
              rw [Bool.not_true, hostParser_nil_domain] at h
              exact absurd h (by simp)
        have hnotempty : isSpecialScheme sc = true → ¬hst = Host.empty := by
          intro hsv he
          rw [he] at hkind
          simp only [hostKindOkOf, Bool.or_eq_true, Bool.not_eq_true', hsv, beq_iff_eq] at hkind
          rcases hkind with h | h
          · exact absurd h (by simp)
          · exact hfile h
        have hhne : isSpecialScheme sc = true ∨ (un.isEmpty && pw.isEmpty) = false ∨ po ≠ none →
            (hostSerializer hst).toList ≠ [] := by
          intro hcond he
          have hE := hempty he
          rcases hcond with h | h | h
          · exact hnotempty h hE
          · rw [hE] at c14
            simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at c14
            rcases c14 with hx | hx
            · exact absurd trivial hx
            · simp only [Url.includesCredentials, Bool.or_eq_false_iff, Bool.not_eq_false'] at hx
              rw [hx.1, hx.2] at h
              simp at h
          · exact h (hv.emptyHostNoPort (by rw [hE]))
        have hcan' : hostParser asciiDomainToASCII (hostSerializer hst).toList
            (!isSpecialScheme sc) = some hst := by
          rcases hcan with h | h
          · subst h
            cases hsx : isSpecialScheme sc with
            | false => exact hostParser_nil_opaque
            | true => exact absurd rfl (hnotempty hsx)
          · simpa [Url.isSpecial] using h
        refine roundtrip_host hs ha hr hlow rfl hfile (encodedWith_mem c3) (encodedWith_mem c4)
          hcan' hok' hnc ?hhead hhne ?hport ?hqc ?hfc ?hsegs ?hall
        case hhead =>
          intro hsv c hc
          rw [hsv] at hok'
          cases hx : (hostSerializer hst).toList with
          | nil => exact absurd hx (hhne (Or.inl hsv))
          | cons d t =>
            rw [hx] at hc
            simp only [List.cons_append, List.head?_cons, Option.mem_def,
              Option.some.injEq] at hc
            have h2 := (hostReadable_auth hok' d (by rw [hx]; simp)).2
            subst hc
            constructor <;> (intro he; rw [he] at h2; revert h2; decide)
        case hport =>
          intro p hp
          refine ⟨by have := hv.portRange p hp; omega, ?_⟩
          simp only at c2
          rw [hp] at c2
          simp only [bne_iff_ne, ne_eq] at c2
          simp only [portOf, beq_iff_eq]
          rw [if_neg c2]
        case hqc =>
          intro x hx c hcm
          simp only at c5
          rw [hx] at c5
          exact encodedWith_mem c5 c hcm
        case hfc =>
          intro x hx c hcm
          simp only at c6
          rw [hx] at c6
          exact encodedWith_mem c6 c hcm
        case hsegs =>
          intro hsv
          cases segs with
          | nil =>
            simp only [Url.isSpecial, hsv, Bool.not_true, Bool.false_or] at c9
            exact absurd c9 (by simp)
          | cons x t => simp
        case hall =>
          intro x hx
          obtain ⟨h1, h2, h3, h4, h5⟩ := hseg x hx
          exact ⟨fun c hc => ⟨h1 c hc, isTerminator_false (h4 c hc)
            (ne_qh_of_pathSet (h1 c hc)).1 (ne_qh_of_pathSet (h1 c hc)).2
            (fun hsv => h5 hsv c hc)⟩, h2, h3⟩

/-- 二つの述語だけで往復が出る。`sc://h/a` はどちらも満たす。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] }) none
    = some { scheme := "sc", host := some (.opaque "h"), path := .list ["a"] } :=
  roundtrip_canonical ((checkValidUrl_iff _).mp (by decide)) (by decide)

/-- `file:` も同じである。 -/
example : basicUrlParse (urlSerializer
      { scheme := "file", host := some .empty, path := .list ["a"] }) none
    = some { scheme := "file", host := some .empty, path := .list ["a"] } :=
  roundtrip_canonical ((checkValidUrl_iff _).mp (by decide)) (by decide)

/-- query と fragment が付いていても同じである。 -/
example : basicUrlParse (urlSerializer
      { scheme := "sc", path := .opaque "x", query := some "q", fragment := some "f" }) none
    = some { scheme := "sc", path := .opaque "x", query := some "q", fragment := some "f" } :=
  roundtrip_canonical ((checkValidUrl_iff _).mp (by decide)) (by decide)

end Url
