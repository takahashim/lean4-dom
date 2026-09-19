import Url.Roundtrip.File

/-!
# host の条件
-/

namespace Url

open Infra

/-! ## host の条件

`canonicalUrl` の `hostParser (hostSerializer h) = some h` から、
host state が serialize した文字列を読み直せることと、
前処理が落とす文字を含まないことを出す。host の種類ごとに根拠が違う。
-/

/-- `%` も alphanumeric も含まない set なら、percent-encode の出力に set の文字は無い。 -/
theorem utf8PercentEncode_out {set : Char → Bool}
    (hp : set '%' = false) (ha : ∀ c, isAsciiAlphanumeric c = true → set c = false) :
    ∀ {input : List Char}, ∀ c ∈ utf8PercentEncode set input, set c = false := by
  intro input c hc
  unfold utf8PercentEncode at hc
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
  split at hc
  · obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp hc
    have h2 := percentEncodeByte_alnum b c hb
    simp only [Bool.or_eq_true, beq_iff_eq] at h2
    rcases h2 with rfl | h2
    · exact hp
    · exact ha c h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    rename_i hset
    simpa using hset

/-- IPv4 を serialize した文字は 10 進の数字か `.` である。 -/
theorem ipv4Serializer_chars (addr : Nat) :
    ∀ c ∈ (ipv4Serializer addr).toList, isAsciiDigit c = true ∨ c = '.' := by
  intro c hc
  rw [show ipv4Serializer addr
      = toString (addr / 16777216 % 256) ++ "." ++ toString (addr / 65536 % 256) ++ "."
        ++ toString (addr / 256 % 256) ++ "." ++ toString (addr % 256) from rfl] at hc
  simp only [String.toList_append] at hc
  have hdot : ∀ x ∈ ("." : String).toList, x = '.' := by decide
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · exact Or.inl (toString_digits _ c hc)
            · exact Or.inr (hdot c hc)
          · exact Or.inl (toString_digits _ c hc)
        · exact Or.inr (hdot c hc)
      · exact Or.inl (toString_digits _ c hc)
    · exact Or.inr (hdot c hc)
  · exact Or.inl (toString_digits _ c hc)

/-- 10 進の数字は forbidden host code point ではない。 -/
theorem not_forbidden_of_digit {c : Char} (h : isAsciiDigit c = true) :
    isForbiddenHost c = false := by
  simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isForbiddenHost, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  repeat' constructor
  all_goals first
    | omega
    | (intro he; rw [he] at h; revert h; decide)

/-- opaque host が返るなら、入力は opaque host parser を通っている。 -/
theorem hostParser_opaque_eq {f : List Char → Option String} {input : List Char} {o : String}
    {b : Bool} (h : hostParser f input b = some (.opaque o)) :
    opaqueHostParser input = some (.opaque o) := by
  unfold hostParser at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, -, hx⟩ := h
      exact absurd hx (by simp)
    · simp at h
  · split at h
    · exact h
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · simp at h
        · split at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨x, -, hx⟩ := h
            exact absurd hx (by simp)
          · simp at h

/-- domain が返るなら、その文字列は domain parser の出力である。 -/
theorem hostParser_domain_eq {f : List Char → Option String} {input : List Char} {d : String}
    {b : Bool} (h : hostParser f input b = some (.domain d)) :
    ∃ dom, f dom = some d := by
  unfold hostParser at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, -, hx⟩ := h
      exact absurd hx (by simp)
    · simp at h
  · split at h
    · rcases (opaqueHostParser_cases h).2 with ⟨-, hx⟩ | ⟨-, hx⟩ <;> simp at hx
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · simp at h
        · split at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨x, -, hx⟩ := h
            exact absurd hx (by simp)
          · rename_i dom hdom _
            simp only [Option.some.injEq, Host.domain.injEq] at h
            exact ⟨_, by rw [hdom, h]⟩

/-- C0 control でも space でもないことを、C0 control の側から言う。 -/
theorem ne_c0_of_isC0Control {c : Char} (h : isC0Control c = false) (hs : ¬c = ' ') :
    isC0ControlOrSpace c = false := by
  simp only [isC0Control, decide_eq_false_iff_not, Nat.not_le] at h
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
  have h20 : c.toNat ≠ 0x20 := by
    intro he
    exact hs (by rw [← Char.ofNat_toNat c, he])
  omega

/-- alphanumeric は C0 control percent-encode set に入らない。 -/
theorem c0Set_of_alnum {c : Char} (h : isAsciiAlphanumeric c = true) : c0ControlSet c = false := by
  simp only [isAsciiAlphanumeric, isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha, isAsciiDigit,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le,
    Nat.not_lt]
  omega

/--
**canonical な host は、serialize した文字列を host state が読み直せる。**

`canonicalUrl` の host の条件（`hostParser (hostSerializer h) = some h`）から、
`roundtrip_canonical` が仮定に置いていた二つを出す。
-/
theorem hostReadable_of_canonical {sp : Bool} {h : Host}
    (hc : h = Host.empty ∨
      hostParser asciiDomainToASCII (hostSerializer h).toList (!sp) = some h) :
    hostReadable sp h ∧ ∀ c ∈ (hostSerializer h).toList, isC0ControlOrSpace c = false := by
  cases h with
  | empty =>
    exact ⟨Or.inl (fun c hcm => by simp [hostSerializer] at hcm),
      fun c hcm => by simp [hostSerializer] at hcm⟩
  | ipv6 a => exact ⟨hostReadable_ipv6 sp a, ipv6_no_c0 a⟩
  | ipv4 a =>
    refine ⟨Or.inl (fun c hcm => ?_), fun c hcm => ?_⟩
    · rcases ipv4Serializer_chars a c hcm with hd | hd
      · exact not_forbidden_of_digit hd
      · rw [hd]; decide
    · rcases ipv4Serializer_chars a c hcm with hd | hd
      · simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
        simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
        omega
      · rw [hd]; decide
  | «opaque» o =>
    rcases hc with hx | hx
    · exact absurd hx (by simp)
    · have hp : opaqueHostParser o.toList = some (Host.opaque o) := hostParser_opaque_eq hx
      have hnf : ∀ c ∈ o.toList, isForbiddenHost c = false := by
        have h2 := opaqueHostParser_no_forbidden hp
        simp only [List.any_eq_false] at h2
        exact fun c hcm => by simpa using h2 c hcm
      have henc : o.toList = utf8PercentEncode c0ControlSet o.toList := by
        rcases (opaqueHostParser_cases hp).2 with ⟨-, hx⟩ | ⟨-, hx⟩
        · simp at hx
        · simp only [Host.opaque.injEq] at hx
          calc o.toList
              = (String.ofList (utf8PercentEncode c0ControlSet o.toList)).toList := by rw [← hx]
            _ = utf8PercentEncode c0ControlSet o.toList := String.toList_ofList
      refine ⟨Or.inl hnf, fun c hcm => ?_⟩
      have hcm' : c ∈ o.toList := hcm
      have hc0 : c0ControlSet c = false := by
        rw [henc] at hcm'
        exact utf8PercentEncode_out (by decide) (fun x hx => c0Set_of_alnum hx) c hcm'
      refine ne_c0_of_c0Set hc0 ?_
      intro he
      have h4 := hnf c hcm
      rw [he] at h4
      revert h4
      decide
  | domain d =>
    rcases hc with hx | hx
    · exact absurd hx (by simp)
    · obtain ⟨dom, hdom⟩ := hostParser_domain_eq hx
      have h2 := asciiDomainToASCII_no_forbidden hdom
      simp [String.any] at h2
      have hfd : ∀ c ∈ d.toList, isForbiddenDomain c = false := h2
      have hnf : ∀ c ∈ d.toList, isForbiddenHost c = false := by
        intro c hcm
        have := hfd c hcm
        simp only [isForbiddenDomain, Bool.or_eq_false_iff] at this
        exact this.1.1.1
      refine ⟨Or.inl hnf, fun c hcm => ?_⟩
      have h3 := hfd c hcm
      simp only [isForbiddenDomain, Bool.or_eq_false_iff] at h3
      refine ne_c0_of_isC0Control h3.1.1.2 ?_
      intro he
      have := hnf c hcm
      rw [he] at this
      revert this
      decide

end Url
