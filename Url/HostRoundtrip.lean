import Url.Ipv4Roundtrip
import Url.Ipv6Roundtrip
import Url.UrlencodedRoundtrip

/-!
# host の往復

§3.5 host serializer で書いたものを §3.2 host parser で読むと元に戻ること。
`canonicalUrl`（`Url/Roundtrip.lean`）の host の条件がこれである。

host の種類ごとに段取りが違う。

* **IPv4**（`hostParser_ipv4`）。`Url/Ipv4Roundtrip.lean` の数の往復の上に、
  percent-decode と domain parser の層を乗せる。どちらも 10 進の数字と `.` に対しては
  何もしない。
* **opaque host**（`hostParser_opaque_id`）。parser の出力は percent-encode 済みなので、
  もう一度 encode しても変わらない（`utf8PercentEncode_id`）。
* **domain**（`hostParser_domain_id`）。すでに小文字の ASCII で forbidden domain code point が
  無いので、domain parser を素通りする。「数字で終わらない」ことは仮定に置く
  （終わるなら parser は IPv4 として読むので、その record は domain にならない）。

* **IPv6**（`hostParser_ipv6`）。`[` と `]` を外して `Url/Ipv6Roundtrip.lean` の
  `ipv6Parser_serializer` に渡す。
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-- `%` の無い ASCII の列は、percent-decode で変わらない。 -/
theorem percentDecodeBytes_ascii_id : ∀ (l : List Char),
    (∀ c ∈ l, c.toNat < 0x80 ∧ ¬c = '%') →
    percentDecodeBytes (asciiBytes l) = asciiBytes l
  | [], _ => rfl
  | c :: rest, h => by
    have hc := h c List.mem_cons_self
    have hne : ¬((UInt8.ofNat c.toNat).toNat == 0x25) = true := by
      simp only [beq_iff_eq]
      intro he
      rw [show (UInt8.ofNat c.toNat).toNat = c.toNat from by
        simp [Nat.mod_eq_of_lt (show c.toNat < 256 by have := hc.1; omega)]] at he
      exact hc.2 (by rw [← Char.ofNat_toNat c, he])
    show percentDecodeBytes (UInt8.ofNat c.toNat :: asciiBytes rest) = _
    rw [percentDecodeBytes_cons_ne hne]
    rw [percentDecodeBytes_ascii_id rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- `%` の無い ASCII の列は、percent-decode して UTF-8 で読み直しても変わらない。 -/
theorem percentDecodeToString_ascii {l : List Char}
    (h : ∀ c ∈ l, c.toNat < 0x80 ∧ ¬c = '%') : percentDecodeToString l = l := by
  unfold percentDecodeToString stringPercentDecode
  rw [utf8Encode_ofList_ascii l (fun c hc => (h c hc).1)]
  rw [percentDecodeBytes_ascii_id l h]
  rw [← utf8Encode_ofList_ascii l (fun c hc => (h c hc).1)]
  rw [utf8Decode_encode, String.toList_ofList]

/-- 小文字に直しても変わらない文字だけの列は、`asciiLowercase` で変わらない。 -/
theorem asciiLowercase_id {l : List Char} (h : ∀ c ∈ l, asciiLowerChar c = c) :
    asciiLowercase (String.ofList l) = String.ofList l := by
  unfold asciiLowercase
  rw [String.toList_ofList, map_self_of_mem h]

/-- すでに domain の形をしている列は、domain parser を素通りする。 -/
theorem asciiDomainToASCII_id {l : List Char} (hne : ¬l = [])
    (h : ∀ c ∈ l, isAscii c = true ∧ asciiLowerChar c = c ∧ isForbiddenDomain c = false) :
    asciiDomainToASCII l = some (String.ofList l) := by
  have hemp : (String.ofList l).isEmpty = false := by
    cases hx : (String.ofList l).isEmpty with
    | false => rfl
    | true =>
      exfalso
      rw [String.isEmpty_iff] at hx
      have h2 := congrArg String.toList hx
      rw [String.toList_ofList] at h2
      exact hne (by simpa using h2)
  have hfor : (String.ofList l).any isForbiddenDomain = false := by
    simp [String.any]
    exact fun c hc => (h c hc).2.2
  unfold asciiDomainToASCII
  rw [if_pos (by simp only [List.all_eq_true]; exact fun c hc => (h c hc).1)]
  rw [asciiLowercase_id (fun c hc => (h c hc).2.1)]
  unfold asciiDomainToASCII.asciiDomainCheck
  simp only [hemp, hfor, Bool.false_eq_true, if_false]

/-- IPv4 を serialize した文字が満たすことをまとめておく。 -/
theorem ipv4Serializer_char_facts {addr : Nat} {c : Char}
    (hc : c ∈ (ipv4Serializer addr).toList) :
    c.toNat < 0x80 ∧ ¬c = '%' ∧ isAscii c = true ∧ asciiLowerChar c = c ∧
      isForbiddenDomain c = false ∧ ¬c = '[' := by
  rcases ipv4Serializer_chars addr c hc with hd | hd
  · have ha : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 := by
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      exact hd
    refine ⟨by omega, ?_, by simp only [isAscii, decide_eq_true_eq]; omega, ?_, ?_, ?_⟩
    · intro he; rw [he] at ha; revert ha; decide
    · unfold asciiLowerChar
      rw [if_neg (by
        simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le]
        omega)]
    · simp only [isForbiddenDomain, Bool.or_eq_false_iff]
      refine ⟨⟨⟨not_forbidden_of_digit hd, ?_⟩, ?_⟩, ?_⟩
      · simp only [isC0Control, decide_eq_false_iff_not, Nat.not_le]; omega
      · simp only [beq_eq_false_iff_ne, ne_eq]
        intro he; rw [he] at ha; revert ha; decide
      · simp only [beq_eq_false_iff_ne, ne_eq]; omega
    · intro he; rw [he] at ha; revert ha; decide
  · subst hd
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- IPv4 を serialize した文字列は空でない。 -/
theorem ipv4Serializer_ne_nil (addr : Nat) : ¬(ipv4Serializer addr).toList = [] := by
  intro hx
  have h2 := ipv4Parts_serializer addr
  rw [hx] at h2
  simp [ipv4Parts, strictSplit, strictSplit.go] at h2

/-- IPv4 を serialize した文字列は「数字で終わる」。 -/
theorem endsInANumber_serializer (addr : Nat) :
    endsInANumber (ipv4Serializer addr).toList = true := by
  unfold endsInANumber
  rw [ipv4Parts_serializer addr]
  simp only [List.getLast?_cons_cons, List.getLast?_singleton]
  rw [if_pos ?hp]
  case hp =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨?_, fun c hc => toString_digits _ c hc⟩
    cases hx : (toString (addr % 256)).toList with
    | nil => exact absurd hx (toString_ne_nil _)
    | cons a b => rfl

/-- **IPv4 host は serialize して host parser に通すと元に戻る。** -/
theorem hostParser_ipv4 {addr : Nat} (h : addr < 4294967296) :
    hostParser asciiDomainToASCII (hostSerializer (Host.ipv4 addr)).toList false
      = some (Host.ipv4 addr) := by
  have hfacts : ∀ c ∈ (ipv4Serializer addr).toList,
      c.toNat < 0x80 ∧ ¬c = '%' ∧ isAscii c = true ∧ asciiLowerChar c = c ∧
        isForbiddenDomain c = false ∧ ¬c = '[' :=
    fun c hc => ipv4Serializer_char_facts hc
  have hne := ipv4Serializer_ne_nil addr
  have hemp : (ipv4Serializer addr).toList.isEmpty = false := by
    cases hx : (ipv4Serializer addr).toList with
    | nil => exact absurd hx hne
    | cons a b => rfl
  show hostParser asciiDomainToASCII (ipv4Serializer addr).toList false = _
  unfold hostParser
  split
  · next rest heq =>
    exfalso
    exact (hfacts '[' (by rw [heq]; simp)).2.2.2.2.2 rfl
  · simp only [Bool.false_eq_true, if_false, hemp]
    rw [percentDecodeToString_ascii (fun c hc => ⟨(hfacts c hc).1, (hfacts c hc).2.1⟩)]
    rw [asciiDomainToASCII_id hne
      (fun c hc => ⟨(hfacts c hc).2.2.1, (hfacts c hc).2.2.2.1, (hfacts c hc).2.2.2.2.1⟩)]
    simp only [String.toList_ofList, endsInANumber_serializer, if_true]
    rw [ipv4Parser_serializer h]
    rfl

/-- **percent-encode 済みの opaque host は、host parser を通すと元に戻る。** -/
theorem hostParser_opaque_id {f : List Char → Option String} {o : String}
    (hne : ¬o.toList = [])
    (hf : ∀ c ∈ o.toList, isForbiddenHost c = false)
    (hc0 : ∀ c ∈ o.toList, c0ControlSet c = false) :
    hostParser f o.toList true = some (Host.opaque o) := by
  have hemp : o.toList.isEmpty = false := by
    cases hx : o.toList with
    | nil => exact absurd hx hne
    | cons a b => rfl
  unfold hostParser
  split
  · next rest heq =>
    exfalso
    have h2 := hf '[' (by rw [heq]; simp)
    revert h2
    decide
  · rw [if_pos rfl]
    unfold opaqueHostParser
    have hany : o.toList.any isForbiddenHost = false := by
      simp only [List.any_eq_false]
      exact fun c hc => by simpa using hf c hc
    simp only [hany, hemp, Bool.false_eq_true, if_false]
    rw [utf8PercentEncode_id hc0, String.ofList_toList]

/-- **canonical な domain は、host parser を通すと元に戻る。** -/
theorem hostParser_domain_id {d : String} (hne : ¬d.toList = [])
    (h : ∀ c ∈ d.toList, isAscii c = true ∧ asciiLowerChar c = c ∧ isForbiddenDomain c = false)
    (hend : endsInANumber d.toList = false) :
    hostParser asciiDomainToASCII d.toList false = some (Host.domain d) := by
  have hemp : d.toList.isEmpty = false := by
    cases hx : d.toList with
    | nil => exact absurd hx hne
    | cons a b => rfl
  have hfh : ∀ c ∈ d.toList, isForbiddenHost c = false := by
    intro c hc
    have h2 := (h c hc).2.2
    simp only [isForbiddenDomain, Bool.or_eq_false_iff] at h2
    exact h2.1.1.1
  have hpct : ∀ c ∈ d.toList, c.toNat < 0x80 ∧ ¬c = '%' := by
    intro c hc
    have h2 := (h c hc).2.2
    simp only [isForbiddenDomain, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h2
    have ha := (h c hc).1
    simp only [isAscii, decide_eq_true_eq] at ha
    exact ⟨by omega, h2.1.2⟩
  unfold hostParser
  split
  · next rest heq =>
    exfalso
    have h2 := hfh '[' (by rw [heq]; simp)
    revert h2
    decide
  · simp only [Bool.false_eq_true, if_false, hemp]
    rw [percentDecodeToString_ascii hpct]
    rw [asciiDomainToASCII_id hne (fun c hc => ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2⟩)]
    simp only [String.toList_ofList, hend, Bool.false_eq_true, if_false]
    rw [String.ofList_toList]

/-- `1.2.3.4` は実際にこの形である。 -/
example : hostParser asciiDomainToASCII (hostSerializer (Host.ipv4 16909060)).toList false
    = some (Host.ipv4 16909060) :=
  hostParser_ipv4 (by omega)

/-- opaque host の例。`h` は percent-encode しても変わらない。 -/
example : hostParser asciiDomainToASCII (hostSerializer (Host.opaque "h")).toList true
    = some (Host.opaque "h") :=
  hostParser_opaque_id (by decide) (by decide) (by decide)

/-- **IPv6 host も、serialize して host parser に通すと元に戻る。** -/
theorem hostParser_ipv6 {f : List Char → Option String} {a : Ipv6} {b : Bool}
    (h8 : a.length = 8) (hp : ∀ p ∈ a, p < 65536) :
    hostParser f (hostSerializer (Host.ipv6 a)).toList b = some (Host.ipv6 a) := by
  have hser : (hostSerializer (Host.ipv6 a)).toList
      = '[' :: ((ipv6Serializer a).toList ++ [']']) := by
    simp only [hostSerializer, String.toList_append]
    rw [show ("[" : String).toList = ['['] from rfl, show ("]" : String).toList = [']'] from rfl]
    simp
  rw [hser, hostParser]
  rw [show ((ipv6Serializer a).toList ++ [']']).reverse
      = ']' :: (ipv6Serializer a).toList.reverse from by simp]
  simp only [List.reverse_reverse]
  rw [ipv6Parser_serializer h8 hp]
  rfl

/-- `[::1]` も戻る。 -/
example : hostParser asciiDomainToASCII
      (hostSerializer (Host.ipv6 [0, 0, 0, 0, 0, 0, 0, 1])).toList false
    = some (Host.ipv6 [0, 0, 0, 0, 0, 0, 0, 1]) :=
  hostParser_ipv6 (by decide) (by decide)

end Url
