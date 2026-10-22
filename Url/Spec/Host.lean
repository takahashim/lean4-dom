import Url.Spec.Ipv4
import Url.Spec.Ipv6
import Url.Spec.Percent
import Infra.Spec.Utf8DecodeDeterministic

/-!
# host parser の関係仕様（§3.2 host parser）

host parser は四つの道に分かれる。

| 入力 | 結果 | 本文 |
| --- | --- | --- |
| `[` で始まる | `]` で終わればその中を IPv6 parser で読む | step 1 |
| opaque（special でない URL） | forbidden host code point が無ければ、C0 control percent-encode set で encode | step 2、opaque-host parser |
| それ以外で ends in a number | IPv4 parser で読む | step 4-6 |
| それ以外 | domain | step 4-7 |

domain の道は「percent-decode して、UTF-8 decode without BOM して、domain to ASCII」で、
ここでは三つをそれぞれの関係で書く。percent-decode は §1.3 の `PctDecodes`（`Url/Spec/Percent.lean`）、
UTF-8 decode は Encoding Standard の `Decodes`（`Infra/Spec/Utf8Decode.lean`）、
ends in a number と IPv4 parser は §3.3 の `EndsInNumber` と `Ipv4Parses`（`Url/Spec/Ipv4.lean`）である。
IPv6 は §3.3 の `Ipv6Text`（`Url/Spec/Ipv6.lean`）で書く。domain to ASCII（UTS #46）は引数 `t` のまま残す。

`hostParser_iff` が、実装の `hostParser` はこの関係を計算すると言う。
-/

namespace Url.Spec

open Infra Url

/--
§3.2 host parser。`HostParses t isOpaque input h` は「`input` を読むと host `h`」。

domain の道で ToASCII が空文字列を返したときは、ends in a number の assert が成り立たないので
domain として扱う（実装と同じ。ToASCII が空を返さないことは `ToAsciiOk` が言う）。
-/
inductive HostParses (t : List Char → Option String) (isOpaque : Bool) : List Char → Host → Prop
  | ipv6 {inner : List Char} {a : Ipv6} : Ipv6Text inner a →
      HostParses t isOpaque ('[' :: (inner ++ [']'])) (.ipv6 a)
  | opaqueHost {input : List Char} : isOpaque = true → (∀ r, input ≠ '[' :: r) →
      (∀ c ∈ input, isForbiddenHost c = false) →
      HostParses t isOpaque input
        (if input = [] then .empty else .opaque (String.ofList (utf8PercentEncode c0ControlSet input)))
  | ipv4 {input : List Char} {bytes : Bytes} {domain : List Char} {ascii : String} {addr : Nat} :
      isOpaque = false → (∀ r, input ≠ '[' :: r) → input ≠ [] →
      PctDecodes (utf8Encode (String.ofList input)) bytes → Infra.Spec.Decodes bytes domain →
      t domain = some ascii → ascii.toList ≠ [] → EndsInNumber ascii.toList →
      Ipv4Parses ascii.toList addr →
      HostParses t isOpaque input (.ipv4 addr)
  | domain {input : List Char} {bytes : Bytes} {domain : List Char} {ascii : String} :
      isOpaque = false → (∀ r, input ≠ '[' :: r) → input ≠ [] →
      PctDecodes (utf8Encode (String.ofList input)) bytes → Infra.Spec.Decodes bytes domain →
      t domain = some ascii → ¬ (ascii.toList ≠ [] ∧ EndsInNumber ascii.toList) →
      HostParses t isOpaque input (.domain ascii)

/-- 実装の percent-decode と UTF-8 decode は二つの関係の合成である。 -/
theorem percentDecodeToString_iff (input domain : List Char) :
    percentDecodeToString input = domain ↔
      ∃ bytes, PctDecodes (utf8Encode (String.ofList input)) bytes ∧ Infra.Spec.Decodes bytes domain := by
  unfold percentDecodeToString stringPercentDecode
  constructor
  · intro h
    exact ⟨_, percentDecodeBytes_spec _, Infra.Spec.Decodes.eq_utf8Decode_iff.mpr h.symm⟩
  · rintro ⟨bytes, hp, hd⟩
    rw [percentDecodeBytes_iff.mp hp]
    exact (Infra.Spec.Decodes.eq_utf8Decode_iff.mp hd).symm

/-- `endsInANumber` は、空でなければ `EndsInNumber`、空なら false である。 -/
theorem endsInANumber_eq (l : List Char) :
    endsInANumber l = true ↔ (l ≠ [] ∧ EndsInNumber l) := by
  by_cases hne : l = []
  · subst hne; simp [endsInANumber, ipv4Parts, strictSplit, strictSplit.go, ipv4NumberParser]
  · rw [endsInANumber_iff hne]; simp [hne]

/-- **host parser は関係 `HostParses` を計算する。** 入力に制限は無い。 -/
theorem hostParser_iff (t : List Char → Option String) (isOpaque : Bool) (input : List Char)
    (h : Host) : hostParser t input isOpaque = some h ↔ HostParses t isOpaque input h := by
  constructor
  · intro hp
    unfold hostParser at hp
    split at hp
    · next rest =>
      split at hp
      · next revInner hrev =>
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hp
        have : rest = revInner.reverse ++ [']'] := by
          have := congrArg List.reverse hrev; simpa using this
        subst this
        exact .ipv6 ((ipv6Parser_iff _ _).mp ha)
      · simp at hp
    · next hnb =>
      have hnb' : ∀ r, input ≠ '[' :: r := fun r he => hnb r he
      cases hop : isOpaque
      · rw [hop] at hp
        simp only [Bool.false_eq_true, if_false] at hp
        split at hp
        · simp at hp
        · next hne =>
          have hne' : input ≠ [] := by simpa using hne
          obtain ⟨bytes, hpd, hdec⟩ := (percentDecodeToString_iff input _).mp rfl
          split at hp
          · simp at hp
          · next ascii hascii =>
            split at hp
            · next hend =>
              obtain ⟨addr, haddr, rfl⟩ := Option.map_eq_some_iff.mp hp
              obtain ⟨hl, he⟩ := (endsInANumber_eq _).mp hend
              exact .ipv4 rfl hnb' hne' hpd hdec hascii hl he ((ipv4Parser_iff _ _).mp haddr)
            · next hend =>
              simp only [Option.some.injEq] at hp
              subst hp
              exact .domain rfl hnb' hne' hpd hdec hascii (fun h' => hend ((endsInANumber_eq _).mpr h'))
      · rw [hop] at hp
        simp only [if_true] at hp
        unfold opaqueHostParser at hp
        split at hp
        · simp at hp
        · next hf =>
          simp only [Option.some.injEq] at hp
          subst hp
          have he : (if input.isEmpty = true then Host.empty
              else Host.opaque (String.ofList (utf8PercentEncode c0ControlSet input)))
              = (if input = [] then Host.empty
                else Host.opaque (String.ofList (utf8PercentEncode c0ControlSet input))) := by
            cases input <;> rfl
          rw [he]
          refine .opaqueHost rfl hnb' (fun c hc => ?_)
          simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hf
          exact hf c hc
  · intro hh
    cases hh with
    | @ipv6 inner a ha =>
      unfold hostParser
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.reverse_reverse, (ipv6Parser_iff _ _).mpr ha, Option.map_some]
    | @opaqueHost _ hop hnb hf =>
      subst hop
      unfold hostParser
      split
      · next r => exact absurd rfl (hnb r)
      · simp only [if_true]
        rw [opaqueHostParser_of_no_forbidden (by simpa using hf)]
        cases input <;> rfl
    | @ipv4 _ bytes domain ascii addr hop hnb hne hpd hdec hascii hl he haddr =>
      subst hop
      have hdom : percentDecodeToString input = domain :=
        (percentDecodeToString_iff input domain).mpr ⟨bytes, hpd, hdec⟩
      unfold hostParser
      split
      · next r => exact absurd rfl (hnb r)
      · simp only [Bool.false_eq_true, if_false]
        rw [if_neg (by simpa using hne), hdom, hascii]
        simp only
        rw [if_pos ((endsInANumber_eq _).mpr ⟨hl, he⟩), (ipv4Parser_iff _ _).mpr haddr]
        rfl
    | @domain _ bytes domain ascii hop hnb hne hpd hdec hascii he =>
      subst hop
      have hdom : percentDecodeToString input = domain :=
        (percentDecodeToString_iff input domain).mpr ⟨bytes, hpd, hdec⟩
      unfold hostParser
      split
      · next r => exact absurd rfl (hnb r)
      · simp only [Bool.false_eq_true, if_false]
        rw [if_neg (by simpa using hne), hdom, hascii]
        simp only
        rw [if_neg (fun h' => he ((endsInANumber_eq _).mp h'))]

end Url.Spec
