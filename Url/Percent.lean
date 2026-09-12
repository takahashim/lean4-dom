import Infra.Bytes

/-!
# percent-encoding

WHATWG URL Standard §1.3 の percent-encode / percent-decode と、
§1.3 の percent-encode set。

percent-decoding は **byte 列** を作る。
そこから UTF-8 decode するので、`Infra/Bytes.lean` の層の上に置く。
-/

namespace Url

open Infra

/-! ## percent-encode set -/

/-- URL Standard §1.3 C0 control percent-encode set。C0 control と U+007E より大きい全部。 -/
def c0ControlSet (c : Char) : Bool := isC0Control c || c.toNat > 0x7E

/-- URL Standard §1.3 fragment percent-encode set。 -/
def fragmentSet (c : Char) : Bool :=
  c0ControlSet c || c == ' ' || c == '"' || c == '<' || c == '>' || c == '`'

/-- URL Standard §1.3 query percent-encode set。`` ` `` を含まないので fragment とは別に書く。 -/
def querySet (c : Char) : Bool :=
  c0ControlSet c || c == ' ' || c == '"' || c == '#' || c == '<' || c == '>'

/-- URL Standard §1.3 special-query percent-encode set。 -/
def specialQuerySet (c : Char) : Bool := querySet c || c == '\''

/-- URL Standard §1.3 path percent-encode set。 -/
def pathSet (c : Char) : Bool :=
  querySet c || c == '?' || c == '^' || c == '`' || c == '{' || c == '}'

/-- URL Standard §1.3 userinfo percent-encode set。 -/
def userinfoSet (c : Char) : Bool :=
  pathSet c || c == '/' || c == ':' || c == ';' || c == '=' || c == '@' ||
    (0x5B ≤ c.toNat && c.toNat ≤ 0x5D) || c == '|'

/-- URL Standard §1.3 component percent-encode set。 -/
def componentSet (c : Char) : Bool :=
  userinfoSet c || (0x24 ≤ c.toNat && c.toNat ≤ 0x26) || c == '+' || c == ','

/-! ## encode -/

/-- byte を `%XX`（大文字 16 進）に直す。 -/
def percentEncodeByte (b : UInt8) : List Char :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  let d := fun (n : Nat) => Char.ofNat (if n < 10 then 0x30 + n else 0x41 + n - 10)
  ['%', d hi, d lo]

/--
URL Standard §1.3 "UTF-8 percent-encode"。

set に入る code point を UTF-8 にしてから byte ごとに `%XX` にする。
入らないものはそのまま置く。
-/
def utf8PercentEncode (set : Char → Bool) (input : List Char) : List Char :=
  input.flatMap fun c =>
    if set c then (utf8EncodeChar c).flatMap percentEncodeByte else [c]

/-! ## decode -/

/--
URL Standard §1.3 "percent-decode"（byte 列に対する版）。

`%` の後ろ 2 つが hex digit でなければ、その `%` はそのまま残す。
-/
def percentDecodeBytes : Bytes → Bytes
  | [] => []
  | b :: b1 :: b2 :: rest =>
    if b.toNat == 0x25 then
      match hexValue (Char.ofNat b1.toNat), hexValue (Char.ofNat b2.toNat) with
      | some h1, some h2 => UInt8.ofNat (h1 * 16 + h2) :: percentDecodeBytes rest
      | _, _ => b :: percentDecodeBytes (b1 :: b2 :: rest)
    else b :: percentDecodeBytes (b1 :: b2 :: rest)
  -- 残りが 2 byte 未満なら `%` は decode できない。
  | b :: rest => b :: percentDecodeBytes rest

/-- URL Standard §1.3 "string percent-decode"。UTF-8 にしてから decode する。 -/
def stringPercentDecode (input : List Char) : Bytes :=
  percentDecodeBytes (utf8Encode (String.ofList input))

/-- percent-decode してから UTF-8 として読む。host parser と query が使う形。 -/
def percentDecodeToString (input : List Char) : List Char :=
  utf8Decode (stringPercentDecode input)

/-! ## 性質 -/

/-- 16 進の数字として使う文字は ASCII alphanumeric である。 -/
theorem hexDigitChar_alnum : ∀ n : Nat, n < 16 →
    isAsciiAlphanumeric (Char.ofNat (if n < 10 then 0x30 + n else 0x41 + n - 10)) = true
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

/-- `%XX` は `%` と 16 進の数字からなる。 -/
theorem percentEncodeByte_alnum (b : UInt8) :
    ∀ c ∈ percentEncodeByte b, c == '%' || isAsciiAlphanumeric c := by
  have hb : b.toNat < 256 := by simpa [UInt8.size] using b.toNat_lt_size
  intro c hc
  unfold percentEncodeByte at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · simp
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inr (hexDigitChar_alnum _ (by omega)))
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inr (hexDigitChar_alnum _ (Nat.mod_lt _ (by omega))))

/--
percent-encode は `%` と 16 進の数字しか足さない。

したがって、`%` でも alphanumeric でもない文字 `d` は、元々あったぶんしか出てこない。
parser が「区切り文字は encode の結果に現れない」と言うときの根拠である。
-/
theorem utf8PercentEncode_avoid {set : Char → Bool} {d : Char}
    (h1 : isAsciiAlphanumeric d = false) (h2 : d ≠ '%') :
    ∀ {input : List Char}, (∀ c ∈ input, c ≠ d) → ∀ c ∈ utf8PercentEncode set input, c ≠ d := by
  intro input h c hc
  unfold utf8PercentEncode at hc
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
  split at hc
  · obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp hc
    have ha := percentEncodeByte_alnum b c hb
    intro heq
    rw [heq] at ha
    simp only [h1, beq_iff_eq, Bool.or_eq_true, Bool.false_eq_true, or_false] at ha
    exact h2 ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact h _ hx

/-- `%XX` に直した 3 文字は必ず `%` で始まる。 -/
theorem percentEncodeByte_head (b : UInt8) : (percentEncodeByte b).head? = some '%' := rfl

/--
set に入らない code point しか無いなら、percent-encode は何もしない。

percent-encode が「必要なものだけ」を変えることの形式的な言い方である。
-/
theorem utf8PercentEncode_id {set : Char → Bool} :
    ∀ {input : List Char}, (∀ c ∈ input, set c = false) → utf8PercentEncode set input = input
  | [], _ => rfl
  | c :: rest, h => by
    show (if set c then _ else [c]) ++ _ = c :: rest
    rw [if_neg (by rw [h c List.mem_cons_self]; simp)]
    have := utf8PercentEncode_id (input := rest) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    show c :: utf8PercentEncode set rest = c :: rest
    rw [this]

end Url
