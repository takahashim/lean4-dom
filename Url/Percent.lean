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
