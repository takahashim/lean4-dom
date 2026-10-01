import Infra.Bytes

/-!
# UTF-8 decode の関係仕様

`Infra.utf8Decode` の **不正な byte 列に対する復元規則** を、関数を呼ばずに
入力の形だけで書く。Encoding Standard の "UTF-8 decoder" の state machine
（`bytes_needed` / `lower_boundary` / `upper_boundary`）に対応する。

仕様は二段に分ける。

* `Chunk bs c bs'` — 先頭の **maximal subpart** が 1 文字 `c` を作り、残りが `bs'`。
  復元規則はここにだけ現れる。
* `Decodes bs cs` — `Chunk` の連接。byte 列全体の復号。

`Infra/Spec/Utf8DecodeSound.lean` で、実行関数 `utf8Decode` が `Decodes` を満たすことを示す。
-/

namespace Infra.Spec

open Infra

/-- ASCII byte（`0xxxxxxx`）。 -/
def IsAscii (b : UInt8) : Prop := b.toNat < 0x80

/-- 2 byte 列の先頭 byte（C2..DF）。C0/C1 は overlong なので除く。 -/
def IsLead2 (b : UInt8) : Prop := 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF

/-- 3 byte 列の先頭 byte（E0..EF）。 -/
def IsLead3 (b : UInt8) : Prop := 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF

/-- 4 byte 列の先頭 byte（F0..F4）。F5 以上は範囲外なので除く。 -/
def IsLead4 (b : UInt8) : Prop := 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4

/-- continuation byte（80..BF）。 -/
def IsContinuation (b : UInt8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

/-- continuation byte が運ぶ 6 bit の値。`IsContinuation` のもとで 0..63 になる。 -/
def ContinuationValue (b : UInt8) : Nat := b.toNat - 0x80

/--
3 byte 列の最初の continuation byte の範囲。

E0 は overlong、ED は surrogate を避けるために boundary が狭い
（Encoding Standard の lower / upper boundary）。
-/
def FirstCont3 (n b1 : Nat) : Prop :=
  (if n == 0xE0 then 0xA0 else 0x80) ≤ b1 ∧ b1 ≤ (if n == 0xED then 0x9F else 0xBF)

/-- 4 byte 列の最初の continuation byte の範囲。F0 は overlong、F4 は範囲外を避ける。 -/
def FirstCont4 (n b1 : Nat) : Prop :=
  (if n == 0xF0 then 0x90 else 0x80) ≤ b1 ∧ b1 ≤ (if n == 0xF4 then 0x8F else 0xBF)

/--
一歩ぶんの復号。

`Chunk bs c bs'` は「`bs` の先頭の maximal subpart が `c` を出し、残りが `bs'`」を表す。
`c = replacementChar` の規則が、decoder がどこで error を出し、どの byte を読み直すか
（state machine の "prepend byte to ioQueue"）をそのまま述べている。

正しい列の規則は、出す文字を **code point の算術** で述べる。Encoding Standard の
`UTF-8 code point = (UTF-8 code point << 6) | (byte & 0x3F)` を、先頭 byte から
引く値と 64 の冪で書き直したものである。decoder の bit 演算とは独立に書いてあるので、
shift 量や mask の誤りは `utf8Decode_spec` の証明で捕まる。`c` が `Char` であること自体が、
その code point が Unicode scalar value であることを要求する。
-/
inductive Chunk : Bytes → Char → Bytes → Prop where
  /-- ASCII は 1 byte でその文字。 -/
  | ascii {b : UInt8} {c : Char} {rest : Bytes} (h : IsAscii b) (hc : c.toNat = b.toNat) :
      Chunk (b :: rest) c rest
  /-- 2 byte 列。 -/
  | lead2 {b b1 : UInt8} {c : Char} {rest : Bytes} (v1 : Nat) (h : IsLead2 b)
      (h1 : IsContinuation b1) (hv : ContinuationValue b1 = v1)
      (hc : c.toNat = (b.toNat - 0xC0) * 64 + v1) :
      Chunk (b :: b1 :: rest) c rest
  /-- 2 byte 列の 2 byte 目が continuation でない。先頭だけを U+FFFD にして読み直す。 -/
  | lead2_cont_none {b b1 : UInt8} {rest : Bytes} (h : IsLead2 b)
      (h1 : ¬ IsContinuation b1) :
      Chunk (b :: b1 :: rest) replacementChar (b1 :: rest)
  /-- 2 byte 列が途切れている。 -/
  | lead2_eof {b : UInt8} (h : IsLead2 b) :
      Chunk [b] replacementChar []
  /-- 3 byte 列。 -/
  | lead3 {b b1 b2 : UInt8} {c : Char} {rest : Bytes} (v2 : Nat) (h : IsLead3 b)
      (hb : FirstCont3 b.toNat b1.toNat) (h2 : IsContinuation b2)
      (hv : ContinuationValue b2 = v2)
      (hc : c.toNat = (b.toNat - 0xE0) * 4096 + (b1.toNat - 0x80) * 64 + v2) :
      Chunk (b :: b1 :: b2 :: rest) c rest
  /-- 3 byte 列の 1 byte 目が boundary の外（overlong / surrogate）。先頭だけを U+FFFD にする。 -/
  | lead3_b1_bad {b b1 b2 : UInt8} {rest : Bytes} (h : IsLead3 b)
      (hb : ¬ FirstCont3 b.toNat b1.toNat) :
      Chunk (b :: b1 :: b2 :: rest) replacementChar (b1 :: b2 :: rest)
  /-- 3 byte 列の 2 byte 目が continuation でない。そこまでを U+FFFD にして読み直す。 -/
  | lead3_b2_bad {b b1 b2 : UInt8} {rest : Bytes} (h : IsLead3 b)
      (hb : FirstCont3 b.toNat b1.toNat) (h2 : ¬ IsContinuation b2) :
      Chunk (b :: b1 :: b2 :: rest) replacementChar (b2 :: rest)
  /-- 3 byte 列が 1 byte で途切れている。 -/
  | lead3_eof {b : UInt8} (h : IsLead3 b) :
      Chunk [b] replacementChar []
  /-- 3 byte 列が 2 byte で途切れ、boundary の外。 -/
  | lead3_eof_b1_bad {b b1 : UInt8} (h : IsLead3 b)
      (hb : ¬ FirstCont3 b.toNat b1.toNat) :
      Chunk [b, b1] replacementChar [b1]
  /-- 3 byte 列が 2 byte で途切れ、boundary の中。 -/
  | lead3_eof_b1_ok {b b1 : UInt8} (h : IsLead3 b)
      (hb : FirstCont3 b.toNat b1.toNat) :
      Chunk [b, b1] replacementChar []
  /-- 4 byte 列。 -/
  | lead4 {b b1 b2 b3 : UInt8} {c : Char} {rest : Bytes} (v2 v3 : Nat) (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) (h2 : IsContinuation b2) (hv2 : ContinuationValue b2 = v2)
      (h3 : IsContinuation b3) (hv3 : ContinuationValue b3 = v3)
      (hc : c.toNat
        = (b.toNat - 0xF0) * 262144 + (b1.toNat - 0x80) * 4096 + v2 * 64 + v3) :
      Chunk (b :: b1 :: b2 :: b3 :: rest) c rest
  /-- 4 byte 列の 1 byte 目が boundary の外。先頭だけを U+FFFD にする。 -/
  | lead4_b1_bad {b b1 b2 b3 : UInt8} {rest : Bytes} (h : IsLead4 b)
      (hb : ¬ FirstCont4 b.toNat b1.toNat) :
      Chunk (b :: b1 :: b2 :: b3 :: rest) replacementChar (b1 :: b2 :: b3 :: rest)
  /-- 4 byte 列の 2 byte 目が continuation でない。そこまでを U+FFFD にして読み直す。 -/
  | lead4_b2_bad {b b1 b2 b3 : UInt8} {rest : Bytes} (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) (h2 : ¬ IsContinuation b2) :
      Chunk (b :: b1 :: b2 :: b3 :: rest) replacementChar (b2 :: b3 :: rest)
  /-- 4 byte 列の 3 byte 目が continuation でない。そこまでを U+FFFD にして読み直す。 -/
  | lead4_b3_bad {b b1 b2 b3 : UInt8} {rest : Bytes} (v2 : Nat) (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) (h2 : IsContinuation b2)
      (hv2 : ContinuationValue b2 = v2)
      (h3 : ¬ IsContinuation b3) :
      Chunk (b :: b1 :: b2 :: b3 :: rest) replacementChar (b3 :: rest)
  /-- 4 byte 列が 1 byte で途切れている。 -/
  | lead4_eof {b : UInt8} (h : IsLead4 b) :
      Chunk [b] replacementChar []
  /-- 4 byte 列が 2 byte で途切れ、boundary の外。 -/
  | lead4_eof_b1_bad {b b1 : UInt8} (h : IsLead4 b)
      (hb : ¬ FirstCont4 b.toNat b1.toNat) :
      Chunk [b, b1] replacementChar [b1]
  /-- 4 byte 列が 2 byte で途切れ、boundary の中。 -/
  | lead4_eof_b1_ok {b b1 : UInt8} (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) :
      Chunk [b, b1] replacementChar []
  /-- 4 byte 列が 3 byte で途切れ、boundary の外。 -/
  | lead4_eof_b1_bad2 {b b1 b2 : UInt8} (h : IsLead4 b)
      (hb : ¬ FirstCont4 b.toNat b1.toNat) :
      Chunk [b, b1, b2] replacementChar [b1, b2]
  /-- 4 byte 列が 3 byte で途切れ、2 byte 目が continuation でない。 -/
  | lead4_eof_b2_bad {b b1 b2 : UInt8} (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) (h2 : ¬ IsContinuation b2) :
      Chunk [b, b1, b2] replacementChar [b2]
  /-- 4 byte 列が 3 byte で途切れ、2 byte 目まで正しい。 -/
  | lead4_eof_b1_ok2 {b b1 b2 : UInt8} (v2 : Nat) (h : IsLead4 b)
      (hb : FirstCont4 b.toNat b1.toNat) (h2 : IsContinuation b2)
      (hv2 : ContinuationValue b2 = v2) :
      Chunk [b, b1, b2] replacementChar []
  /-- 先頭 byte がどの列の先頭でもない。1 byte を U+FFFD にして次へ。 -/
  | invalid {b : UInt8} (rest : Bytes)
      (h : ¬ (IsAscii b ∨ IsLead2 b ∨ IsLead3 b ∨ IsLead4 b)) :
      Chunk (b :: rest) replacementChar rest

/-- `Chunk` の連接。byte 列全体の復号。 -/
inductive Decodes : Bytes → List Char → Prop where
  | nil : Decodes [] []
  | cons {bs bs' : Bytes} {c : Char} {cs : List Char} :
      Chunk bs c bs' → Decodes bs' cs → Decodes bs (c :: cs)

end Infra.Spec
