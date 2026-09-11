import Infra.Ascii

/-!
# Infra Standard の byte sequence

URL Standard は percent-decoding で **任意の byte 列** を作り、
そこから UTF-8 として decode する（不正な並びは U+FFFD に置き換える）。
`String` では表せないので、byte 列は `List UInt8` として持つ。

UTF-16 の lone surrogate（`Dom/Basic/Utf16.lean` の話）と違って、
ここは `Char` の側に穴が空かない。
UTF-8 decode の出力は必ず Unicode scalar value の列になる
（不正な並びは replacement character になる）ので、`String` に収まる。
-/

namespace Infra

/-- Infra の byte sequence。 -/
abbrev Bytes := List UInt8

/-! ## UTF-8 encode -/

/-- 一つの scalar value を UTF-8 で符号化する。 -/
def utf8EncodeChar (c : Char) : Bytes :=
  let n := c.toNat
  if n < 0x80 then [UInt8.ofNat n]
  else if n < 0x800 then
    [UInt8.ofNat (0xC0 ||| (n >>> 6)), UInt8.ofNat (0x80 ||| (n &&& 0x3F))]
  else if n < 0x10000 then
    [UInt8.ofNat (0xE0 ||| (n >>> 12)), UInt8.ofNat (0x80 ||| ((n >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (n &&& 0x3F))]
  else
    [UInt8.ofNat (0xF0 ||| (n >>> 18)), UInt8.ofNat (0x80 ||| ((n >>> 12) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| ((n >>> 6) &&& 0x3F)), UInt8.ofNat (0x80 ||| (n &&& 0x3F))]

/-- 文字列を UTF-8 で符号化する。 -/
def utf8Encode (s : String) : Bytes := s.toList.flatMap utf8EncodeChar

/-! ## UTF-8 decode -/

/-- Infra の replacement character。 -/
def replacementChar : Char := ⟨0xFFFD, by decide⟩

/--
code point の値から `Char` を作る。surrogate と範囲外は replacement character にする。

Unicode scalar value でない値は `Char` で表せないので、ここで潰す。
UTF-8 decode の出力が必ず `String` に収まるのはこのためである。
-/
def charOfScalar (n : Nat) : Char :=
  if n < 0xD800 || (0xDFFF < n && n < 0x110000) then Char.ofNat n else replacementChar

/--
continuation byte（`10xxxxxx`）から下位 6 bit を取り出す。
continuation byte でなければ `none`。
-/
def continuationBits (b : UInt8) : Option Nat :=
  if b.toNat &&& 0xC0 == 0x80 then some (b.toNat &&& 0x3F) else none

/--
UTF-8 decode without BOM、不正な並びは replacement character に置き換える。

先頭 byte の形から続く byte 数を決め、足りない・形が違う・overlong・
surrogate・範囲外ならその 1 byte を replacement character にして次へ進む。
仕様（Encoding Standard）の decoder はもう少し細かく「どこまで巻き戻すか」を決めるが、
URL Standard が使うのは「不正なら U+FFFD」という結果だけである。
-/
def utf8Decode : Bytes → List Char
  | [] => []
  | b :: rest =>
    let n := b.toNat
    if n < 0x80 then charOfScalar n :: utf8Decode rest
    else if 0xC2 ≤ n && n ≤ 0xDF then
      match _hr : rest with
      | b1 :: rest' =>
        match continuationBits b1 with
        | some v1 => charOfScalar (((n &&& 0x1F) <<< 6) ||| v1) :: utf8Decode rest'
        | none => replacementChar :: utf8Decode rest
      | [] => [replacementChar]
    else if 0xE0 ≤ n && n ≤ 0xEF then
      match _hr : rest with
      | b1 :: b2 :: rest' =>
        match continuationBits b1, continuationBits b2 with
        | some v1, some v2 =>
          let cp := ((n &&& 0x0F) <<< 12) ||| (v1 <<< 6) ||| v2
          -- overlong と surrogate は `charOfScalar` が replacement にする。
          (if cp < 0x800 then replacementChar else charOfScalar cp) :: utf8Decode rest'
        | _, _ => replacementChar :: utf8Decode rest
      | _ => replacementChar :: utf8Decode rest
    else if 0xF0 ≤ n && n ≤ 0xF4 then
      match _hr : rest with
      | b1 :: b2 :: b3 :: rest' =>
        match continuationBits b1, continuationBits b2, continuationBits b3 with
        | some v1, some v2, some v3 =>
          let cp := ((n &&& 0x07) <<< 18) ||| (v1 <<< 12) ||| (v2 <<< 6) ||| v3
          (if cp < 0x10000 then replacementChar else charOfScalar cp) :: utf8Decode rest'
        | _, _, _ => replacementChar :: utf8Decode rest
      | _ => replacementChar :: utf8Decode rest
    else replacementChar :: utf8Decode rest
termination_by bs => bs.length
decreasing_by all_goals first | (subst_vars; simp_wf; omega) | (subst_vars; simp_wf) | simp_wf

/-- byte 列を UTF-8 として読んだ文字列。 -/
def utf8DecodeString (bs : Bytes) : String := String.ofList (utf8Decode bs)

end Infra
