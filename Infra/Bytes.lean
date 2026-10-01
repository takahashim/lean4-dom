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

/-- code point の値が Unicode scalar value の範囲にあるか。 -/
def isScalarValue (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n < 0x110000)

/-- `Char` の値は必ず scalar value の範囲にある。 -/
theorem isScalarValue_toNat (c : Char) : isScalarValue c.toNat = true := by
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  unfold isScalarValue
  rcases hv with h | h
  · simp [h]
  · simp [h.1, h.2]

/--
code point の値から `Char` を作る。surrogate と範囲外は replacement character にする。

Unicode scalar value でない値は `Char` で表せないので、ここで潰す。
UTF-8 decode の出力が必ず `String` に収まるのはこのためである。
-/
def charOfScalar (n : Nat) : Char :=
  if isScalarValue n then Char.ofNat n else replacementChar

/--
continuation byte（`10xxxxxx`）から下位 6 bit を取り出す。
continuation byte でなければ `none`。
-/
def continuationBits (b : UInt8) : Option Nat :=
  if b.toNat &&& 0xC0 == 0x80 then some (b.toNat &&& 0x3F) else none

/-- 選択済みの包含境界に byte 値が収まるかを判定する。 -/
def withinBoundary (lower upper value : Nat) : Bool :=
  decide (lower ≤ value) && decide (value ≤ upper)

/--
UTF-8 decode without BOM、不正な並びは replacement character に置き換える。

Encoding Standard の UTF-8 decoder と同じく、**maximal subpart** ごとに 1 個の
replacement character を出す。先頭 byte の形で続く byte 数を決め、E0 / ED / F0 / F4 では
最初の continuation byte の範囲（lower / upper boundary）も見る。範囲外ならその byte を
読み直しに回し、**先頭 byte ぶんだけ**を replacement character にする。途中の
continuation が欠けている・形が違うなら、そこまでを 1 個にしてその byte を読み直す。

boundary が overlong・surrogate・範囲外をすべて捉えるので、組み立てた code point は
必ず Unicode scalar value になる（`Infra.Spec.assemble3` / `assemble4`）。
-/
def utf8Decode : Bytes → List Char
  | [] => []
  | b :: rest =>
    let n := b.toNat
    if n < 0x80 then charOfScalar n :: utf8Decode rest
    else if 0xC2 ≤ n && n ≤ 0xDF then
      -- 2 byte: 2 byte 目を消費するか、置換文字の後に読み直す。
      match _hr : rest with
      | b1 :: rest' =>
        match continuationBits b1 with
        | some v1 => charOfScalar (((n &&& 0x1F) <<< 6) ||| v1) :: utf8Decode rest'
        | none => replacementChar :: utf8Decode rest
      | [] => [replacementChar]
    else if 0xE0 ≤ n && n ≤ 0xEF then
      -- 3 byte: 最後の byte を調べる前に境界を検証する。
      let lo := if n == 0xE0 then 0xA0 else 0x80
      let hi := if n == 0xED then 0x9F else 0xBF
      match _hr : rest with
      | b1 :: b2 :: rest' =>
        if withinBoundary lo hi b1.toNat = true then
          match continuationBits b2 with
          | some v2 =>
            charOfScalar (((n &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| v2)
              :: utf8Decode rest'
          | none => replacementChar :: utf8Decode (b2 :: rest')
        else replacementChar :: utf8Decode rest
      | b1 :: [] =>
        if withinBoundary lo hi b1.toNat = true then [replacementChar]
        else replacementChar :: utf8Decode rest
      | [] => [replacementChar]
    else if 0xF0 ≤ n && n ≤ 0xF4 then
      -- 4 byte: 不正・途中終了の各 prefix を maximal subpart に従って処理する。
      let lo := if n == 0xF0 then 0x90 else 0x80
      let hi := if n == 0xF4 then 0x8F else 0xBF
      match _hr : rest with
      | b1 :: b2 :: b3 :: rest' =>
        if withinBoundary lo hi b1.toNat = true then
          match continuationBits b2, continuationBits b3 with
          | some v2, some v3 =>
            charOfScalar (((n &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) ||| (v2 <<< 6)
              ||| v3) :: utf8Decode rest'
          | some _, none => replacementChar :: utf8Decode (b3 :: rest')
          | none, _ => replacementChar :: utf8Decode (b2 :: b3 :: rest')
        else replacementChar :: utf8Decode rest
      | b1 :: b2 :: [] =>
        if withinBoundary lo hi b1.toNat = true then
          match continuationBits b2 with
          | some _ => [replacementChar]
          | none => replacementChar :: utf8Decode [b2]
        else replacementChar :: utf8Decode rest
      | b1 :: [] =>
        if withinBoundary lo hi b1.toNat = true then [replacementChar]
        else replacementChar :: utf8Decode rest
      | [] => [replacementChar]
    else replacementChar :: utf8Decode rest
termination_by bs => bs.length
decreasing_by all_goals first | (subst_vars; simp_wf; omega) | (subst_vars; simp_wf) | simp_wf

/-- byte 列を UTF-8 として読んだ文字列。 -/
def utf8DecodeString (bs : Bytes) : String := String.ofList (utf8Decode bs)

end Infra
