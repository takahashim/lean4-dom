import Url.Urlencoded

/-!
# `application/x-www-form-urlencoded` の往復

URL Standard §5。serialize したものを parse すると元に戻る。

## 二段に分かれる

* **成分の往復**（この file）。`urlencodedEncode` した文字列を
  `plusToSpace` → percent-decode → UTF-8 decode で読み戻すと元に戻る。
* **分割の逆**（未着手）。`&` と最初の `=` での分割が intercalate の逆になること。
  `urlencodedEncode_no_separator`（serialize した成分に `&` も `=` も現れない）が
  その足場である。

## 鍵になる並び

parser は `+` を空白に直して**から** percent-decode する。リテラルの `+` は
`urlencodedSet` に入るので `%2B` になり、`plusToSpace` を先に通しても壊れない。
この順序がないと `%2B` が空白になってしまう。
-/

namespace Url

open Infra

/-! ## ASCII の byte 列 -/

/-- ASCII だけの文字の列は、そのまま byte の列になる。 -/
def asciiBytes (l : List Char) : Bytes := l.map (fun c => UInt8.ofNat c.toNat)

theorem utf8EncodeChar_ascii {c : Char} (h : c.toNat < 0x80) :
    utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  simp [utf8EncodeChar, h]

theorem utf8Encode_ofList_ascii : ∀ (l : List Char), (∀ c ∈ l, c.toNat < 0x80) →
    utf8Encode (String.ofList l) = asciiBytes l
  | [], _ => rfl
  | c :: rest, h => by
    have hc := h c List.mem_cons_self
    have ih := utf8Encode_ofList_ascii rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold utf8Encode at *
    simp only [String.toList_ofList] at *
    rw [List.flatMap_cons, utf8EncodeChar_ascii hc, ih]
    rfl

/-- `%` でない byte は decode で素通しする。 -/
theorem percentDecodeBytes_cons_ne {b : UInt8} (h : ¬(b.toNat == 0x25) = true) (rest : Bytes) :
    percentDecodeBytes (b :: rest) = b :: percentDecodeBytes rest := by
  match rest with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rw [percentDecodeBytes, if_neg h]

/-- `percentEncodeByte` が使う 16 進の数字。 -/
def hexDigitChar (n : Nat) : Char := Char.ofNat (if n < 10 then 0x30 + n else 0x41 + n - 10)

theorem percentEncodeByte_eq (b : UInt8) :
    percentEncodeByte b = ['%', hexDigitChar (b.toNat / 16), hexDigitChar (b.toNat % 16)] := rfl

theorem hexDigitChar_lt : ∀ n : Nat, n < 16 → (hexDigitChar n).toNat < 128
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

theorem hexValue_hexDigitChar : ∀ n : Nat, n < 16 → hexValue (hexDigitChar n) = some n
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

/-- ASCII の文字は byte にして戻しても同じ文字である。 -/
theorem charOfByte_ascii {c : Char} (h : c.toNat < 128) :
    Char.ofNat (UInt8.ofNat c.toNat).toNat = c := by
  rw [show (UInt8.ofNat c.toNat).toNat = c.toNat from by
    simp [Nat.mod_eq_of_lt (show c.toNat < 256 by omega)]]
  exact Char.ofNat_toNat c

/-- **percent-encode した byte は読み戻せる。** -/
theorem percentDecode_encodeByte (b : UInt8) (rest : Bytes) :
    percentDecodeBytes (asciiBytes (percentEncodeByte b) ++ rest)
      = b :: percentDecodeBytes rest := by
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  have hhi : b.toNat / 16 < 16 := by omega
  have hlo : b.toNat % 16 < 16 := by omega
  simp only [percentEncodeByte_eq, asciiBytes, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  rw [percentDecodeBytes]
  simp only [show (UInt8.ofNat (Char.toNat '%')).toNat = 0x25 from by decide, beq_self_eq_true,
    if_pos, charOfByte_ascii (hexDigitChar_lt _ hhi), charOfByte_ascii (hexDigitChar_lt _ hlo),
    hexValue_hexDigitChar _ hhi, hexValue_hexDigitChar _ hlo]
  rw [show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat from by omega]
  simp

/-! ## `+` の扱い -/

theorem hexDigitChar_ne_plus : ∀ n : Nat, n < 16 →
    ((UInt8.ofNat (hexDigitChar n).toNat).toNat == 0x2B) = false
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

@[simp] theorem plusToSpace_append (a b : Bytes) :
    plusToSpace (a ++ b) = plusToSpace a ++ plusToSpace b := List.map_append

@[simp] theorem asciiBytes_append (a b : List Char) :
    asciiBytes (a ++ b) = asciiBytes a ++ asciiBytes b := List.map_append

/-- percent-encode した byte 列に `+` は現れない。 -/
theorem plusToSpace_encodeByte (b : UInt8) :
    plusToSpace (asciiBytes (percentEncodeByte b)) = asciiBytes (percentEncodeByte b) := by
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  simp only [percentEncodeByte_eq, asciiBytes, plusToSpace, List.map_cons, List.map_nil,
    hexDigitChar_ne_plus _ (show b.toNat / 16 < 16 by omega),
    hexDigitChar_ne_plus _ (show b.toNat % 16 < 16 by omega),
    show ((UInt8.ofNat (Char.toNat '%')).toNat == 0x2B) = false from by decide, if_false,
    Bool.false_eq_true]

theorem plusToSpace_encodeBytes : ∀ bs : Bytes,
    plusToSpace (asciiBytes (bs.flatMap percentEncodeByte))
      = asciiBytes (bs.flatMap percentEncodeByte)
  | [] => rfl
  | b :: rest => by
    rw [List.flatMap_cons, asciiBytes_append, plusToSpace_append, plusToSpace_encodeByte,
      plusToSpace_encodeBytes rest]

/-- **percent-encode した byte 列は読み戻せる。** -/
theorem percentDecode_encodeBytes : ∀ (bs rest : Bytes),
    percentDecodeBytes (asciiBytes (bs.flatMap percentEncodeByte) ++ rest)
      = bs ++ percentDecodeBytes rest
  | [], rest => by simp [asciiBytes]
  | b :: bs, rest => by
    rw [List.flatMap_cons, asciiBytes_append, List.append_assoc, percentDecode_encodeByte,
      percentDecode_encodeBytes bs rest, List.cons_append]

/-! ## 成分の往復 -/

/-- 素通しされる文字は ASCII で、`+` でも `%` でもない。 -/
theorem not_set_bounds {c : Char} (h : urlencodedSet c = false) :
    c.toNat < 128 ∧ c.toNat ≠ 0x2B ∧ c.toNat ≠ 0x25 := by
  unfold urlencodedSet at h
  simp only [Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((h | h) | h) | h) | h)
  · simp only [isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
      isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  all_goals (subst h; exact ⟨by decide, by decide, by decide⟩)

/-- **serialize した一文字ぶんを読み戻すと、その文字の UTF-8 になる。** -/
theorem decode_encodeChar (c : Char) (rest : Bytes) :
    percentDecodeBytes (plusToSpace (asciiBytes (urlencodedEncodeChar c) ++ rest))
      = utf8EncodeChar c ++ percentDecodeBytes (plusToSpace rest) := by
  unfold urlencodedEncodeChar
  split
  · -- space は `+` になり、読み戻すと 0x20 に戻る
    next hsp =>
    have hc : c = ' ' := by simpa using hsp
    subst hc
    simp only [asciiBytes, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      plusToSpace, List.map_cons, show ((UInt8.ofNat (Char.toNat '+')).toNat == 0x2B) = true from
        by decide, if_pos]
    rw [percentDecodeBytes_cons_ne (by decide)]
    rfl
  · split
    · -- set に入るものは `%XX` になる
      rw [plusToSpace_append, plusToSpace_encodeBytes, percentDecode_encodeBytes]
    · -- 素通し
      next hset =>
      obtain ⟨hlt, hplus, hpct⟩ := not_set_bounds (by simpa using hset)
      have hb : (UInt8.ofNat c.toNat).toNat = c.toNat := by
        simp [Nat.mod_eq_of_lt (show c.toNat < 256 by omega)]
      simp only [asciiBytes, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        plusToSpace, List.map_cons]
      rw [if_neg (by simp [hb]; omega), percentDecodeBytes_cons_ne (by simp [hb]; omega),
        utf8EncodeChar_ascii (by omega)]
      rfl

/-- serialize した成分を読み戻すと、元の文字列の UTF-8 になる。 -/
theorem decode_encodeList : ∀ (l : List Char) (rest : Bytes),
    percentDecodeBytes (plusToSpace (asciiBytes (l.flatMap urlencodedEncodeChar) ++ rest))
      = l.flatMap utf8EncodeChar ++ percentDecodeBytes (plusToSpace rest)
  | [], rest => by simp [asciiBytes]
  | c :: l, rest => by
    rw [List.flatMap_cons, asciiBytes_append, List.append_assoc, decode_encodeChar,
      decode_encodeList l rest, List.flatMap_cons, List.append_assoc]

/-- **成分の往復。** serialize して読み戻すと元の文字列に戻る。 -/
theorem decodeComponent (s : String) :
    utf8DecodeString (percentDecodeBytes (plusToSpace (asciiBytes (urlencodedEncode s)))) = s := by
  have h : percentDecodeBytes (plusToSpace (asciiBytes (urlencodedEncode s))) = utf8Encode s := by
    have h0 := decode_encodeList s.toList []
    rw [show percentDecodeBytes (plusToSpace []) = [] from rfl, List.append_nil] at h0
    simpa [urlencodedEncode, utf8Encode, plusToSpace, asciiBytes] using h0
  rw [h, utf8DecodeString_encode]

end Url
