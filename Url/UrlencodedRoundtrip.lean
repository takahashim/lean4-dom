import Url.Urlencoded

/-!
# `application/x-www-form-urlencoded` の往復

URL Standard §5。serialize したものを parse すると元に戻る。

## 二段に分かれる

* **成分の往復**（この file）。`urlencodedEncode` した文字列を
  `plusToSpace` → percent-decode → UTF-8 decode で読み戻すと元に戻る。
* **分割の逆**。`&` と最初の `=` での分割が連結の逆になること。
  `urlencodedEncode_no_separator`（serialize した成分に `&` も `=` も現れない）が
  その足場である。どちらの分割も accumulator で書かれているので、その形の帰納法を使う。

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

/-! ## `&` での分割 -/

/-- 区切りを含まない塊は accumulator にそのまま積まれる。 -/
theorem splitAmp_go_append : ∀ (p : Bytes), (∀ b ∈ p, ¬(b.toNat == 0x26) = true) →
    ∀ (rest acc : Bytes), splitAmp.go (p ++ rest) acc = splitAmp.go rest (p.reverse ++ acc)
  | [], _, rest, acc => by simp
  | b :: p, h, rest, acc => by
    rw [List.cons_append, splitAmp.go, if_neg (h b List.mem_cons_self),
      splitAmp_go_append p (fun x hx => h x (List.mem_cons_of_mem _ hx)) rest (b :: acc)]
    simp

/-- **`&` での分割は連結の逆である。** -/
theorem splitAmp_intercalate : ∀ (p : Bytes) (ps : List Bytes),
    (∀ b ∈ p, ¬(b.toNat == 0x26) = true) →
    (∀ q ∈ ps, ∀ b ∈ q, ¬(b.toNat == 0x26) = true) →
    splitAmp (p ++ ps.flatMap (fun x => UInt8.ofNat 0x26 :: x)) = p :: ps
  | p, [], hp, _ => by
    show splitAmp.go (p ++ []) [] = _
    rw [splitAmp_go_append p hp [] []]
    simp [splitAmp.go]
  | p, q :: qs, hp, hq => by
    show splitAmp.go (p ++ (q :: qs).flatMap (fun x => UInt8.ofNat 0x26 :: x)) [] = _
    rw [show (q :: qs).flatMap (fun x => UInt8.ofNat 0x26 :: x)
        = UInt8.ofNat 0x26 :: (q ++ qs.flatMap (fun x => UInt8.ofNat 0x26 :: x)) from by simp,
      splitAmp_go_append p hp _ [], splitAmp.go, if_pos (by decide)]
    simp only [List.append_nil, List.reverse_reverse]
    rw [show splitAmp.go (q ++ qs.flatMap (fun x => UInt8.ofNat 0x26 :: x)) []
        = splitAmp (q ++ qs.flatMap (fun x => UInt8.ofNat 0x26 :: x)) from rfl,
      splitAmp_intercalate q qs (hq q List.mem_cons_self)
        (fun x hx => hq x (List.mem_cons_of_mem _ hx))]

/-! ## 最初の `=` での分割 -/

theorem splitFirstEq_go_append : ∀ (p : Bytes), (∀ b ∈ p, ¬(b.toNat == 0x3D) = true) →
    ∀ (rest acc : Bytes),
      splitFirstEq.go (p ++ rest) acc = splitFirstEq.go rest (p.reverse ++ acc)
  | [], _, rest, acc => by simp
  | b :: p, h, rest, acc => by
    rw [List.cons_append, splitFirstEq.go, if_neg (h b List.mem_cons_self),
      splitFirstEq_go_append p (fun x hx => h x (List.mem_cons_of_mem _ hx)) rest (b :: acc)]
    simp

/-- **最初の `=` での分割は name と value を戻す。** -/
theorem splitFirstEq_append (name value : Bytes)
    (h : ∀ b ∈ name, ¬(b.toNat == 0x3D) = true) :
    splitFirstEq (name ++ UInt8.ofNat 0x3D :: value) = (name, value) := by
  show splitFirstEq.go (name ++ UInt8.ofNat 0x3D :: value) [] = _
  rw [splitFirstEq_go_append name h _ [], splitFirstEq.go, if_pos (by decide)]
  simp

/-! ## 区切りが成分に現れないこと -/

theorem toNat_ne_of_ne {c d : Char} (h : c ≠ d) : c.toNat ≠ d.toNat := by
  intro he
  exact h (by rw [← Char.ofNat_toNat c, ← Char.ofNat_toNat d, he])

theorem percentEncodeByte_ascii (b : UInt8) : ∀ c ∈ percentEncodeByte b, c.toNat < 128 := by
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  intro c hc
  rw [percentEncodeByte_eq] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h
  · subst h; decide
  · subst h; exact hexDigitChar_lt _ (by omega)
  · subst h; exact hexDigitChar_lt _ (by omega)

/-- serialize した成分は ASCII だけからなる。 -/
theorem urlencodedEncode_ascii (s : String) : ∀ c ∈ urlencodedEncode s, c.toNat < 128 := by
  intro c hc
  unfold urlencodedEncode at hc
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hc
  unfold urlencodedEncodeChar at hx
  split at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; decide
  · split at hx
    · obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hx
      exact percentEncodeByte_ascii b c hb
    · next hset =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact (not_set_bounds (by simpa using hset)).1

/-- ASCII の文字を byte にすると値は変わらない。 -/
theorem toNat_asciiByte {c : Char} (h : c.toNat < 128) :
    (UInt8.ofNat c.toNat).toNat = c.toNat := by
  simp [Nat.mod_eq_of_lt (show c.toNat < 256 by omega)]

theorem asciiBytes_no_sep (s : String) (d : Char) (hd : d = '&' ∨ d = '=') :
    ∀ b ∈ asciiBytes (urlencodedEncode s), ¬(b.toNat == d.toNat) = true := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := List.mem_map.mp hb
  subst hcb
  have hasc := urlencodedEncode_ascii s c hc
  have hne := urlencodedEncode_no_separator s c hc
  rw [toNat_asciiByte hasc]
  simp only [beq_iff_eq]
  rcases hd with h | h <;> subst h
  · exact toNat_ne_of_ne hne.1
  · exact toNat_ne_of_ne hne.2

/-! ## 全体の往復 -/

/-- serialize した一組ぶんの文字列。 -/
def partChars (t : String × String) : List Char :=
  urlencodedEncode t.1 ++ ['='] ++ urlencodedEncode t.2

theorem serializeUrlencoded_eq (l : List (String × String)) :
    serializeUrlencoded l = String.ofList (intercalateChars ['&'] (l.map partChars)) := rfl

theorem partChars_ascii (t : String × String) : ∀ c ∈ partChars t, c.toNat < 128 := by
  intro c hc
  unfold partChars at hc
  rcases List.mem_append.mp hc with h | h
  · rcases List.mem_append.mp h with h | h
    · exact urlencodedEncode_ascii _ c h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; decide
  · exact urlencodedEncode_ascii _ c h

theorem intercalateChars_ascii : ∀ (ps : List (List Char)),
    (∀ p ∈ ps, ∀ c ∈ p, c.toNat < 128) → ∀ c ∈ intercalateChars ['&'] ps, c.toNat < 128
  | [], _ => by simp [intercalateChars]
  | a :: as, h => by
    intro c hc
    unfold intercalateChars at hc
    rcases List.mem_append.mp hc with hm | hm
    · exact h a List.mem_cons_self c hm
    · obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.mp hm
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hcx
      rcases hcx with hcx | hcx
      · subst hcx; decide
      · exact h x (List.mem_cons_of_mem _ hx) c hcx

theorem asciiBytes_intercalate (a : List Char) (as : List (List Char)) :
    asciiBytes (intercalateChars ['&'] (a :: as))
      = asciiBytes a ++ (as.map asciiBytes).flatMap (fun y => UInt8.ofNat 0x26 :: y) := by
  unfold intercalateChars asciiBytes
  rw [List.map_append, List.map_flatMap, List.flatMap_map]
  rfl

/-- 区切りでない文字しか無い列は、byte にしてもその区切りを含まない。 -/
theorem asciiBytes_ne (l : List Char) (d : Char) (hasc : ∀ c ∈ l, c.toNat < 128)
    (hne : ∀ c ∈ l, c ≠ d) : ∀ b ∈ asciiBytes l, ¬(b.toNat == d.toNat) = true := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := List.mem_map.mp hb
  subst hcb
  rw [toNat_asciiByte (hasc c hc)]
  simp only [beq_iff_eq]
  exact toNat_ne_of_ne (hne c hc)

theorem partChars_ne (t : String × String) (d : Char) (hd : d = '&' ∨ d = '=') (hda : d ≠ '=') :
    ∀ c ∈ partChars t, c ≠ d := by
  intro c hc
  unfold partChars at hc
  rcases List.mem_append.mp hc with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases hd with h' | h' <;> subst h'
      · exact (urlencodedEncode_no_separator _ c h).1
      · exact (urlencodedEncode_no_separator _ c h).2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; exact fun he => hda he.symm
  · rcases hd with h' | h' <;> subst h'
    · exact (urlencodedEncode_no_separator _ c h).1
    · exact (urlencodedEncode_no_separator _ c h).2

theorem partBytes_no_amp (t : String × String) :
    ∀ b ∈ asciiBytes (partChars t), ¬(b.toNat == 0x26) = true :=
  asciiBytes_ne _ '&' (partChars_ascii t) (partChars_ne t '&' (Or.inl rfl) (by decide))

/-- 一組ぶんの byte 列を読み戻すと元の組に戻る。 -/
theorem parse_partBytes (t : String × String) :
    (if (asciiBytes (partChars t)).isEmpty then none
      else
        let (name, value) := splitFirstEq (asciiBytes (partChars t))
        let dec := fun (x : Bytes) => utf8DecodeString (percentDecodeBytes (plusToSpace x))
        some (dec name, dec value)) = some t := by
  have hsplit : asciiBytes (partChars t)
      = asciiBytes (urlencodedEncode t.1) ++ UInt8.ofNat 0x3D
        :: asciiBytes (urlencodedEncode t.2) := by
    unfold partChars asciiBytes
    simp
  have hne : ∀ b ∈ asciiBytes (urlencodedEncode t.1), ¬(b.toNat == 0x3D) = true :=
    asciiBytes_ne _ '=' (urlencodedEncode_ascii _)
      (fun c hc => (urlencodedEncode_no_separator _ c hc).2)
  rw [hsplit, splitFirstEq_append _ _ hne]
  simp only [decodeComponent]
  rw [if_neg (by cases h : asciiBytes (urlencodedEncode t.1) <;> simp)]

theorem filterMap_parts : ∀ (ts : List (String × String)),
    (ts.map (fun u => asciiBytes (partChars u))).filterMap
      (fun bs => if bs.isEmpty then none
        else
          let (name, value) := splitFirstEq bs
          let dec := fun (x : Bytes) => utf8DecodeString (percentDecodeBytes (plusToSpace x))
          some (dec name, dec value)) = ts
  | [] => rfl
  | u :: us => by
    rw [List.map_cons, List.filterMap_cons, parse_partBytes u, filterMap_parts us]

/-- **§5 の往復。** serialize して parse すると元に戻る。 -/
theorem parse_serialize (l : List (String × String)) :
    parseUrlencodedString (serializeUrlencoded l) = l := by
  have hascii : ∀ c ∈ intercalateChars ['&'] (l.map partChars), c.toNat < 128 :=
    intercalateChars_ascii _ (by
      intro p hp
      obtain ⟨t, _, hpt⟩ := List.mem_map.mp hp
      subst hpt
      exact partChars_ascii t)
  rw [parseUrlencodedString, serializeUrlencoded_eq, utf8Encode_ofList_ascii _ hascii]
  match l with
  | [] => rfl
  | t :: ts =>
    rw [List.map_cons, asciiBytes_intercalate]
    unfold parseUrlencoded
    rw [splitAmp_intercalate _ _
      (partBytes_no_amp t) (by
        intro q hq
        obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
        obtain ⟨u, _, hup⟩ := List.mem_map.mp hp
        subst hup; subst hpq
        exact partBytes_no_amp u)]
    show (asciiBytes (partChars t) :: (ts.map partChars).map asciiBytes).filterMap _ = _
    rw [show (ts.map partChars).map asciiBytes
        = ts.map (fun u => asciiBytes (partChars u)) from by simp]
    rw [List.filterMap_cons, parse_partBytes t, filterMap_parts ts]

end Url
