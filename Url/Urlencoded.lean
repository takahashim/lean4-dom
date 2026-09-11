import Url.Percent

/-!
# application/x-www-form-urlencoded

WHATWG URL Standard §5.1 の parser と §5.2 の serializer。

parser は **byte 列** を受け取り、`&` と `=` で切り、`+` を空白に直してから
percent-decode して UTF-8 として読む。`Infra/Bytes.lean` の層の上に置ける。

encoding は UTF-8 に固定する（他の encoding は仕様も
「conforming なのは UTF-8 だけ」と書いている）。
-/

namespace Url

open Infra

/--
URL Standard §1.3 application/x-www-form-urlencoded percent-encode set。

仕様の注記どおり、**ASCII alphanumeric と `*` `-` `.` `_` 以外のすべて** である。
component set からの差分として書くより、この形のほうが読みやすく、
`serializeUrlencoded` の往復の証明でも扱いやすい。
-/
def urlencodedSet (c : Char) : Bool :=
  !(isAsciiAlphanumeric c || c == '*' || c == '-' || c == '.' || c == '_')

/-! ## serializer -/

/--
URL Standard §5.2 の serializer が一つの成分に施す変換。

space は `+`、それ以外で set に入るものは `%XX`。
-/
def urlencodedEncode (s : String) : List Char :=
  s.toList.flatMap fun c =>
    if c == ' ' then ['+']
    else if urlencodedSet c then (utf8EncodeChar c).flatMap percentEncodeByte
    else [c]

/-- URL Standard §5.2 application/x-www-form-urlencoded serializer。 -/
def serializeUrlencoded (tuples : List (String × String)) : String :=
  String.intercalate "&"
    (tuples.map fun t =>
      String.ofList (urlencodedEncode t.1) ++ "=" ++ String.ofList (urlencodedEncode t.2))

/-! ## parser -/

/-- byte 列を 0x26 (`&`) で切る。空の断片も残す（parser が step 3.1 で捨てる）。 -/
def splitAmp (input : Bytes) : List Bytes :=
  go input []
where
  go : Bytes → Bytes → List Bytes
    | [], acc => [acc.reverse]
    | b :: rest, acc => if b.toNat == 0x26 then acc.reverse :: go rest [] else go rest (b :: acc)

/-- 最初の 0x3D (`=`) で切る。無ければ全体と空。 -/
def splitFirstEq (bs : Bytes) : Bytes × Bytes :=
  go bs []
where
  go : Bytes → Bytes → Bytes × Bytes
    | [], acc => (acc.reverse, [])
    | b :: rest, acc => if b.toNat == 0x3D then (acc.reverse, rest) else go rest (b :: acc)

/-- 0x2B (`+`) を 0x20 (space) に直す（step 3.4）。 -/
def plusToSpace (bs : Bytes) : Bytes :=
  bs.map fun b => if b.toNat == 0x2B then UInt8.ofNat 0x20 else b

/-- URL Standard §5.1 application/x-www-form-urlencoded parser。 -/
def parseUrlencoded (input : Bytes) : List (String × String) :=
  (splitAmp input).filterMap fun bs =>
    if bs.isEmpty then none
    else
      let (name, value) := splitFirstEq bs
      let dec := fun (x : Bytes) => utf8DecodeString (percentDecodeBytes (plusToSpace x))
      some (dec name, dec value)

/-- 文字列を byte 列にしてから parse する。`URLSearchParams` の入口。 -/
def parseUrlencodedString (s : String) : List (String × String) :=
  parseUrlencoded (utf8Encode s)

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
serialize した成分には `&` も `=` も現れない。

parser が `&` と `=` で切れるのはこのためである。
`urlencodedSet` に入らないのは ASCII alphanumeric と `*` `-` `.` `_` だけで、
そのどれでもないので、素通しされる文字が区切りになることはない。
入る文字は `+` か `%XX` になり、`%` も 16 進の数字も区切りではない。
-/
theorem urlencodedEncode_no_separator (s : String) :
    ∀ c ∈ urlencodedEncode s, c ≠ '&' ∧ c ≠ '=' := by
  intro c hc
  unfold urlencodedEncode at hc
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hc
  split at hx
  · -- space は `+` になる
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact ⟨by decide, by decide⟩
  · split at hx
    · -- percent-encode された。`%` か 16 進の数字。
      obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hx
      have halnum := percentEncodeByte_alnum b c hb
      refine ⟨?_, ?_⟩ <;> intro heq <;> rw [heq] at halnum <;> revert halnum <;> decide
    · -- 素通し。set に入らないのは alphanumeric と `*` `-` `.` `_` だけ。
      next hset =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      refine ⟨?_, ?_⟩ <;> intro heq <;> rw [heq] at hset <;> revert hset <;> decide

end Url
