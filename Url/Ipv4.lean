import Infra.Ascii

/-!
# IPv4 parser

WHATWG URL Standard §3.3 の "IPv4 number parser"、"IPv4 parser"、
"ends in a number" checker、および IPv4 serializer。

どれも文字列から数値への純粋な関数で、木も状態も要らない。
歴史的に実装が食い違いやすいところ（16 進と 8 進の接頭辞、
part 数が 4 でないときの畳み込み、最後の part の上限）が全部ここに集まっている。
-/

namespace Url

open Infra

/-- 区切りで厳密に分ける（Infra の "strictly split"）。空の断片も残す。 -/
def strictSplit (l : List Char) (sep : Char) : List (List Char) :=
  go l []
where
  go : List Char → List Char → List (List Char)
    | [], acc => [acc.reverse]
    | c :: rest, acc => if c == sep then acc.reverse :: go rest [] else go rest (c :: acc)

/-- 基数 `r` の digit の値。 -/
def radixDigit (r : Nat) (c : Char) : Option Nat :=
  match hexValue c with
  | none => none
  | some v => if v < r then some v else none

/-- 基数 `r` で読む。空でなく全部が digit ならその値。 -/
def parseRadix (r : Nat) : List Char → Option Nat
  | [] => none
  | l => l.foldl (fun acc c =>
      match acc, radixDigit r c with
      | some a, some v => some (a * r + v)
      | _, _ => none) (some 0)

/--
URL Standard §3.3 "IPv4 number parser"。

返すのは (値, 10 進でなかったか)。仕様の validation error は
「その旨の boolean を返す」形で持つ（parse 自体は失敗しない）。
-/
def ipv4NumberParser (input : List Char) : Option (Nat × Bool) :=
  -- step 1
  match input with
  | [] => none
  | _ =>
    -- step 4-5
    let (rest, radix, validationError) :=
      match input with
      | '0' :: 'X' :: t => (t, 16, true)
      | '0' :: 'x' :: t => (t, 16, true)
      | '0' :: (t : List Char) =>
        if t.isEmpty then (['0'], 10, false) else (t, 8, true)
      | _ => (input, 10, false)
    -- step 6
    if rest.isEmpty then some (0, true)
    -- step 7-8
    else match parseRadix radix rest with
      | none => none
      | some v => some (v, validationError)

/--
IPv4 parser と "ends in a number" の step 1-2。

U+002E で厳密に分け、末尾が空 part ならそれを落とす（part が 2 個以上のとき）。
-/
def ipv4Parts (input : List Char) : List (List Char) :=
  let parts := strictSplit input '.'
  if (parts.getLast?.map List.isEmpty).getD false && parts.length > 1 then parts.dropLast
  else parts

/--
URL Standard §3.3 "ends in a number" checker。

最後の part が 10 進の数字だけか、IPv4 number として読めるなら true。
host parser がこれで IPv4 として読むかどうかを決める。
-/
def endsInANumber (input : List Char) : Bool :=
  match (ipv4Parts input).getLast? with
  | none => false
  | some last =>
    if !last.isEmpty && last.all (fun c => isAsciiDigit c) then true
    else (ipv4NumberParser last).isSome

/--
URL Standard §3.3 "IPv4 parser"。失敗したら `none`。

step 4 の「part 数が 4 を超えたら失敗」は、数値に直した後の `numbers` の側で見る。
`mapM` は長さを変えないので同じことで、証明が素直になる。
-/
def ipv4Parser (input : List Char) : Option Nat :=
  -- step 6（step 1-2 は `ipv4Parts`）
  match (ipv4Parts input).mapM (fun p => (ipv4NumberParser p).map Prod.fst) with
  | none => none
  | some numbers =>
    -- step 4
    if numbers.length > 4 || numbers.isEmpty then none
    -- step 8：最後以外は 255 以下でなければならない
    else if numbers.dropLast.any (fun n => n > 255) then none
    else match numbers.getLast? with
      | none => none
      | some last =>
        -- step 9：最後は 256^(5 - size) 未満でなければならない
        if last ≥ 256 ^ (5 - numbers.length) then none
        else
          -- step 10-13。counter が 0 から始まるので、畳み込んだ値に 256^(5 - size) を掛ける。
          some (numbers.dropLast.foldl (fun acc n => acc * 256 + n) 0 *
            256 ^ (5 - numbers.length) + last)

/-- URL Standard §3.5 IPv4 serializer。 -/
def ipv4Serializer (addr : Nat) : String :=
  let go (n : Nat) : List String :=
    [toString (n / 16777216 % 256), toString (n / 65536 % 256),
     toString (n / 256 % 256), toString (n % 256)]
  String.intercalate "." (go addr)

/-! ## 性質 -/

theorem radixDigit_lt {r : Nat} {c : Char} {v : Nat} (h : radixDigit r c = some v) : v < r := by
  unfold radixDigit at h
  split at h
  · simp at h
  · next w hw =>
    split at h
    · next hlt => rw [← Option.some.inj h]; exact hlt
    · simp at h

/-- 256 進で畳み込んだ値の上限。各項が 255 以下なら桁数ぶんに収まる。 -/
theorem foldl_base256_lt : ∀ (l : List Nat) (a k : Nat), (∀ n ∈ l, n ≤ 255) → a < 256 ^ k →
    l.foldl (fun acc n => acc * 256 + n) a < 256 ^ (k + l.length)
  | [], a, k, _, ha => by simpa using ha
  | n :: rest, a, k, hle, ha => by
    have hn : n ≤ 255 := hle n List.mem_cons_self
    have hstep : a * 256 + n < 256 ^ (k + 1) := by
      have : 256 ^ (k + 1) = 256 ^ k * 256 := by rw [Nat.pow_succ]
      omega
    have := foldl_base256_lt rest (a * 256 + n) (k + 1)
      (fun m hm => hle m (List.mem_cons_of_mem _ hm)) hstep
    show List.foldl _ (a * 256 + n) rest < _
    have hlen : k + 1 + rest.length = k + (n :: rest).length := by simp; omega
    rw [← hlen]
    exact this

/--
IPv4 parser が返す値は 32 bit に収まる。

part 数が 4 でなくても成り立つ。最後の part の上限（step 9）が
残りの桁数をちょうど埋めるように決まっているからである。
-/
theorem ipv4Parser_lt {input : List Char} {a : Nat} (h : ipv4Parser input = some a) :
    a < 256 ^ 4 := by
  unfold ipv4Parser at h
  split at h
  · simp at h
  · next numbers hnum =>
    split at h
    · simp at h
    · next hsize =>
      split at h
      · simp at h
      · next hbig =>
        split at h
        · simp at h
        · next last hlast =>
          split at h
          · simp at h
          · next hlt =>
            rw [← Option.some.inj h]
            simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, not_or] at hsize
            have hlen4 : numbers.length ≤ 4 := by omega
            have hpos : 1 ≤ numbers.length := by
              cases hn : numbers with
              | nil => exact absurd hn hsize.2
              | cons _ t => simp
            -- 最後以外は 255 以下
            have hle : ∀ n ∈ numbers.dropLast, n ≤ 255 := by
              intro n hn
              have hc : ¬ (decide (n > 255) = true) := fun hc =>
                hbig (List.any_eq_true.mpr ⟨n, hn, hc⟩)
              simp only [decide_eq_true_eq] at hc
              omega
            have hfold := foldl_base256_lt numbers.dropLast 0 0 hle (by simp)
            have hdl : numbers.dropLast.length = numbers.length - 1 := by simp
            rw [hdl] at hfold
            simp only [Nat.zero_add] at hfold
            have hlast' : last < 256 ^ (5 - numbers.length) := by omega
            -- 桁が合う：(size − 1) + (5 − size) = 4
            have hmul : 256 ^ (numbers.length - 1) * 256 ^ (5 - numbers.length) = 256 ^ 4 := by
              rw [← Nat.pow_add]
              congr 1
              omega
            have hsub : (256 ^ (numbers.length - 1) - 1) * 256 ^ (5 - numbers.length) =
                256 ^ (numbers.length - 1) * 256 ^ (5 - numbers.length) -
                  256 ^ (5 - numbers.length) := by
              rw [Nat.sub_mul, Nat.one_mul]
            have hmono := Nat.mul_le_mul_right (256 ^ (5 - numbers.length))
              (Nat.le_sub_one_of_lt hfold)
            -- 畳み込みぶんは 256^4 から最後の桁を引いた残りに収まる。
            have hkey : numbers.dropLast.foldl (fun acc n => acc * 256 + n) 0 *
                256 ^ (5 - numbers.length) ≤ 256 ^ 4 - 256 ^ (5 - numbers.length) := by
              rw [← hmul, ← hsub]; exact hmono
            have hfpos : 0 < 256 ^ (numbers.length - 1) := Nat.pow_pos (by omega)
            have hmle : 256 ^ (5 - numbers.length) ≤ 256 ^ 4 := by
              rw [← hmul]
              exact Nat.le_mul_of_pos_left _ hfpos
            omega

end Url
