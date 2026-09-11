import Infra.Ascii

/-!
# Punycode（RFC 3492）

IDNA が使う bootstring の実装。**Unicode の表を一切使わない**、閉じたアルゴリズムである。
UTS #46 のうち表に依存しない部分はここだけで、残り（写像表・NFC・Bidi・Joiner）は
実行時に外から与える（`Url/Idna.lean`）。

## 仕組み

非 ASCII の code point を、その値の昇順に「前回からの差分」で符号化する。
差分は可変長の 36 進で、桁ごとの閾値が **適応バイアス** で変わる。
偏った入力（同じ文字種が続く）ほど短くなる。

## 停止性

fuel は使わない。三つのループそれぞれに測度がある。

* `adaptLoop` — `delta` が 35 で割られて減る
* `encodeDigits` — `q` が減る（閾値 `t` が 1 以上なので `(q - t) / (36 - t) < q`）
* `encodeLoop` — 残りの code point の個数が減る
* `decodeDigits` / `decodeLoop` — 残りの入力が減る
-/

namespace Url.Punycode

open Infra

/-! ## 定数と小道具 -/

/-- 桁の値を文字にする。0-25 が `a`-`z`、26-35 が `0`-`9`。 -/
def digitChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (0x61 + d) else Char.ofNat (0x30 + d - 26)

/-- 文字を桁の値にする。大文字も受ける。 -/
def digitValue (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x61 ≤ n && n ≤ 0x7A then some (n - 0x61)
  else if 0x41 ≤ n && n ≤ 0x5A then some (n - 0x41)
  else if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30 + 26)
  else none

/-- `k` 桁目の閾値。`tmin = 1`、`tmax = 26`。 -/
def threshold (k bias : Nat) : Nat :=
  if k ≤ bias then 1 else if bias + 26 ≤ k then 26 else k - bias

theorem threshold_pos (k bias : Nat) : 1 ≤ threshold k bias := by
  unfold threshold
  split
  · omega
  · split <;> omega

theorem threshold_le (k bias : Nat) : threshold k bias ≤ 26 := by
  unfold threshold
  split
  · omega
  · split <;> omega

/-- 適応バイアスの縮小ループ。`delta` が `455` 以下になるまで 35 で割る。 -/
def adaptLoop (delta k : Nat) : Nat × Nat :=
  if 455 < delta then adaptLoop (delta / 35) (k + 36) else (delta, k)
termination_by delta
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- RFC 3492 の adapt。`damp = 700`、`skew = 38`、`base - tmin + 1 = 36`。 -/
def adapt (delta numpoints : Nat) (firstTime : Bool) : Nat :=
  let d0 := if firstTime then delta / 700 else delta / 2
  let d1 := d0 + d0 / numpoints
  let r := adaptLoop d1 0
  r.2 + 36 * r.1 / (r.1 + 38)

/-! ## 符号化 -/

/-- 差分 `q` を可変長の桁列にする。 -/
def encodeDigits (bias : Nat) (k q : Nat) : List Char :=
  let t := threshold k bias
  if q < t then [digitChar q]
  else digitChar (t + (q - t) % (36 - t)) :: encodeDigits bias (k + 36) ((q - t) / (36 - t))
termination_by q
decreasing_by
  have _h1 := threshold_pos k bias
  have _h2 := threshold_le k bias
  calc (q - threshold k bias) / (36 - threshold k bias)
      ≤ q - threshold k bias := Nat.div_le_self _ _
    _ < q := by omega

/-- 符号化の途中の状態。 -/
structure EncState where
  out : List Char
  delta : Nat
  bias : Nat
  h : Nat

/-- 入力を 1 文字見て状態を進める。 -/
def scanOne (b m : Nat) (st : EncState) (c : Char) : EncState :=
  if c.toNat < m then { st with delta := st.delta + 1 }
  else if c.toNat == m then
    { out := st.out ++ encodeDigits st.bias 36 st.delta, delta := 0,
      bias := adapt st.delta (st.h + 1) (st.h == b), h := st.h + 1 }
  else st

/-- 非 ASCII の code point を昇順に処理する。 -/
def encodeLoop (input : List Char) (b : Nat) : List Nat → Nat → EncState → EncState
  | [], _, st => st
  | m :: rest, n, st =>
    let st1 := { st with delta := st.delta + (m - n) * (st.h + 1) }
    let st2 := input.foldl (scanOne b m) st1
    encodeLoop input b rest (m + 1) { st2 with delta := st2.delta + 1 }

/-- 昇順に重複なく入れる。 -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: insertSorted x ys

def sortedDistinct : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortedDistinct xs)

/--
RFC 3492 の符号化。`xn--` は付けない（label の変換は呼ぶ側の仕事）。

基本 code point が一つでもあれば区切りの `-` を付ける。すべて ASCII の入力でも付く
（RFC の例 (P) `-> $1.00 <-` が `-> $1.00 <--` になるのがこれである）。
-/
def encode (input : List Char) : List Char :=
  let basic := input.filter (fun c => c.toNat < 0x80)
  let todo := sortedDistinct ((input.filter (fun c => 0x80 ≤ c.toNat)).map Char.toNat)
  let st := encodeLoop input basic.length todo 128
    { out := [], delta := 0, bias := 72, h := basic.length }
  basic ++ (if basic.isEmpty then [] else ['-']) ++ st.out

/-! ## 復号 -/

/-- 可変長整数を一つ読む。返すのは（増えた `i`、残りの入力）。 -/
def decodeDigits (bias : Nat) : List Char → Nat → Nat → Nat → Option (Nat × List Char)
  | [], _, _, _ => none
  | c :: rest, k, w, i =>
    match digitValue c with
    | none => none
    | some d =>
      if d < threshold k bias then some (i + d * w, rest)
      else decodeDigits bias rest (k + 36) (w * (36 - threshold k bias)) (i + d * w)

/-- 可変長整数を読むと入力は必ず減る。復号の停止性に要る。 -/
theorem decodeDigits_length : ∀ (bias : Nat) (l : List Char) (k w i : Nat) (r : Nat × List Char),
    decodeDigits bias l k w i = some r → r.2.length < l.length
  | _, [], _, _, _, _, h => by simp [decodeDigits] at h
  | bias, c :: rest, k, w, i, r, h => by
    rw [decodeDigits] at h
    split at h
    · simp at h
    · split at h
      · rw [← Option.some.inj h]; simp
      · have := decodeDigits_length bias rest (k + 36) _ _ r h
        simp; omega

/-- 一つずつ code point を挿していく。 -/
def decodeLoop (bias n i : Nat) (out : List Char) : List Char → Option (List Char)
  | [] => some out
  | c :: rest =>
    match hd : decodeDigits bias (c :: rest) 36 1 i with
    | none => none
    | some (i', rem) =>
      let numpoints := out.length + 1
      let n' := n + i' / numpoints
      let pos := i' % numpoints
      if n' < 0xD800 || (0xDFFF < n' && n' < 0x110000) then
        decodeLoop (adapt (i' - i) numpoints (i == 0)) n' (pos + 1)
          (out.insertIdx pos (Char.ofNat n')) rem
      else none
termination_by l => l.length
decreasing_by
  have := decodeDigits_length bias (c :: rest) 36 1 i (i', rem) hd
  simpa using this

/-- 最後の区切りで基本部分と拡張部分に分ける。区切りが無ければ基本部分は空。 -/
def splitLastDelim (input : List Char) : List Char × List Char :=
  match input.reverse.span (fun c => c != '-') with
  | (revTail, []) => ([], revTail.reverse)
  | (revTail, _ :: revHead) => (revHead.reverse, revTail.reverse)

/-- RFC 3492 の復号。`xn--` は剥がしてから渡す。 -/
def decode (input : List Char) : Option (List Char) :=
  let (basic, ext) := splitLastDelim input
  if basic.any (fun c => 0x80 ≤ c.toNat) then none
  else decodeLoop 72 128 0 basic ext

/-! ## 出力が ASCII であること -/

theorem toNat_ofNat_ascii {n : Nat} (h : n < 0x80) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dif_pos (show n.isValidChar from Or.inl (by omega))]
  unfold Char.ofNatAux Char.toNat
  simp

theorem digitChar_ascii {d : Nat} (h : d < 36) : (digitChar d).toNat < 0x80 := by
  unfold digitChar
  split
  · rw [toNat_ofNat_ascii (by omega)]; omega
  · rw [toNat_ofNat_ascii (by omega)]; omega

theorem encodeDigits_ascii (bias : Nat) : ∀ (k q : Nat) (c : Char),
    c ∈ encodeDigits bias k q → c.toNat < 0x80
  | k, q, c, hc => by
    rw [encodeDigits] at hc
    have h1 := threshold_pos k bias
    have h2 := threshold_le k bias
    split at hc
    · next hq =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; exact digitChar_ascii (by omega)
    · next hq =>
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc
        refine digitChar_ascii ?_
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      · exact encodeDigits_ascii bias (k + 36) _ c hc
termination_by _ q => q
decreasing_by
  have _h1 := threshold_pos k bias
  have _h2 := threshold_le k bias
  calc (q - threshold k bias) / (36 - threshold k bias)
      ≤ q - threshold k bias := Nat.div_le_self _ _
    _ < q := by omega

theorem scanOne_ascii (b m : Nat) (st : EncState) (c : Char)
    (h : ∀ x ∈ st.out, x.toNat < 0x80) : ∀ x ∈ (scanOne b m st c).out, x.toNat < 0x80 := by
  unfold scanOne
  split
  · exact h
  · split
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · exact encodeDigits_ascii st.bias 36 st.delta x hx
    · exact h

theorem scanFold_ascii (b m : Nat) : ∀ (l : List Char) (st : EncState),
    (∀ x ∈ st.out, x.toNat < 0x80) → ∀ x ∈ (l.foldl (scanOne b m) st).out, x.toNat < 0x80
  | [], _, h => h
  | c :: rest, st, h => scanFold_ascii b m rest (scanOne b m st c) (scanOne_ascii b m st c h)

theorem encodeLoop_ascii (input : List Char) (b : Nat) : ∀ (todo : List Nat) (n : Nat)
    (st : EncState), (∀ x ∈ st.out, x.toNat < 0x80) →
    ∀ x ∈ (encodeLoop input b todo n st).out, x.toNat < 0x80
  | [], _, _, h => h
  | m :: rest, n, st, h => by
    rw [encodeLoop]
    refine encodeLoop_ascii input b rest (m + 1) _ ?_
    exact scanFold_ascii b m input _ h

/-- **符号化の出力は ASCII だけからなる。** -/
theorem encode_ascii (input : List Char) : ∀ c ∈ encode input, c.toNat < 0x80 := by
  intro c hc
  unfold encode at hc
  rcases List.mem_append.mp hc with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · have := (List.mem_filter.mp hx).2
      simpa using this
    · split at hx
      · simp at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; decide
  · exact encodeLoop_ascii input _ _ _ _ (by simp) c hx

end Url.Punycode
