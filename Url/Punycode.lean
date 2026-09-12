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

/-- 桁の値を文字にして読み戻すと元に戻る。 -/
theorem digitValue_digitChar {d : Nat} (h : d < 36) : digitValue (digitChar d) = some d := by
  have hall : ∀ e ∈ List.range 36, digitValue (digitChar e) = some e := by decide
  exact hall d (List.mem_range.mpr h)

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
def encodeBasic (input : List Char) : List Char := input.filter (fun c => c.toNat < 0x80)

/-- 区切りより後ろ。非 ASCII の code point を差分の列に変えたものである。 -/
def encodeExt (input : List Char) : List Char :=
  (encodeLoop input (encodeBasic input).length
      (sortedDistinct ((input.filter (fun c => 0x80 ≤ c.toNat)).map Char.toNat)) 128
      { out := [], delta := 0, bias := 72, h := (encodeBasic input).length }).out

def encode (input : List Char) : List Char :=
  encodeBasic input
    ++ (if (encodeBasic input).isEmpty then [] else ['-'])
    ++ encodeExt input

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

/--
**可変長整数の往復。**

`encodeDigits` が書いた桁列を `decodeDigits` が読むと元の値が出る。
重み `w` と初期値 `i` は呼び出し側の文脈をそのまま引き継ぐので、
後ろに何が続いていても（`rest`）そこは触らずに返す。

RFC 3492 の可変長整数は最下位桁が先で、`k` 桁目の閾値 `t` 未満の桁が終端である。
符号化は `q` を `t` と `36 - t` で割り、復号は重みを `36 - t` 倍しながら足す。
`Nat.mod_add_div'` がその二つを繋ぐ。
-/
theorem decodeDigits_encodeDigits (bias : Nat) :
    ∀ (q k w i : Nat) (rest : List Char),
      decodeDigits bias (encodeDigits bias k q ++ rest) k w i = some (i + q * w, rest) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ihq =>
    intro k w i rest
    rw [encodeDigits]
    have ht1 := threshold_pos k bias
    have ht2 := threshold_le k bias
    split
    · next hlt =>
      rw [List.cons_append, List.nil_append, decodeDigits]
      simp only [digitValue_digitChar (show q < 36 by omega), hlt, reduceIte]
    · next hge =>
      have hm : 0 < 36 - threshold k bias := by omega
      have hmod : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
        Nat.mod_lt _ hm
      have hd : threshold k bias + (q - threshold k bias) % (36 - threshold k bias) < 36 := by
        omega
      rw [List.cons_append, decodeDigits]
      simp only [digitValue_digitChar hd,
        show ¬ (threshold k bias + (q - threshold k bias) % (36 - threshold k bias)
          < threshold k bias) by omega, reduceIte]
      rw [ihq ((q - threshold k bias) / (36 - threshold k bias)) (by
        calc (q - threshold k bias) / (36 - threshold k bias) ≤ q - threshold k bias :=
              Nat.div_le_self _ _
          _ < q := by omega)]
      have hmd : (q - threshold k bias) % (36 - threshold k bias)
          + (q - threshold k bias) / (36 - threshold k bias) * (36 - threshold k bias)
          = q - threshold k bias := Nat.mod_add_div' _ _
      have key : threshold k bias + (q - threshold k bias) % (36 - threshold k bias)
          + (q - threshold k bias) / (36 - threshold k bias) * (36 - threshold k bias) = q := by
        omega
      have hswap : (q - threshold k bias) / (36 - threshold k bias) * (w * (36 - threshold k bias))
          = (q - threshold k bias) / (36 - threshold k bias) * (36 - threshold k bias) * w := by
        rw [Nat.mul_comm w (36 - threshold k bias), ← Nat.mul_assoc]
      rw [hswap, Nat.add_assoc, ← Nat.add_mul, key]

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



/-!
## 走査 1 回分の道具

`encodeLoop` は非 ASCII の code point `m` を昇順に見て、`m` の出現ごとに差分を吐く。
復号はそれを読んで `m` を挿す。その 1 回分を切り出すための道具を並べる。
-/

/-- `m` 未満の文字の個数。走査が `delta` に足す分である。 -/
def countBelow (m : Nat) (l : List Char) : Nat := (l.filter (fun c => decide (c.toNat < m))).length

theorem scanOne_lt (b m : Nat) (st : EncState) (c : Char) (h : c.toNat < m) :
    scanOne b m st c = { st with delta := st.delta + 1 } := by
  unfold scanOne; rw [if_pos h]

theorem scanOne_gt (b m : Nat) (st : EncState) (c : Char) (h1 : ¬ c.toNat < m)
    (h2 : c.toNat ≠ m) : scanOne b m st c = st := by
  unfold scanOne; rw [if_neg h1, if_neg (by simp [h2])]

theorem scanOne_hit (b m : Nat) (st : EncState) (c : Char) (h1 : ¬ c.toNat < m)
    (h2 : c.toNat = m) :
    scanOne b m st c
      = { out := st.out ++ encodeDigits st.bias 36 st.delta, delta := 0,
          bias := adapt st.delta (st.h + 1) (st.h == b), h := st.h + 1 } := by
  unfold scanOne; rw [if_neg h1, if_pos (by simp [h2])]

/-- **`m` を含まない走査は何も吐かない。** `delta` が `m` 未満の文字の個数だけ増える。 -/
theorem scanFold_no_hit (b m : Nat) : ∀ (l : List Char) (d bi hh : Nat),
    (∀ c ∈ l, c.toNat ≠ m) →
    l.foldl (scanOne b m) { out := [], delta := d, bias := bi, h := hh }
      = { out := [], delta := d + countBelow m l, bias := bi, h := hh } := by
  intro l
  induction l with
  | nil => intro d bi hh _; simp [countBelow]
  | cons c rest ih =>
    intro d bi hh hne
    show rest.foldl (scanOne b m) (scanOne b m { out := [], delta := d, bias := bi, h := hh } c) = _
    have hc : c.toNat ≠ m := hne c List.mem_cons_self
    by_cases hlt : c.toNat < m
    · rw [scanOne_lt b m _ c hlt,
        ih (d + 1) bi hh (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
      simp only [countBelow, List.filter_cons, hlt, decide_true, if_true, List.length_cons]
      congr 1
      omega
    · rw [scanOne_gt b m _ c hlt hc,
        ih d bi hh (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
      simp [countBelow, hlt]

/--
復号の途中の文字列。`input` のうち code point が `m` 未満のものすべてと、
`m` に等しいものの先頭 `j` 個を、元の順に並べたもの。

RFC 3492 の復号は「小さい code point から順に挿していく」ので、
その途中経過がちょうどこれになる。
-/
def partialAt (input : List Char) (m j : Nat) : List Char :=
  match input with
  | [] => []
  | c :: rest =>
    if c.toNat < m then c :: partialAt rest m j
    else if c.toNat == m then
      if j = 0 then partialAt rest m 0 else c :: partialAt rest m (j - 1)
    else partialAt rest m j

/-- `m` 未満だけを残したもの。`j = 0` の場合である。 -/
theorem partialAt_zero (input : List Char) (m : Nat) :
    partialAt input m 0 = input.filter (fun c => decide (c.toNat < m)) := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    rw [partialAt, List.filter_cons]
    split
    · next h => simp [h, ih]
    · split
      · next h => simp_all
      · next h => simp_all

/-!
## 符号化の出力は自由な累積である

`out` は append しかされない。符号化の途中状態から「そこで吐いた分」だけを
切り出せるので、復号との対応を段ごとに切って考えられる。
`delta` / `bias` / `h` は `out` に依らない。
-/

/-- `scanOne` が吐く分。`out` には依らない。 -/
def scanEmit (m : Nat) (d bi : Nat) (c : Char) : List Char :=
  if c.toNat < m then [] else if c.toNat == m then encodeDigits bi 36 d else []

theorem scanOne_eq (b m : Nat) (o : List Char) (d bi h : Nat) (c : Char) :
    scanOne b m { out := o, delta := d, bias := bi, h := h } c
      = { out := o ++ scanEmit m d bi c,
          delta := (scanOne b m { out := [], delta := d, bias := bi, h := h } c).delta,
          bias := (scanOne b m { out := [], delta := d, bias := bi, h := h } c).bias,
          h := (scanOne b m { out := [], delta := d, bias := bi, h := h } c).h } := by
  unfold scanOne scanEmit
  split
  · simp
  · split <;> simp

/-- **`out` は自由な累積である。** 畳み込みの結果は、前に付いていた `out` をそのまま前置する。 -/
theorem scanFold_eq (b m : Nat) : ∀ (l : List Char) (o : List Char) (d bi h : Nat),
    l.foldl (scanOne b m) { out := o, delta := d, bias := bi, h := h }
      = { out := o ++ (l.foldl (scanOne b m) { out := [], delta := d, bias := bi, h := h }).out,
          delta := (l.foldl (scanOne b m) { out := [], delta := d, bias := bi, h := h }).delta,
          bias := (l.foldl (scanOne b m) { out := [], delta := d, bias := bi, h := h }).bias,
          h := (l.foldl (scanOne b m) { out := [], delta := d, bias := bi, h := h }).h } := by
  intro l
  induction l with
  | nil => intro o d bi h; simp
  | cons c rest ih =>
    intro o d bi h
    show rest.foldl (scanOne b m) (scanOne b m { out := o, delta := d, bias := bi, h := h } c) = _
    rw [scanOne_eq b m o d bi h c, ih]
    rw [show (c :: rest).foldl (scanOne b m) { out := [], delta := d, bias := bi, h := h }
          = rest.foldl (scanOne b m)
              (scanOne b m { out := [], delta := d, bias := bi, h := h } c) from rfl]
    rw [scanOne_eq b m [] d bi h c,
      ih ([] ++ scanEmit m d bi c)
        (scanOne b m { out := [], delta := d, bias := bi, h := h } c).delta
        (scanOne b m { out := [], delta := d, bias := bi, h := h } c).bias
        (scanOne b m { out := [], delta := d, bias := bi, h := h } c).h]
    simp

/-- `encodeLoop` でも `out` は自由な累積である。 -/
theorem encodeLoop_eq (input : List Char) (b : Nat) :
    ∀ (todo : List Nat) (n : Nat) (o : List Char) (d bi h : Nat),
      encodeLoop input b todo n { out := o, delta := d, bias := bi, h := h }
        = { out := o ++ (encodeLoop input b todo n
                { out := [], delta := d, bias := bi, h := h }).out,
            delta := (encodeLoop input b todo n
                { out := [], delta := d, bias := bi, h := h }).delta,
            bias := (encodeLoop input b todo n
                { out := [], delta := d, bias := bi, h := h }).bias,
            h := (encodeLoop input b todo n
                { out := [], delta := d, bias := bi, h := h }).h } := by
  intro todo
  induction todo with
  | nil => intro n o d bi h; simp [encodeLoop]
  | cons m rest ih =>
    intro n o d bi h
    simp only [encodeLoop]
    rw [scanFold_eq b m input o (d + (m - n) * (h + 1)) bi h]
    rw [ih (m + 1) (o ++ (input.foldl (scanOne b m)
            { out := [], delta := d + (m - n) * (h + 1), bias := bi, h := h }).out) _ _ _,
        ih (m + 1) ((input.foldl (scanOne b m)
            { out := [], delta := d + (m - n) * (h + 1), bias := bi, h := h }).out) _ _ _]
    simp only [List.append_assoc]


/-!
## 走査 1 回分の双模倣

符号化が `m` の出現ごとに吐く差分を、復号がそのまま挿入に戻すことを言う。

不変条件は `PassInv` にまとめてある。入力を「走査済み」と「これから」に割ると、
復号が持っている文字列は `A ++ B` の形になる。`A` は挿し終わった前半
（`partialAt pre m j`）、`B` はこれから来る `m` 未満（`partialAt suf m 0`）である。
次の挿入位置はちょうど `A.length` で、そこは復号の `i + delta` に一致する。

**`B` を落として考えることはできない。** `m` 未満の文字が来ると挿入位置は進むのに
復号の文字列は伸びないので、「位置が長さを超えない」が単独では成り立たない。
その文字が既に `B` に入っていること（前の pass で挿さっているから）が効いている。
-/

theorem insertIdx_append (A B : List Char) (x : Char) :
    (A ++ B).insertIdx A.length x = (A ++ [x]) ++ B := by
  induction A with
  | nil => simp [List.insertIdx]
  | cons a rest ih =>
    have : ((a :: rest) ++ B).insertIdx (a :: rest).length x
        = a :: (rest ++ B).insertIdx rest.length x := rfl
    rw [this, ih]; simp

theorem encodeDigits_ne_nil (bias k q : Nat) : encodeDigits bias k q ≠ [] := by
  rw [encodeDigits]; split <;> simp

/--
一歩分の吐き出し。差分を読んで `A` の末尾に `m` を挿す。

`n` は復号側がいま見ている code point で、pass の最初の吐き出しではここが `m` まで跳ぶ
（符号化が `(m - n) * (h + 1)` を差分に足しているため）。同じ pass の二回目以降は
`n = m` で、その場合は `(m - n) * N = 0` なので同じ式で表せる。
-/
theorem decode_emit (n m : Nat) (hnm : n ≤ m)
    (hm : m < 0xD800 ∨ (0xDFFF < m ∧ m < 0x110000))
    (A B : List Char) (i d bi : Nat) (E : List Char)
    (hlen : A.length + (m - n) * (A.length + B.length + 1) = i + d) :
    decodeLoop bi n i (A ++ B) (encodeDigits bi 36 d ++ E)
      = decodeLoop (adapt d (A.length + B.length + 1) (i == 0)) m (A.length + 1)
          ((A ++ [Char.ofNat m]) ++ B) E := by
  obtain ⟨c0, t0, he⟩ : ∃ c0 t0, encodeDigits bi 36 d = c0 :: t0 := by
    cases h : encodeDigits bi 36 d with
    | nil => exact absurd h (encodeDigits_ne_nil _ _ _)
    | cons a t => exact ⟨a, t, rfl⟩
  have hdd : decodeDigits bi (c0 :: (t0 ++ E)) 36 1 i = some (i + d, E) := by
    have h := decodeDigits_encodeDigits bi d 36 1 i E
    rw [he] at h
    simpa using h
  rw [he, List.cons_append, decodeLoop]
  split
  · next hd => rw [hdd] at hd; simp at hd
  · next i' rem hd =>
    rw [hdd] at hd
    have hp := Option.some.inj hd
    have h1 : i' = i + d := (congrArg Prod.fst hp).symm
    have h2 : rem = E := (congrArg Prod.snd hp).symm
    subst h1; subst h2
    have hnp : (A ++ B).length + 1 = A.length + B.length + 1 := by simp
    have hN : 0 < A.length + B.length + 1 := by omega
    have hAlt : A.length < A.length + B.length + 1 := by omega
    have hdiv : (i + d) / ((A ++ B).length + 1) = m - n := by
      rw [hnp, ← hlen, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hAlt, Nat.zero_add]
    have hmod : (i + d) % ((A ++ B).length + 1) = A.length := by
      rw [hnp, ← hlen, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hAlt]
    simp only [hdiv, hmod, show n + (m - n) = m by omega]
    have hvalid : (decide (m < 55296) || decide (57343 < m) && decide (m < 1114112)) = true := by
      rcases hm with hv | ⟨hv1, hv2⟩
      · simp [hv]
      · simp [hv1, hv2]
    rw [if_pos hvalid]
    rw [show i + d - i = d by omega, hnp, insertIdx_append]

/--
走査 1 回を追うための状態。

`A` は挿し終わった前半、`B` はまだ来ていない `m` 未満、`n` は復号がいま見ている
code point である。`n` は pass の最初の吐き出しで `m` まで跳び、以降は動かない。
-/
structure PassState where
  A : List Char
  B : List Char
  n : Nat
  i : Nat
  d : Nat
  bias : Nat
  hh : Nat

/-- 走査 1 回で復号側に起きること。 -/
def passRun (b m : Nat) : List Char → PassState → PassState
  | [], st => st
  | c :: rest, st =>
    if c.toNat < m then
      passRun b m rest { st with A := st.A ++ [c], B := st.B.tail, d := st.d + 1 }
    else if c.toNat == m then
      passRun b m rest
        { A := st.A ++ [Char.ofNat m], B := st.B, n := m, i := st.A.length + 1, d := 0,
          bias := adapt st.d (st.A.length + st.B.length + 1) (st.hh == b), hh := st.hh + 1 }
    else passRun b m rest st

/--
不変条件。

`lenA` が要。次の挿入位置 `A.length` に、まだ残っている code point の跳び
`(m - n) * N` を足したものが、復号の `i + delta` に一致する。
最初の吐き出しの後は `n = m` なので跳びが消え、`A.length = i + delta` になる。
-/
structure PassInv (b m : Nat) (suf : List Char) (st : PassState) : Prop where
  bEq : st.B = partialAt suf m 0
  nLe : st.n ≤ m
  lenA : st.A.length + (m - st.n) * (st.A.length + st.B.length + 1) = st.i + st.d
  lenH : st.hh = st.A.length + st.B.length
  firstFlag : (st.hh == b) = (st.i == 0)
  bLe : b ≤ st.hh

/-- **走査 1 回分の双模倣。** -/
theorem decode_scan (b m : Nat) (hm : m < 0xD800 ∨ (0xDFFF < m ∧ m < 0x110000)) :
    ∀ (suf : List Char) (st : PassState) (rest : List Char),
      PassInv b m suf st →
      decodeLoop st.bias st.n st.i (st.A ++ st.B)
          ((suf.foldl (scanOne b m)
              { out := [], delta := st.d, bias := st.bias, h := st.hh }).out ++ rest)
        = decodeLoop (passRun b m suf st).bias (passRun b m suf st).n (passRun b m suf st).i
            ((passRun b m suf st).A ++ (passRun b m suf st).B) rest := by
  intro suf
  induction suf with
  | nil => intro st rest _; simp [passRun]
  | cons c rest' ih =>
    intro st rest hinv
    have hB : st.B = partialAt (c :: rest') m 0 := hinv.bEq
    rw [partialAt] at hB
    by_cases hlt : c.toNat < m
    · -- `m` 未満。位置が一つ進むだけ。
      rw [if_pos hlt] at hB
      show decodeLoop st.bias st.n st.i (st.A ++ st.B)
          ((rest'.foldl (scanOne b m)
            (scanOne b m { out := [], delta := st.d, bias := st.bias, h := st.hh } c)).out
            ++ rest) = _
      rw [scanOne_lt b m _ c hlt]
      rw [passRun, if_pos hlt]
      have hsplit : st.A ++ st.B = (st.A ++ [c]) ++ st.B.tail := by
        rw [hB]; simp
      rw [hsplit]
      refine ih { st with A := st.A ++ [c], B := st.B.tail, d := st.d + 1 } rest ?_
      have hBlen : st.B.length = (partialAt rest' m 0).length + 1 := by rw [hB]; simp
      refine { bEq := by rw [hB]; simp
               nLe := hinv.nLe
               lenA := ?_
               lenH := ?_
               firstFlag := by simpa using hinv.firstFlag
               bLe := by simpa using hinv.bLe }
      · have h := hinv.lenA
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [hB] at h ⊢
        simp at h ⊢
        rw [show st.A.length + 1 + (partialAt rest' m 0).length + 1
              = st.A.length + ((partialAt rest' m 0).length + 1) + 1 by omega]
        omega
      · have h := hinv.lenH
        rw [hB] at h ⊢
        simp at h ⊢
        omega
    · rw [if_neg hlt] at hB
      by_cases heq : c.toNat = m
      · -- `m` に一致。差分を吐いて挿す。
        rw [if_pos (by simp [heq])] at hB
        show decodeLoop st.bias st.n st.i (st.A ++ st.B)
            ((rest'.foldl (scanOne b m)
              (scanOne b m { out := [], delta := st.d, bias := st.bias, h := st.hh } c)).out
              ++ rest) = _
        rw [scanOne_hit b m _ c hlt heq]
        rw [scanFold_eq b m rest' ([] ++ encodeDigits st.bias 36 st.d) 0
              (adapt st.d (st.hh + 1) (st.hh == b)) (st.hh + 1)]
        simp only [List.nil_append, List.append_assoc]
        rw [decode_emit st.n m hinv.nLe hm st.A st.B st.i st.d st.bias _ hinv.lenA]
        rw [passRun, if_neg hlt, if_pos (by simp [heq])]
        rw [← hinv.lenH, hinv.firstFlag]
        exact ih { A := st.A ++ [Char.ofNat m], B := st.B, n := m, i := st.A.length + 1, d := 0,
                   bias := adapt st.d (st.hh + 1) (st.i == 0), hh := st.hh + 1 } rest
          { bEq := hB
            nLe := Nat.le_refl m
            lenA := by simp
            lenH := by have := hinv.lenH; simp; omega
            firstFlag := by
              have := hinv.bLe
              show (st.hh + 1 == b) = (st.A.length + 1 == 0)
              simp
              omega
            bLe := by have := hinv.bLe; show b ≤ st.hh + 1; omega }
      · -- `m` より大きい。何も起きない。
        rw [if_neg (by simp [heq])] at hB
        show decodeLoop st.bias st.n st.i (st.A ++ st.B)
            ((rest'.foldl (scanOne b m)
              (scanOne b m { out := [], delta := st.d, bias := st.bias, h := st.hh } c)).out
              ++ rest) = _
        rw [scanOne_gt b m _ c hlt heq, passRun, if_neg hlt, if_neg (by simp [heq])]
        exact ih st rest { hinv with bEq := hB }

/-- `PassInv` は走査を通して保たれる。使い切ると `B` は空になる。 -/
theorem passRun_inv (b m : Nat) : ∀ (suf : List Char) (st : PassState),
    PassInv b m suf st → PassInv b m [] (passRun b m suf st) := by
  intro suf
  induction suf with
  | nil => intro st h; simpa [passRun] using h
  | cons c rest' ih =>
    intro st hinv
    have hB : st.B = partialAt (c :: rest') m 0 := hinv.bEq
    rw [partialAt] at hB
    by_cases hlt : c.toNat < m
    · rw [if_pos hlt] at hB
      rw [passRun, if_pos hlt]
      exact ih _
        { bEq := by rw [hB]; simp
          nLe := hinv.nLe
          lenA := by
            have h := hinv.lenA
            simp only [List.length_append, List.length_cons, List.length_nil]
            rw [hB] at h ⊢
            simp at h ⊢
            rw [show st.A.length + 1 + (partialAt rest' m 0).length + 1
                  = st.A.length + ((partialAt rest' m 0).length + 1) + 1 by omega]
            omega
          lenH := by
            have := hinv.lenH
            rw [hB] at this ⊢
            simp at this ⊢
            omega
          firstFlag := by simpa using hinv.firstFlag
          bLe := by simpa using hinv.bLe }
    · rw [if_neg hlt] at hB
      by_cases heq : c.toNat = m
      · rw [if_pos (by simp [heq])] at hB
        rw [passRun, if_neg hlt, if_pos (by simp [heq])]
        exact ih _
          { bEq := hB
            nLe := Nat.le_refl m
            lenA := by simp
            lenH := by have := hinv.lenH; simp; omega
            firstFlag := by
              have := hinv.bLe
              show (st.hh + 1 == b) = (st.A.length + 1 == 0)
              simp
              omega
            bLe := by have := hinv.bLe; show b ≤ st.hh + 1; omega }
      · rw [if_neg (by simp [heq])] at hB
        rw [passRun, if_neg hlt, if_neg (by simp [heq])]
        exact ih st { hinv with bEq := hB }

/-- 走査後の符号化状態は `passRun` の状態と一致する（`out` を除く三つ）。 -/
theorem scanFold_passRun (b m : Nat) : ∀ (suf : List Char) (st : PassState) (o : List Char),
    PassInv b m suf st →
    ((suf.foldl (scanOne b m)
        { out := o, delta := st.d, bias := st.bias, h := st.hh }).delta
          = (passRun b m suf st).d
      ∧ (suf.foldl (scanOne b m)
        { out := o, delta := st.d, bias := st.bias, h := st.hh }).bias
          = (passRun b m suf st).bias
      ∧ (suf.foldl (scanOne b m)
        { out := o, delta := st.d, bias := st.bias, h := st.hh }).h
          = (passRun b m suf st).hh) := by
  intro suf
  induction suf with
  | nil => intro st o _; simp [passRun]
  | cons c rest' ih =>
    intro st o hinv
    have hB : st.B = partialAt (c :: rest') m 0 := hinv.bEq
    rw [partialAt] at hB
    by_cases hlt : c.toNat < m
    · rw [if_pos hlt] at hB
      simp only [List.foldl_cons]
      rw [scanOne_lt b m _ c hlt, passRun, if_pos hlt]
      dsimp only
      exact ih { st with A := st.A ++ [c], B := st.B.tail, d := st.d + 1 } o
        { bEq := by rw [hB]; simp
          nLe := hinv.nLe
          lenA := by
            have h := hinv.lenA
            simp only [List.length_append, List.length_cons, List.length_nil]
            rw [hB] at h ⊢
            simp at h ⊢
            rw [show st.A.length + 1 + (partialAt rest' m 0).length + 1
                  = st.A.length + ((partialAt rest' m 0).length + 1) + 1 by omega]
            omega
          lenH := by
            have := hinv.lenH
            rw [hB] at this ⊢
            simp at this ⊢
            omega
          firstFlag := by simpa using hinv.firstFlag
          bLe := by simpa using hinv.bLe }
    · rw [if_neg hlt] at hB
      by_cases heq : c.toNat = m
      · rw [if_pos (by simp [heq])] at hB
        simp only [List.foldl_cons]
        rw [scanOne_hit b m _ c hlt heq, passRun, if_neg hlt, if_pos (by simp [heq])]
        dsimp only
        rw [← hinv.lenH]
        exact ih { A := st.A ++ [Char.ofNat m], B := st.B, n := m, i := st.A.length + 1, d := 0,
                   bias := adapt st.d (st.hh + 1) (st.hh == b), hh := st.hh + 1 } _
          { bEq := hB
            nLe := Nat.le_refl m
            lenA := by simp
            lenH := by have := hinv.lenH; simp; omega
            firstFlag := by
              have := hinv.bLe
              show (st.hh + 1 == b) = (st.A.length + 1 == 0)
              simp
              omega
            bLe := by have := hinv.bLe; show b ≤ st.hh + 1; omega }
      · rw [if_neg (by simp [heq])] at hB
        simp only [List.foldl_cons]
        rw [scanOne_gt b m _ c hlt heq, passRun, if_neg hlt, if_neg (by simp [heq])]
        exact ih st o { hinv with bEq := hB }

/-- `m` が現れれば、走査の後の `n` は `m` になる。 -/
theorem passRun_n (b m : Nat) : ∀ (l : List Char) (st : PassState),
    ((∃ c ∈ l, c.toNat = m) ∨ st.n = m) → (passRun b m l st).n = m := by
  intro l
  induction l with
  | nil =>
    intro st h
    rcases h with ⟨c, hc, _⟩ | h
    · simp at hc
    · simpa [passRun] using h
  | cons c rest ih =>
    intro st h
    rw [passRun]
    by_cases hlt : c.toNat < m
    · rw [if_pos hlt]
      refine ih _ ?_
      rcases h with ⟨x, hx, hxm⟩ | hn
      · rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact Or.inl ⟨x, hx, hxm⟩
      · exact Or.inr hn
    · rw [if_neg hlt]
      by_cases heq : c.toNat = m
      · rw [if_pos (by simp [heq])]
        exact ih _ (Or.inr rfl)
      · rw [if_neg (by simp [heq])]
        refine ih _ ?_
        rcases h with ⟨x, hx, hxm⟩ | hn
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd hxm heq
          · exact Or.inl ⟨x, hx, hxm⟩
        · exact Or.inr hn

/-- 走査の後の前半は、`m` 以下の文字を元の順に並べたものである。 -/
theorem passRun_A (b m : Nat) : ∀ (l : List Char) (st : PassState),
    st.B = partialAt l m 0 →
    (passRun b m l st).A = st.A ++ l.filter (fun c => decide (c.toNat ≤ m)) := by
  intro l
  induction l with
  | nil => intro st _; simp [passRun]
  | cons c rest ih =>
    intro st hB
    rw [partialAt] at hB
    rw [passRun]
    by_cases hlt : c.toNat < m
    · rw [if_pos hlt] at hB
      rw [if_pos hlt, ih _ (by rw [hB]; simp)]
      simp [show c.toNat ≤ m by omega]
    · rw [if_neg hlt] at hB
      rw [if_neg hlt]
      by_cases heq : c.toNat = m
      · rw [if_pos (by simp [heq])] at hB
        rw [if_pos (by simp [heq]),
          ih { A := st.A ++ [Char.ofNat m], B := st.B, n := m, i := st.A.length + 1, d := 0,
               bias := adapt st.d (st.A.length + st.B.length + 1) (st.hh == b),
               hh := st.hh + 1 } hB]
        have hco : Char.ofNat m = c := by rw [← heq, Char.ofNat_toNat]
        simp [show c.toNat ≤ m by omega, hco]
      · rw [if_neg (by simp [heq])] at hB
        rw [if_neg (by simp [heq]), ih st hB]
        simp [show ¬ (c.toNat ≤ m) by omega]

/-!
## 外側のループ

`encodeLoop` は `sortedDistinct` の順に code point を上げていく。
pass の境目で何が保たれるかが要点で、それは次の一本である。

```
i + st.delta = (nEnc - nDec) * (out.length + 1)
```

`nEnc` は `encodeLoop` の引数（前の code point + 1、最初は 128）、
`nDec` は復号がいま見ている code point（前の code point、最初は 128）である。
最初の pass では両者が等しく右辺は 0、二回目以降は 1 ずれるので右辺は `out.length + 1` になる。

後者が成り立つ理由はこうである。前の pass の最後の挿入位置を `pos`、
その後ろに残る「前の code point 未満」の文字数を `k` とすると、
復号の `i` は `pos + 1`、符号化の `delta` は `k + 1`（pass の終わりに 1 足すため）で、
`out.length = pos + 1 + k` だから両辺が一致する。

この一本があると、pass の最初の吐き出しで `decode_emit` の前提

```
A.length + (m - nDec) * N = i + d
```

がちょうど出る。`d` は pass の頭で `(m - nEnc) * N` を足され、
`m` が来るまでに `m` 未満の文字の個数だけ増えるので、
`i + d = (nEnc - nDec) * N + (m - nEnc) * N + A.length = A.length + (m - nDec) * N` となる。
-/

/-- `m` が現れるなら、最初の出現で入力を割れる。 -/
theorem split_first_hit (m : Nat) : ∀ (l : List Char), (∃ c ∈ l, c.toNat = m) →
    ∃ pre c suf, l = pre ++ c :: suf ∧ (∀ x ∈ pre, x.toNat ≠ m) ∧ c.toNat = m := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro h
    by_cases ha : a.toNat = m
    · exact ⟨[], a, rest, by simp, by simp, ha⟩
    · obtain ⟨c, hc, hcm⟩ := h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact absurd hcm ha
      · obtain ⟨pre, c', suf, hl, hpre, hc'⟩ := ih ⟨c, hc, hcm⟩
        exact ⟨a :: pre, c', suf, by rw [hl]; simp,
          by intro x hx; rcases List.mem_cons.mp hx with rfl | hx
             · exact ha
             · exact hpre x hx, hc'⟩

/-- 狭義単調増加。core に `List.Chain'` が無いので自前で置く。 -/
def StrictSorted : List Nat → Prop
  | [] => True
  | m :: rest => (∀ x ∈ rest, m < x) ∧ StrictSorted rest

/-- 外側のループの不変条件。 -/
structure OuterInv (b : Nat) (input : List Char) (todo : List Nat)
    (nEnc nDec dlt h i : Nat) : Prop where
  /-- `nEnc` 以上の code point はすべて `todo` にある。 -/
  covers : ∀ c ∈ input, nEnc ≤ c.toNat → c.toNat ∈ todo
  /-- `todo` の code point はすべて input に現れる。 -/
  occurs : ∀ m ∈ todo, ∃ c ∈ input, c.toNat = m
  /-- `todo` は `nEnc` 以上で、狭義単調増加。 -/
  ge : ∀ m ∈ todo, nEnc ≤ m
  sorted : StrictSorted todo
  /-- `todo` の code point は妥当な scalar value。 -/
  valid : ∀ m ∈ todo, m < 0xD800 ∨ (0xDFFF < m ∧ m < 0x110000)
  hEq : h = (input.filter (fun c => decide (c.toNat < nEnc))).length
  /-- pass の境目で保たれるもの。 -/
  delta : i + dlt = (nEnc - nDec) * (h + 1)
  nLe : nDec ≤ nEnc
  firstFlag : (h == b) = (i == 0)
  bLe : b ≤ h

/-- `nEnc` 以上 `m` 未満の code point が無ければ、二つの filter は一致する。 -/
theorem filter_lt_eq (input : List Char) (nEnc m : Nat) (hnm : nEnc ≤ m)
    (h : ∀ c ∈ input, nEnc ≤ c.toNat → m ≤ c.toNat) :
    input.filter (fun c => decide (c.toNat < nEnc))
      = input.filter (fun c => decide (c.toNat < m)) := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc := h c List.mem_cons_self
    rw [List.filter_cons, List.filter_cons, hrest]
    by_cases h1 : c.toNat < nEnc
    · have h2 : c.toNat < m := by omega
      simp [h1, h2]
    · have h2 : ¬ c.toNat < m := by
        have := hc (by omega); omega
      simp [h1, h2]

/-- **外側のループの双模倣。** `todo` を使い切ると復号は入力そのものを返す。 -/
theorem decode_outer (b : Nat) :
    ∀ (todo : List Nat) (input : List Char) (nEnc nDec dlt bias h i : Nat),
      OuterInv b input todo nEnc nDec dlt h i →
      decodeLoop bias nDec i (input.filter (fun c => decide (c.toNat < nEnc)))
          ((encodeLoop input b todo nEnc
              { out := [], delta := dlt, bias := bias, h := h }).out)
        = some input := by
  intro todo
  induction todo with
  | nil =>
    intro input nEnc nDec dlt bias h i hinv
    rw [encodeLoop]
    have : input.filter (fun c => decide (c.toNat < nEnc)) = input := by
      refine List.filter_eq_self.mpr ?_
      intro c hc
      simp only [decide_eq_true_eq]
      rcases Nat.lt_or_ge c.toNat nEnc with hlt | hge
      · exact hlt
      · exact absurd (hinv.covers c hc hge) (by simp)
    rw [this]
    simp [decodeLoop]
  | cons m rest ih =>
    intro input nEnc nDec dlt bias h i hinv
    -- `nEnc` 以上の code point は `m` 以上しかないので、復号が持っている文字列は
    -- `m` 未満の filter でもある。
    have hnm : nEnc ≤ m := hinv.ge m List.mem_cons_self
    have hgeM : ∀ c ∈ input, nEnc ≤ c.toNat → m ≤ c.toNat := by
      intro c hc hge
      rcases List.mem_cons.mp (hinv.covers c hc hge) with h1 | h1
      · omega
      · exact Nat.le_of_lt (hinv.sorted.1 _ h1)
    have hfil : input.filter (fun c => decide (c.toNat < nEnc))
        = input.filter (fun c => decide (c.toNat < m)) := filter_lt_eq input nEnc m hnm hgeM
    -- pass の状態
    have hB : (input.filter (fun c => decide (c.toNat < m))) = partialAt input m 0 :=
      (partialAt_zero input m).symm
    have hhB : h = (partialAt input m 0).length := by rw [hinv.hEq, hfil, hB]
    -- pass の入口の状態
    have hinvP : PassInv b m input
        { A := [], B := partialAt input m 0, n := nDec, i := i,
          d := dlt + (m - nEnc) * (h + 1), bias := bias, hh := h } := by
      have hnDec := hinv.nLe
      refine { bEq := rfl, nLe := show nDec ≤ m by omega, lenA := ?_, lenH := ?_,
               firstFlag := hinv.firstFlag, bLe := hinv.bLe }
      · show (0 : Nat) + (m - nDec) * (0 + (partialAt input m 0).length + 1)
          = i + (dlt + (m - nEnc) * (h + 1))
        rw [← hhB, show m - nDec = (nEnc - nDec) + (m - nEnc) by omega, Nat.add_mul,
          Nat.zero_add, Nat.zero_add, ← hinv.delta]
        omega
      · show h = 0 + (partialAt input m 0).length
        omega
    -- pass の出口
    have hinvQ := passRun_inv b m input _ hinvP
    have hQn : (passRun b m input
        { A := [], B := partialAt input m 0, n := nDec, i := i,
          d := dlt + (m - nEnc) * (h + 1), bias := bias, hh := h }).n = m := by
      refine passRun_n b m input _ (Or.inl ?_)
      obtain ⟨c, hc, hcm⟩ := hinv.occurs m List.mem_cons_self
      exact ⟨c, hc, hcm⟩
    have hQA : (passRun b m input
        { A := [], B := partialAt input m 0, n := nDec, i := i,
          d := dlt + (m - nEnc) * (h + 1), bias := bias, hh := h }).A
        = input.filter (fun c => decide (c.toNat ≤ m)) := by
      rw [passRun_A b m input _ rfl]; simp
    have hQB : (passRun b m input
        { A := [], B := partialAt input m 0, n := nDec, i := i,
          d := dlt + (m - nEnc) * (h + 1), bias := bias, hh := h }).B = [] := by
      have := hinvQ.bEq; simpa [partialAt] using this
    have hfilM : input.filter (fun c => decide (c.toNat ≤ m))
        = input.filter (fun c => decide (c.toNat < m + 1)) := by
      refine List.filter_congr ?_
      intro c _
      simp [Nat.lt_succ_iff]
    -- 符号化の一段を開く
    rw [encodeLoop]
    rw [encodeLoop_eq input b rest (m + 1)
      (input.foldl (scanOne b m)
        { out := [], delta := dlt + (m - nEnc) * (h + 1), bias := bias, h := h }).out
      ((input.foldl (scanOne b m)
        { out := [], delta := dlt + (m - nEnc) * (h + 1), bias := bias, h := h }).delta + 1)
      (input.foldl (scanOne b m)
        { out := [], delta := dlt + (m - nEnc) * (h + 1), bias := bias, h := h }).bias
      (input.foldl (scanOne b m)
        { out := [], delta := dlt + (m - nEnc) * (h + 1), bias := bias, h := h }).h]
    -- 復号側を pass の形に合わせる
    rw [show input.filter (fun c => decide (c.toNat < nEnc))
        = ([] : List Char) ++ partialAt input m 0 by rw [hfil, hB]; simp]
    rw [decode_scan b m (hinv.valid m List.mem_cons_self) input _ _ hinvP]
    -- 符号化の状態と復号の状態が一致する
    obtain ⟨hd, hbi, hhh⟩ := scanFold_passRun b m input _ [] hinvP
    rw [hd, hbi, hhh, hQn, hQA, hQB]
    simp only [List.append_nil]
    rw [hfilM]
    refine ih input (m + 1) m _ _ _ _ ?_
    have hQlenA := hinvQ.lenA
    have hQlenH := hinvQ.lenH
    rw [hQn, hQA, hQB] at hQlenA
    rw [hQA, hQB] at hQlenH
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, List.length_nil] at hQlenA hQlenH
    exact
      { covers := by
          intro c hc hge
          rcases List.mem_cons.mp (hinv.covers c hc (by omega)) with h1 | h1
          · omega
          · exact h1
        occurs := fun x hx => hinv.occurs x (List.mem_cons_of_mem _ hx)
        ge := fun x hx => hinv.sorted.1 x hx
        sorted := hinv.sorted.2
        valid := fun x hx => hinv.valid x (List.mem_cons_of_mem _ hx)
        hEq := by rw [← hfilM]; exact hQlenH
        delta := by
          rw [show m + 1 - m = 1 by omega, Nat.one_mul]
          omega
        nLe := by omega
        firstFlag := hinvQ.firstFlag
        bLe := hinvQ.bLe }

/-! ## 符号化の枠が復号で戻ること -/

theorem span_loop_all (p : Char → Bool) : ∀ (l acc : List Char), (∀ c ∈ l, p c = true) →
    List.span.loop p l acc = (acc.reverse ++ l, []) := by
  intro l
  induction l with
  | nil => intro acc _; simp [List.span.loop]
  | cons c rest ih =>
    intro acc h
    rw [List.span.loop, h c List.mem_cons_self]
    rw [ih (c :: acc) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

theorem span_loop_split (p : Char → Bool) : ∀ (l : List Char) (x : Char) (r acc : List Char),
    (∀ c ∈ l, p c = true) → p x = false →
    List.span.loop p (l ++ x :: r) acc = (acc.reverse ++ l, x :: r) := by
  intro l
  induction l with
  | nil =>
    intro x r acc _ hx
    simp only [List.nil_append]
    rw [List.span.loop, hx]
    simp
  | cons c rest ih =>
    intro x r acc h hx
    simp only [List.cons_append]
    rw [List.span.loop, h c List.mem_cons_self]
    rw [ih x r (c :: acc) (fun y hy => h y (List.mem_cons_of_mem _ hy)) hx]
    simp

/-- 区切りが無ければ、全部が拡張部分である。 -/
theorem splitLastDelim_no_delim (ext : List Char) (h : ∀ c ∈ ext, c ≠ '-') :
    splitLastDelim ext = ([], ext) := by
  unfold splitLastDelim
  rw [List.span, span_loop_all _ ext.reverse []
    (fun c hc => by simp [h c (List.mem_reverse.mp hc)])]
  simp

/-- 区切りがあれば、最後の区切りの前後に分かれる。 -/
theorem splitLastDelim_append (basic ext : List Char) (h : ∀ c ∈ ext, c ≠ '-') :
    splitLastDelim (basic ++ '-' :: ext) = (basic, ext) := by
  unfold splitLastDelim
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [List.span, span_loop_split _ ext.reverse '-' basic.reverse []
    (fun c hc => by simp [h c (List.mem_reverse.mp hc)]) (by simp)]
  simp

/-- 桁文字は `a`-`z` と `0`-`9` なので、区切りの `-` にはならない。 -/
theorem digitChar_ne_delim {d : Nat} (h : d < 36) : digitChar d ≠ '-' := by
  unfold digitChar
  split
  · next hd =>
    intro heq
    have hx : (Char.ofNat (0x61 + d)).toNat = 0x2D := by rw [heq]; rfl
    rw [toNat_ofNat_ascii (by omega)] at hx
    omega
  · next hd =>
    intro heq
    have hx : (Char.ofNat (0x30 + d - 26)).toNat = 0x2D := by rw [heq]; rfl
    rw [toNat_ofNat_ascii (by omega)] at hx
    omega

theorem encodeDigits_no_delim (bias : Nat) : ∀ (k q : Nat) (c : Char),
    c ∈ encodeDigits bias k q → c ≠ '-'
  | k, q, c, hc => by
    rw [encodeDigits] at hc
    have h1 := threshold_pos k bias
    have h2 := threshold_le k bias
    split at hc
    · next hq =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; exact digitChar_ne_delim (by omega)
    · next hq =>
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc
        refine digitChar_ne_delim ?_
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      · exact encodeDigits_no_delim bias (k + 36) _ c hc
termination_by _ q => q
decreasing_by
  have _h1 := threshold_pos k bias
  have _h2 := threshold_le k bias
  calc (q - threshold k bias) / (36 - threshold k bias)
      ≤ q - threshold k bias := Nat.div_le_self _ _
    _ < q := by omega

theorem scanOne_no_delim (b m : Nat) (st : EncState) (c : Char)
    (h : ∀ x ∈ st.out, x ≠ '-') : ∀ x ∈ (scanOne b m st c).out, x ≠ '-' := by
  unfold scanOne
  split
  · exact h
  · split
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · exact encodeDigits_no_delim st.bias 36 st.delta x hx
    · exact h

theorem scanFold_no_delim (b m : Nat) : ∀ (l : List Char) (st : EncState),
    (∀ x ∈ st.out, x ≠ '-') → ∀ x ∈ (l.foldl (scanOne b m) st).out, x ≠ '-'
  | [], _, h => h
  | c :: rest, st, h =>
    scanFold_no_delim b m rest (scanOne b m st c) (scanOne_no_delim b m st c h)

theorem encodeLoop_no_delim (input : List Char) (b : Nat) : ∀ (todo : List Nat) (n : Nat)
    (st : EncState), (∀ x ∈ st.out, x ≠ '-') →
    ∀ x ∈ (encodeLoop input b todo n st).out, x ≠ '-'
  | [], _, _, h => h
  | m :: rest, n, st, h => by
    rw [encodeLoop]
    exact encodeLoop_no_delim input b rest (m + 1) _ (scanFold_no_delim b m input _ h)

/-- **拡張部分に区切りの `-` は現れない。** -/
theorem encodeExt_no_delim (input : List Char) : ∀ c ∈ encodeExt input, c ≠ '-' :=
  encodeLoop_no_delim input _ _ _ _ (by simp)

/--
**符号化の枠は復号で正確に戻る。**

`decode` はまず最後の `-` で基本部分と拡張部分に分ける。拡張部分には `-` が無いので、
分け方は一意である（基本部分に `-` が何個あっても構わない）。
-/
theorem splitLastDelim_encode (input : List Char) :
    splitLastDelim (encode input) = (encodeBasic input, encodeExt input) := by
  unfold encode
  by_cases h : (encodeBasic input).isEmpty
  · rw [if_pos h]
    have : encodeBasic input = [] := List.isEmpty_iff.mp h
    rw [this]
    simpa using splitLastDelim_no_delim (encodeExt input) (encodeExt_no_delim input)
  · rw [if_neg h]
    have : encodeBasic input ++ ['-'] ++ encodeExt input
        = encodeBasic input ++ '-' :: encodeExt input := by
      rw [List.append_assoc, List.singleton_append]
    rw [this]
    exact splitLastDelim_append _ _ (encodeExt_no_delim input)


/-!
## 往復

`sortedDistinct` が「入力の非 ASCII code point をちょうど覆う」ことを言えば、
外側のループの不変条件が入口で成り立ち、往復が出る。
-/

theorem mem_insertSorted (x : Nat) : ∀ (l : List Nat) (y : Nat),
    y ∈ insertSorted x l ↔ (y = x ∨ y ∈ l) := by
  intro l
  induction l with
  | nil => intro y; simp [insertSorted]
  | cons a t ih =>
    intro y
    rw [insertSorted]
    split
    · simp
    · split
      · next h =>
        have : x = a := by simpa using h
        subst this
        simp
      · rw [List.mem_cons, ih y, List.mem_cons]
        constructor
        · rintro (rfl | rfl | hy) <;> simp_all
        · rintro (rfl | rfl | hy) <;> simp_all

theorem mem_sortedDistinct : ∀ (l : List Nat) (y : Nat),
    y ∈ sortedDistinct l ↔ y ∈ l := by
  intro l
  induction l with
  | nil => intro y; simp [sortedDistinct]
  | cons a t ih =>
    intro y
    rw [sortedDistinct, mem_insertSorted, ih, List.mem_cons]

theorem strictSorted_insertSorted (x : Nat) : ∀ (l : List Nat),
    StrictSorted l → StrictSorted (insertSorted x l) := by
  intro l
  induction l with
  | nil => intro _; simp [insertSorted, StrictSorted]
  | cons a t ih =>
    intro hs
    rw [insertSorted]
    split
    · next h =>
      refine ⟨?_, hs⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h
      · exact Nat.lt_trans h (hs.1 z hz)
    · split
      · exact hs
      · next h1 h2 =>
        refine ⟨?_, ih hs.2⟩
        intro z hz
        have hax : a < x := by simp at h2; omega
        rcases (mem_insertSorted x t z).mp hz with rfl | hz
        · exact hax
        · exact hs.1 z hz

theorem strictSorted_sortedDistinct : ∀ (l : List Nat), StrictSorted (sortedDistinct l) := by
  intro l
  induction l with
  | nil => simp [sortedDistinct, StrictSorted]
  | cons a t ih => rw [sortedDistinct]; exact strictSorted_insertSorted a _ ih

/-- `Char` の番号は妥当な scalar value である。 -/
theorem char_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  exact c.valid

/-- **Punycode の往復。** 符号化して復号すると元に戻る。 -/
theorem decode_encode (input : List Char) : decode (encode input) = some input := by
  unfold decode
  rw [splitLastDelim_encode]
  have hbasic : (encodeBasic input).any (fun c => decide (0x80 ≤ c.toNat)) = false := by
    simp only [List.any_eq_false, encodeBasic]
    intro c hc
    have := (List.mem_filter.mp hc).2
    simp at this ⊢
    omega
  simp only [hbasic, Bool.false_eq_true, if_false]
  unfold encodeExt
  refine decode_outer (encodeBasic input).length _ input 128 128 0 72 _ 0 ?_
  refine { covers := ?_, occurs := ?_, ge := ?_, sorted := ?_, valid := ?_,
           hEq := rfl, delta := by simp, nLe := Nat.le_refl _,
           firstFlag := by simp, bLe := Nat.le_refl _ }
  · intro c hc hge
    refine (mem_sortedDistinct _ _).mpr ?_
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hge⟩, rfl⟩
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := List.mem_map.mp ((mem_sortedDistinct _ _).mp hx)
    exact ⟨c, (List.mem_filter.mp hc).1, hcx⟩
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := List.mem_map.mp ((mem_sortedDistinct _ _).mp hx)
    have := (List.mem_filter.mp hc).2
    simp at this
    omega
  · exact strictSorted_sortedDistinct _
  · intro x hx
    obtain ⟨c, _, hcx⟩ := List.mem_map.mp ((mem_sortedDistinct _ _).mp hx)
    rw [← hcx]
    exact char_valid c
end Url.Punycode
