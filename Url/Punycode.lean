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

end Url.Punycode
