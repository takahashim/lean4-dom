import Url.Roundtrip

/-!
# IPv4 の往復

URL Standard §3.5 の IPv4 serializer で書いたものを §3.3 の IPv4 parser で読むと
元の数に戻る（`ipv4Parser_serializer`）。

## 段取り

* **10 進の往復**。`parseRadix 10` は `portValue` と同じ畳み込みで、
  `portValue_toString`（`Url/Roundtrip.lean`）がその往復を言う。
* **先頭の `0`**。`ipv4NumberParser` は `0` で始まる part を 8 進（`0x` なら 16 進）と読む。
  `toString` は先頭に `0` を置かないので、その枝には入らない。
* **`.` での分割**。`strictSplit` は accumulator で書かれているので、
  その形の補題（`strictSplit_go_append`）を二つ用意して四つの part に割る。
* **組み立て**。part は四つ、どれも 256 未満なので、
  `256 進で 4 桁` の値が元の数に戻る。`addr < 2^32` が要る。

host parser はこの上に `percentDecodeToString` と domain parser を挟むので、
`canonicalUrl` の host の条件（IPv4 の分）にはまだ足りない。
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-- 10 進では `radixDigit` と `digitValue` は同じものである。 -/
theorem radixDigit_ten (c : Char) : radixDigit 10 c = digitValue c := by
  unfold radixDigit hexValue digitValue
  by_cases h1 : (decide (0x30 ≤ c.toNat) && decide (c.toNat ≤ 0x39)) = true
  · rw [if_pos h1, if_pos h1]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    show (if c.toNat - 0x30 < 10 then some (c.toNat - 0x30) else none) = some (c.toNat - 0x30)
    rw [if_pos (by omega)]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (decide (0x41 ≤ c.toNat) && decide (c.toNat ≤ 0x46)) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      show (if c.toNat - 0x41 + 10 < 10 then some (c.toNat - 0x41 + 10) else none) = none
      rw [if_neg (by omega)]
    · rw [if_neg h2]
      by_cases h3 : (decide (0x61 ≤ c.toNat) && decide (c.toNat ≤ 0x66)) = true
      · rw [if_pos h3]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
        show (if c.toNat - 0x61 + 10 < 10 then some (c.toNat - 0x61 + 10) else none) = none
        rw [if_neg (by omega)]
      · rw [if_neg h3]

/--
数字だけの列は 10 進として読める。値は `portValue` と同じである。

畳み込む関数を引数にしてあるのは、`parseRadix` の `match` を書き写すと
別の matcher ができてしまい、`rw` の対象に合わないためである。
-/
theorem foldOpt_digits {f : Option Nat → Char → Option Nat}
    (hf : ∀ (a : Nat) (c : Char) (v : Nat), digitValue c = some v → f (some a) c = some (a * 10 + v)) :
    ∀ (l : List Char) (a : Nat), (∀ c ∈ l, isAsciiDigit c = true) →
      l.foldl f (some a) = some (l.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) a) := by
  intro l
  induction l with
  | nil => intro a _; rfl
  | cons c t ih =>
    intro a h
    have hd : digitValue c = some (c.toNat - 0x30) := by
      have h2 := h c (by simp)
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at h2
      simp only [digitValue]
      rw [if_pos (by simp [h2.1, h2.2])]
    simp only [List.foldl_cons, hf a c _ hd, hd, Option.getD_some]
    exact ih (a * 10 + (c.toNat - 0x30)) (fun x hx => h x (by simp [hx]))

/-- 数字だけの空でない列を 10 進で読むと `portValue` の値になる。 -/
theorem parseRadix_ten {l : List Char} (hne : ¬l = []) (h : ∀ c ∈ l, isAsciiDigit c = true) :
    parseRadix 10 l = some (portValue l) := by
  unfold parseRadix portValue
  cases l with
  | nil => exact absurd rfl hne
  | cons c t =>
    exact foldOpt_digits (fun a x v hv => by simp [radixDigit_ten, hv]) (c :: t) 0 h

/-- `digitChar` は 0 以外では `'0'` を返さない。 -/
theorem digitChar_ne_zero : ∀ (d : Nat), 0 < d → d < 10 → ¬Nat.digitChar d = '0'
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ | 8, _, _ | 9, _, _ =>
    by decide
  | 0, h, _ => absurd h (by omega)
  | _ + 10, _, h => absurd h (by omega)

/-- 10 進の表記は先頭に `0` を置かない。 -/
theorem toDigitsCore_head : ∀ (fuel n : Nat) (ds : List Char), 0 < n → n < fuel →
    ∃ c t, Nat.toDigitsCore 10 fuel n ds = c :: t ∧ ¬c = '0' := by
  intro fuel
  induction fuel with
  | zero => intro n ds h1 h2; omega
  | succ f ih =>
    intro n ds h1 h2
    rw [Nat.toDigitsCore]
    split
    · next hz =>
      refine ⟨Nat.digitChar (n % 10), ds, rfl, ?_⟩
      have : n % 10 = n := by omega
      rw [this]
      exact digitChar_ne_zero n h1 (by omega)
    · next hz => exact ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega) (by omega)

/-- `toString` も同じである。 -/
theorem toString_head_ne_zero {n : Nat} (h : 0 < n) :
    ∃ c t, (toString n).toList = c :: t ∧ ¬c = '0' := by
  show ∃ c t, (Nat.repr n).toList = c :: t ∧ ¬c = '0'
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList]
  exact toDigitsCore_head (n + 1) n [] h (by omega)

/-- **10 進で書いた数は IPv4 number parser で読み直せる。** -/
theorem ipv4NumberParser_toString (n : Nat) :
    ipv4NumberParser (toString n).toList = some (n, false) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · decide
  · obtain ⟨c, t, hs, hc⟩ := toString_head_ne_zero hpos
    have hdig : ∀ x ∈ (toString n).toList, isAsciiDigit x = true := toString_digits n
    unfold ipv4NumberParser
    rw [hs]
    split
    · next he => simp at he
    · split
      rename_i rest radix ve h
      split at h
      · next h1 => simp only [List.cons.injEq] at h1; exact absurd h1.1 hc
      · next h1 => simp only [List.cons.injEq] at h1; exact absurd h1.1 hc
      · next h1 => simp only [List.cons.injEq] at h1; exact absurd h1.1 hc
      · simp only [Prod.mk.injEq] at h
        obtain ⟨hr, hrad, hve⟩ := h
        subst hr
        subst hrad
        subst hve
        rw [if_neg (by simp)]
        rw [parseRadix_ten (by simp) (by rw [← hs]; exact hdig)]
        rw [← hs, portValue_toString]

/-- 区切りを含まない列は、そのまま一つの断片になる。 -/
theorem strictSplit_go_nodot (sep : Char) : ∀ (l acc : List Char), (∀ c ∈ l, ¬c = sep) →
    strictSplit.go sep l acc = [acc.reverse ++ l] := by
  intro l
  induction l with
  | nil => intro acc _; simp [strictSplit.go]
  | cons c t ih =>
    intro acc h
    rw [strictSplit.go, if_neg (by simp [h c (by simp)])]
    rw [ih (c :: acc) (fun x hx => h x (by simp [hx]))]
    simp

/-- 区切りの手前までが一つの断片になり、その後ろは続きである。 -/
theorem strictSplit_go_append (sep : Char) : ∀ (l rest acc : List Char), (∀ c ∈ l, ¬c = sep) →
    strictSplit.go sep (l ++ sep :: rest) acc
      = (acc.reverse ++ l) :: strictSplit.go sep rest [] := by
  intro l
  induction l with
  | nil =>
    intro rest acc _
    rw [List.nil_append, strictSplit.go, if_pos (by simp)]
    simp
  | cons c t ih =>
    intro rest acc h
    rw [List.cons_append, strictSplit.go, if_neg (by simp [h c (by simp)])]
    rw [ih rest (c :: acc) (fun x hx => h x (by simp [hx]))]
    simp

/-- 10 進の表記に `.` は無い。 -/
theorem toString_no_dot (n : Nat) : ∀ c ∈ (toString n).toList, ¬c = '.' := by
  intro c hc he
  have := toString_digits n c hc
  rw [he] at this
  revert this
  decide

/-- IPv4 を serialize した文字列は、`.` で四つに分かれる。 -/
theorem ipv4Parts_serializer (addr : Nat) :
    ipv4Parts (ipv4Serializer addr).toList
      = [(toString (addr / 16777216 % 256)).toList, (toString (addr / 65536 % 256)).toList,
         (toString (addr / 256 % 256)).toList, (toString (addr % 256)).toList] := by
  have hs : (ipv4Serializer addr).toList
      = (toString (addr / 16777216 % 256)).toList ++ '.' ::
        ((toString (addr / 65536 % 256)).toList ++ '.' ::
          ((toString (addr / 256 % 256)).toList ++ '.' :: (toString (addr % 256)).toList)) := by
    rw [show ipv4Serializer addr
        = toString (addr / 16777216 % 256) ++ "." ++ toString (addr / 65536 % 256) ++ "."
          ++ toString (addr / 256 % 256) ++ "." ++ toString (addr % 256) from rfl]
    simp only [String.toList_append]
    rw [show ("." : String).toList = ['.'] from rfl]
    simp
  unfold ipv4Parts strictSplit
  rw [hs]
  rw [strictSplit_go_append '.' _ _ [] (toString_no_dot _)]
  rw [strictSplit_go_append '.' _ _ [] (toString_no_dot _)]
  rw [strictSplit_go_append '.' _ _ [] (toString_no_dot _)]
  rw [strictSplit_go_nodot '.' _ [] (toString_no_dot _)]
  simp only [List.reverse_nil, List.nil_append]
  simp

/-- **IPv4 アドレスは serialize して parse し直すと元に戻る。**（§3.5 → §3.3） -/
theorem ipv4Parser_serializer {addr : Nat} (h : addr < 4294967296) :
    ipv4Parser (ipv4Serializer addr).toList = some addr := by
  have hnum : ∀ n : Nat, ipv4NumberParser (Nat.toDigits 10 n) = some (n, false) := by
    intro n
    have := ipv4NumberParser_toString n
    simpa using this
  have hmap : (ipv4Parts (ipv4Serializer addr).toList).mapM
      (fun p => (ipv4NumberParser p).map Prod.fst)
      = some [addr / 16777216 % 256, addr / 65536 % 256, addr / 256 % 256, addr % 256] := by
    rw [ipv4Parts_serializer addr]
    simp [hnum]
  have hdl : ([addr / 16777216 % 256, addr / 65536 % 256, addr / 256 % 256,
      addr % 256] : List Nat).dropLast
      = [addr / 16777216 % 256, addr / 65536 % 256, addr / 256 % 256] := rfl
  have hgl : ([addr / 16777216 % 256, addr / 65536 % 256, addr / 256 % 256,
      addr % 256] : List Nat).getLast? = some (addr % 256) := rfl
  have hany : (([addr / 16777216 % 256, addr / 65536 % 256,
      addr / 256 % 256] : List Nat).any fun n => decide (255 < n)) = false := by
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not, Nat.not_lt]
    omega
  unfold ipv4Parser
  rw [hmap]
  dsimp only
  rw [hdl, hgl, hany]
  simp only [List.length_cons, List.length_nil, List.isEmpty_cons, Bool.or_false,
    Bool.false_eq_true, if_false, Nat.reduceAdd, gt_iff_lt, Nat.lt_irrefl, decide_false,
    Nat.reduceSub, Nat.pow_one, List.foldl_cons, List.foldl_nil, ge_iff_le]
  rw [if_neg (show ¬(256 ≤ addr % 256) from by omega)]
  simp only [Option.some.injEq]
  omega

/-- 仮定が空でないことの確認。`1.2.3.4` は実際にこの形である。 -/
example : ipv4Parser (ipv4Serializer 16909060).toList = some 16909060 :=
  ipv4Parser_serializer (by omega)

/-- 境界。`255.255.255.255` も戻る。 -/
example : ipv4Parser (ipv4Serializer 4294967295).toList = some 4294967295 :=
  ipv4Parser_serializer (by omega)

/-- `0.0.0.0` も戻る。part が `0` のときだけ 10 進の枝が違う。 -/
example : ipv4Parser (ipv4Serializer 0).toList = some 0 :=
  ipv4Parser_serializer (by omega)

end Url
