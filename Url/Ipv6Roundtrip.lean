import Url.Ipv6

/-!
# IPv6 の往復

§3.5 IPv6 serializer で書いたものを §3.3 IPv6 parser で読むと元に戻ること。
いまあるのは**圧縮しない場合**（`ipv6CompressIndex` が `none` を返す address）である。

## 段取り

* **16 進の往復**（`hexValueOf_toHexString`）。`takeHex` の畳み込みと同じ形の
  `hexValueOf` を置いて、`toHexString.go` についての帰納法で往復を言う。
  10 進の `portValue_toString` と同じ作りである。
* **桁数**（`toHexString_length`）。`takeHex 4` が piece を読み切るには 4 桁以下が要る。
* **piece の一歩**（`ipv6Loop_piece`, `ipv6Loop_last`）。fuel を `fuel' + 1` の形で
  受け取るのは、`ipv6Loop 9` の `9` と `8 + 1` が `rw` では合わないためである。
* **serialize の形**（`ipv6Serializer_go_nocompress`）。圧縮が無いので
  `ignore0` は `false` のままで、piece と `:` が交互に並ぶ。

圧縮する場合（`::`）は、`ipv6CompressIndex` が選ぶ 0 の並び（`ipv6CompressIndex_run`）と
serialize の形（`ipv6Serializer_go_seg` ほか三つ）まで来ている。残りは parser の側で、
piece の列をまとめて読む補題と `::` の一歩、それに `ipv6Expand` の算術である。
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-- 16 進で読んだ値。`takeHex` の畳み込みと同じものである。 -/
def hexValueOf (l : List Char) : Nat :=
  l.foldl (fun acc c => acc * 16 + (hexValue c).getD 0) 0

theorem hexFold_acc : ∀ (l : List Char) (a : Nat),
    l.foldl (fun acc c => acc * 16 + (hexValue c).getD 0) a
      = a * 16 ^ l.length + hexValueOf l := by
  intro l
  induction l with
  | nil => intro a; simp [hexValueOf]
  | cons c t ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (a * 16 + (hexValue c).getD 0)]
    rw [show hexValueOf (c :: t) = (hexValue c).getD 0 * 16 ^ t.length + hexValueOf t from by
      unfold hexValueOf
      rw [List.foldl_cons, ih (0 * 16 + (hexValue c).getD 0)]
      simp [hexValueOf]]
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 16 (16 ^ t.length)]
    omega

/-- `hexValueOf` は連結で分けられる。 -/
theorem hexValueOf_append (l1 l2 : List Char) :
    hexValueOf (l1 ++ l2) = hexValueOf l1 * 16 ^ l2.length + hexValueOf l2 := by
  unfold hexValueOf
  rw [List.foldl_append, hexFold_acc]
  rfl

/-- `toHexString` が積む文字は、その桁の値に読み戻せる。 -/
theorem hexValue_hexChar : ∀ (d : Nat), d < 16 →
    hexValue (Char.ofNat (if d < 10 then 0x30 + d else 0x61 + d - 10)) = some d
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

/-- `toHexString.go` が積んだ桁は、16 進で読み戻すと元の数になる。 -/
theorem hexValueOf_toHexStringGo : ∀ (fuel n : Nat) (acc : List Char), n ≤ fuel →
    hexValueOf (toHexString.go n acc) = n * 16 ^ acc.length + hexValueOf acc := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc h
    have : n = 0 := Nat.le_zero.mp h
    subst this
    simp [toHexString.go]
  | succ f ih =>
    intro n acc h
    cases n with
    | zero => simp [toHexString.go]
    | succ m =>
      rw [toHexString.go]
      rw [ih ((m + 1) / 16) _ (by omega)]
      have hd : hexValue (Char.ofNat (if (m + 1) % 16 < 10 then 0x30 + (m + 1) % 16
          else 0x61 + (m + 1) % 16 - 10)) = some ((m + 1) % 16) :=
        hexValue_hexChar _ (by omega)
      rw [show hexValueOf (Char.ofNat (if (m + 1) % 16 < 10 then 0x30 + (m + 1) % 16
          else 0x61 + (m + 1) % 16 - 10) :: acc)
          = (m + 1) % 16 * 16 ^ acc.length + hexValueOf acc from by
        rw [show (Char.ofNat (if (m + 1) % 16 < 10 then 0x30 + (m + 1) % 16
            else 0x61 + (m + 1) % 16 - 10) :: acc)
            = [Char.ofNat (if (m + 1) % 16 < 10 then 0x30 + (m + 1) % 16
              else 0x61 + (m + 1) % 16 - 10)] ++ acc from rfl]
        rw [hexValueOf_append]
        simp [hexValueOf, hd]]
      simp only [List.length_cons, Nat.pow_succ]
      have hsplit : (m + 1) / 16 * (16 ^ acc.length * 16) + (m + 1) % 16 * 16 ^ acc.length
          = (m + 1) * 16 ^ acc.length := by
        rw [Nat.mul_comm (16 ^ acc.length) 16, ← Nat.mul_assoc, ← Nat.add_mul]
        rw [show (m + 1) / 16 * 16 + (m + 1) % 16 = m + 1 from by omega]
      omega

/-- **16 進で書いた数は、読み直すと元に戻る。** -/
theorem hexValueOf_toHexString (n : Nat) : hexValueOf (toHexString n).toList = n := by
  unfold toHexString
  split
  · next h => simp only [beq_iff_eq] at h; subst h; decide
  · rw [String.toList_ofList, hexValueOf_toHexStringGo n n [] (by omega)]
    simp [hexValueOf]

/-- `toHexString` が積むのは 16 進の数字だけである。 -/
theorem toHexStringGo_hex : ∀ (fuel n : Nat) (acc : List Char), n ≤ fuel →
    (∀ c ∈ acc, (hexValue c).isSome = true) →
    ∀ c ∈ toHexString.go n acc, (hexValue c).isSome = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc h hacc
    have : n = 0 := Nat.le_zero.mp h
    subst this
    simpa [toHexString.go] using hacc
  | succ f ih =>
    intro n acc h hacc
    cases n with
    | zero => simpa [toHexString.go] using hacc
    | succ m =>
      rw [toHexString.go]
      refine ih ((m + 1) / 16) _ (by omega) ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hexValue_hexChar _ (by omega)]; rfl
      · exact hacc c hc

theorem toHexString_hex (n : Nat) : ∀ c ∈ (toHexString n).toList, (hexValue c).isSome = true := by
  unfold toHexString
  split
  · intro c hc; simp at hc; subst hc; decide
  · rw [String.toList_ofList]
    exact toHexStringGo_hex n n [] (by omega) (by simp)

/-- `toHexString` の桁数は 16 進の桁数で抑えられる。 -/
theorem toHexStringGo_length : ∀ (fuel d n : Nat) (acc : List Char), n ≤ fuel → n < 16 ^ d →
    (toHexString.go n acc).length ≤ d + acc.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro d n acc h _
    have : n = 0 := Nat.le_zero.mp h
    subst this
    simp [toHexString.go]
  | succ f ih =>
    intro d n acc h hlt
    cases n with
    | zero => simp [toHexString.go]
    | succ m =>
      cases d with
      | zero => simp at hlt
      | succ e =>
        rw [toHexString.go]
        have hrec : (m + 1) / 16 < 16 ^ e := by
          rw [Nat.pow_succ] at hlt
          omega
        have := ih e ((m + 1) / 16)
          (Char.ofNat (if (m + 1) % 16 < 10 then 0x30 + (m + 1) % 16
            else 0x61 + (m + 1) % 16 - 10) :: acc) (by omega) hrec
        simp only [List.length_cons] at this ⊢
        omega

theorem toHexString_length {n : Nat} (h : n < 65536) : (toHexString n).toList.length ≤ 4 := by
  unfold toHexString
  split
  · simp
  · rw [String.toList_ofList]
    have := toHexStringGo_length n 4 n [] (by omega) (by simpa using h)
    simpa using this

/-- `takeHex` は 16 進の数字を読み切って、そこで止まる。 -/
theorem takeHex_append : ∀ (l : List Char) (n : Nat) (rest : List Char),
    (∀ c ∈ l, (hexValue c).isSome = true) → l.length ≤ n →
    (∀ c ∈ rest.head?, hexValue c = none) →
    takeHex n (l ++ rest) = (hexValueOf l, l.length, rest) := by
  intro l
  induction l with
  | nil =>
    intro n rest _ _ hr
    cases n with
    | zero => simp [takeHex, hexValueOf]
    | succ m =>
      cases rest with
      | nil => simp [takeHex, hexValueOf]
      | cons c t =>
        rw [List.nil_append, takeHex]
        rw [hr c rfl]
        simp [hexValueOf]
  | cons c l' ih =>
    intro n rest hl hlen hr
    cases n with
    | zero => simp at hlen
    | succ m =>
      have hc := hl c (by simp)
      rw [List.cons_append, takeHex]
      cases hv : hexValue c with
      | none => rw [hv] at hc; simp at hc
      | some v =>
        simp only []
        rw [ih m rest (fun x hx => hl x (by simp [hx])) (by simp at hlen; omega) hr]
        simp only [List.length_cons]
        rw [show hexValueOf (c :: l') = v * 16 ^ l'.length + hexValueOf l' from by
          rw [show (c :: l') = [c] ++ l' from rfl, hexValueOf_append]
          simp [hexValueOf, hv]]

/-- 一つの piece を読むところ。 -/
theorem takeHex_toHexString {p : Nat} (hp : p < 65536) (rest : List Char)
    (hr : ∀ c ∈ rest.head?, hexValue c = none) :
    takeHex 4 ((toHexString p).toList ++ rest) = (p, (toHexString p).toList.length, rest) := by
  rw [takeHex_append _ 4 rest (toHexString_hex p) (toHexString_length hp) hr]
  rw [hexValueOf_toHexString]

theorem toHexStringGo_ne_nil : ∀ (fuel n : Nat) (acc : List Char), n ≤ fuel → ¬acc = [] →
    ¬toHexString.go n acc = [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc h hacc
    have : n = 0 := Nat.le_zero.mp h
    subst this
    simpa [toHexString.go] using hacc
  | succ f ih =>
    intro n acc h hacc
    cases n with
    | zero => simpa [toHexString.go] using hacc
    | succ m =>
      rw [toHexString.go]
      exact ih ((m + 1) / 16) _ (by omega) (by simp)

theorem toHexString_ne_nil (n : Nat) : ¬(toHexString n).toList = [] := by
  unfold toHexString
  split
  · simp
  · next h =>
    rw [String.toList_ofList]
    cases n with
    | zero => simp at h
    | succ m =>
      rw [toHexString.go]
      exact toHexStringGo_ne_nil ((m + 1) / 16) ((m + 1) / 16) _ (by omega) (by simp)

/-- `toHexString` は空でなく、`:` でも `.` でも始まらない。 -/
theorem toHexString_head {n : Nat} :
    ∃ c t, (toHexString n).toList = c :: t ∧ ¬c = ':' ∧ ¬c = '.' := by
  cases hx : (toHexString n).toList with
  | nil => exact absurd hx (toHexString_ne_nil n)
  | cons c t =>
    have hc := toHexString_hex n c (by rw [hx]; simp)
    refine ⟨c, t, rfl, ?_, ?_⟩ <;> (intro he; rw [he] at hc; revert hc; decide)

/-- piece を一つ読んで `:` で次へ進む。 -/
theorem ipv6Loop_piece {p : Nat} (hp : p < 65536) (fuel fuel' : Nat) (hf : fuel = fuel' + 1)
    (rest : List Char) (addr : Ipv6)
    (pi : Nat) (compress : Option Nat) (hpi : ¬pi = 8) (hne : ¬rest = []) :
    ipv6Loop fuel ((toHexString p).toList ++ ':' :: rest) addr pi compress
      = ipv6Loop fuel' rest (addr.set pi p) (pi + 1) compress := by
  subst hf
  obtain ⟨c, t, hct, hc1, hc2⟩ := toHexString_head (n := p)
  have hemp : ¬rest.isEmpty = true := by
    cases hx : rest with
    | nil => exact absurd hx hne
    | cons a b => simp
  have htake : takeHex 4 (c :: (t ++ ':' :: rest))
      = (p, (toHexString p).toList.length, ':' :: rest) := by
    rw [← List.cons_append, ← hct]
    exact takeHex_toHexString hp (':' :: rest)
      (fun x hx => by
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
        subst hx
        decide)
  rw [hct]
  simp only [List.cons_append]
  rw [ipv6Loop]
  case x_6 => simp
  case x_7 =>
    intro r h
    simp only [List.cons.injEq] at h
    exact hc1 h.1
  rw [if_neg (by simp [hpi])]
  rw [htake]
  simp only []
  rw [if_neg hemp]

/-- 最後の piece。入力が尽きるので `pieceIndex` を一つ進めて返す。 -/
theorem ipv6Loop_last {p : Nat} (hp : p < 65536) (fuel fuel' : Nat) (hf : fuel = fuel' + 1)
    (addr : Ipv6) (pi : Nat) (compress : Option Nat) (hpi : ¬pi = 8) :
    ipv6Loop fuel (toHexString p).toList addr pi compress
      = some (addr.set pi p, pi + 1, compress) := by
  subst hf
  obtain ⟨c, t, hct, hc1, hc2⟩ := toHexString_head (n := p)
  have htake : takeHex 4 (c :: t) = (p, (toHexString p).toList.length, []) := by
    rw [show (c :: t) = (toHexString p).toList ++ [] from by rw [hct]; simp]
    exact takeHex_toHexString hp [] (by simp)
  rw [hct, ipv6Loop]
  case x_6 => simp
  case x_7 =>
    intro r h
    simp only [List.cons.injEq] at h
    exact hc1 h.1
  rw [if_neg (by simp [hpi])]
  rw [htake]

/-- 圧縮しないときの serialize は、piece と `:` を交互に並べたものである。 -/
theorem ipv6Serializer_go_nocompress : ∀ (l : List (Nat × Nat)),
    (ipv6Serializer.go none l false).toList
      = l.flatMap (fun pi => (toHexString pi.1).toList ++ (if pi.2 == 7 then [] else [':'])) := by
  intro l
  induction l with
  | nil => rfl
  | cons pi rest ih =>
    obtain ⟨p, i⟩ := pi
    rw [ipv6Serializer.go]
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [if_neg (show ¬((none : Option Nat) == some i) = true from by simp)]
    rw [String.toList_append, String.toList_append, ih]
    simp only [List.flatMap_cons]
    congr 1
    · split <;> simp

/--
**圧縮しない IPv6 address は、serialize して parse し直すと元に戻る。**

`ipv6CompressIndex` が `none` を返すのは、長さ 2 以上の 0 の並びが無いときである。
-/
theorem ipv6Parser_serializer_nocompress {a : Ipv6}
    (h8 : a.length = 8) (hp : ∀ p ∈ a, p < 65536) (hc : ipv6CompressIndex a = none) :
    ipv6Parser (ipv6Serializer a).toList = some a := by
  match a, h8 with
  | [p0, p1, p2, p3, p4, p5, p6, p7], _ =>
    have hp0 := hp p0 (by simp)
    have hp1 := hp p1 (by simp)
    have hp2 := hp p2 (by simp)
    have hp3 := hp p3 (by simp)
    have hp4 := hp p4 (by simp)
    have hp5 := hp p5 (by simp)
    have hp6 := hp p6 (by simp)
    have hp7 := hp p7 (by simp)
    have hser : (ipv6Serializer [p0, p1, p2, p3, p4, p5, p6, p7]).toList
        = (toHexString p0).toList ++ ':' :: ((toHexString p1).toList ++ ':' ::
          ((toHexString p2).toList ++ ':' :: ((toHexString p3).toList ++ ':' ::
            ((toHexString p4).toList ++ ':' :: ((toHexString p5).toList ++ ':' ::
              ((toHexString p6).toList ++ ':' :: (toHexString p7).toList)))))) := by
      show (ipv6Serializer.go (ipv6CompressIndex [p0, p1, p2, p3, p4, p5, p6, p7])
        (List.zipIdx [p0, p1, p2, p3, p4, p5, p6, p7]) false).toList = _
      rw [hc, ipv6Serializer_go_nocompress]
      simp
    rw [hser]
    obtain ⟨c0, t0, hct0, hcc0, hcd0⟩ := toHexString_head (n := p0)
    rw [ipv6Parser]
    case x_1 =>
      intro r h
      rw [hct0] at h
      simp only [List.cons_append, List.cons.injEq] at h
      exact hcc0 h.1
    case x_2 =>
      intro r h
      rw [hct0] at h
      simp only [List.cons_append, List.cons.injEq] at h
      exact hcc0 h.1
    rw [ipv6Loop_piece hp0 9 8 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp1 8 7 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp2 7 6 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp3 6 5 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp4 5 4 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp5 4 3 rfl _ _ _ _ (by decide) (by simp)]
    rw [ipv6Loop_piece hp6 3 2 rfl _ _ _ _ (by decide) (toHexString_ne_nil p7)]
    rw [ipv6Loop_last hp7 2 1 rfl _ _ _ (by decide)]
    rfl

/-! ## 圧縮する場合

`::` が出る場合の足場。serialize の側は四つの補題で形が決まる。
parser の側（piece の列をまとめて読む補題と `::` の一歩、`ipv6Expand` の算術）は
まだ入れていない。
-/

/--
**圧縮する位置は、長さ 2 以上の 0 の並びの先頭である。**

`ipv6CompressIndex` の畳み込みは `longestSize` を 1 から始めるので、
返ってくるのは長さ 2 以上の並びだけである。
-/
theorem ipv6CompressIndex_run {p0 p1 p2 p3 p4 p5 p6 p7 c : Nat}
    (hc : ipv6CompressIndex [p0, p1, p2, p3, p4, p5, p6, p7] = some c) :
    c + 1 < 8 ∧ [p0, p1, p2, p3, p4, p5, p6, p7].getD c 0 = 0
      ∧ [p0, p1, p2, p3, p4, p5, p6, p7].getD (c + 1) 0 = 0 := by
  by_cases h0 : p0 = 0 <;> by_cases h1 : p1 = 0 <;> by_cases h2 : p2 = 0 <;>
    by_cases h3 : p3 = 0 <;> by_cases h4 : p4 = 0 <;> by_cases h5 : p5 = 0 <;>
    by_cases h6 : p6 = 0 <;> by_cases h7 : p7 = 0 <;>
    simp [ipv6CompressIndex, List.zipIdx, h0, h1, h2, h3, h4, h5, h6, h7] at hc ⊢ <;>
    (subst hc; simp_all)

/-- 圧縮の位置でない piece は、そのまま並ぶ。 -/
theorem ipv6Serializer_go_seg : ∀ (l rest : List (Nat × Nat)) (c : Nat), (∀ pi ∈ l, ¬pi.2 = c) →
    (ipv6Serializer.go (some c) (l ++ rest) false).toList
      = l.flatMap (fun pi => (toHexString pi.1).toList ++ (if pi.2 = 7 then [] else [':']))
        ++ (ipv6Serializer.go (some c) rest false).toList := by
  intro l
  induction l with
  | nil => intro rest c _; simp
  | cons pi t ih =>
    obtain ⟨p, i⟩ := pi
    intro rest c h
    rw [List.cons_append, ipv6Serializer.go]
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [if_neg (by
      simp only [beq_iff_eq, Option.some.injEq]
      exact fun hx => h (p, i) (by simp) hx.symm)]
    rw [String.toList_append, String.toList_append]
    rw [ih rest c (fun x hx => h x (by simp [hx]))]
    simp only [List.flatMap_cons, List.append_assoc]
    congr 2
    split <;> simp_all

/-- 圧縮の位置。`::` か `:` を書いて、以後の 0 を飛ばす。 -/
theorem ipv6Serializer_go_at (c p : Nat) (rest : List (Nat × Nat)) :
    (ipv6Serializer.go (some c) ((p, c) :: rest) false).toList
      = (if c = 0 then [':', ':'] else [':']) ++ (ipv6Serializer.go (some c) rest true).toList := by
  rw [ipv6Serializer.go]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [if_pos (by simp)]
  rw [String.toList_append]
  congr 1
  split <;> simp_all

/-- 圧縮の後ろの 0 は飛ばされる。 -/
theorem ipv6Serializer_go_skip : ∀ (mid rest : List (Nat × Nat)) (c : Nat),
    (∀ pi ∈ mid, pi.1 = 0) →
    (ipv6Serializer.go (some c) (mid ++ rest) true).toList
      = (ipv6Serializer.go (some c) rest true).toList := by
  intro mid
  induction mid with
  | nil => intro rest c _; simp
  | cons pi t ih =>
    obtain ⟨p, i⟩ := pi
    intro rest c h
    rw [List.cons_append, ipv6Serializer.go]
    rw [if_pos (by simp only [Bool.and_eq_true, beq_iff_eq]
                   exact ⟨trivial, h (p, i) (by simp)⟩)]
    exact ih rest c (fun x hx => h x (by simp [hx]))

/-- 0 の並びが切れたところ。以後は `ignore0` が `false` に戻る。 -/
theorem ipv6Serializer_go_resume (c p i : Nat) (rest : List (Nat × Nat)) (hp : ¬p = 0)
    (hi : ¬i = c) :
    (ipv6Serializer.go (some c) ((p, i) :: rest) true).toList
      = (toHexString p).toList ++ (if i = 7 then [] else [':'])
        ++ (ipv6Serializer.go (some c) rest false).toList := by
  rw [ipv6Serializer.go]
  rw [if_neg (by simp [hp])]
  rw [if_neg (by simp only [beq_iff_eq, Option.some.injEq]; exact fun hx => hi hx.symm)]
  rw [String.toList_append, String.toList_append]
  congr 2
  split <;> simp_all

/-- 圧縮の無い address の例。`2001:db8:1:2:3:4:5:6` は実際にこの形である。 -/
example : ipv6Parser (ipv6Serializer [0x2001, 0xdb8, 1, 2, 3, 4, 5, 6]).toList
    = some [0x2001, 0xdb8, 1, 2, 3, 4, 5, 6] :=
  ipv6Parser_serializer_nocompress (by decide) (by decide) (by decide)

/-- 0 が一つだけなら圧縮しない。 -/
example : ipv6Parser (ipv6Serializer [1, 0, 2, 3, 4, 5, 6, 7]).toList
    = some [1, 0, 2, 3, 4, 5, 6, 7] :=
  ipv6Parser_serializer_nocompress (by decide) (by decide) (by decide)

end Url
