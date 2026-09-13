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

圧縮する場合（`::`）も `ipv6Parser_serializer_compress` で閉じた。
`ipv6Parser_serializer` が両方をまとめる。
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

`::` が出る場合。address を 0 の並びで `pre ++ replicate L 0 ++ post` に割り
（`ipv6_run_decompose`）、serialize の形を四つの補題で決め、parser の側は
piece の列をまとめて読む補題（`ipv6Loop_pieces`）と `::` の一歩（`ipv6Loop_colon`）で進む。

最後の `ipv6Expand` の帳尻は、parser の `compress` が圧縮位置 `c` ではなく `c + 1` に
なることで合う。`take (c + 1)` に 0 が一つ含まれ、`replicate` が残り `L - 1` 個を戻す。
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

/-- piece の列を address に順に書き込む。 -/
def setPieces : Ipv6 → Nat → List Nat → Ipv6
  | addr, _, [] => addr
  | addr, i, p :: ps => setPieces (addr.set i p) (i + 1) ps

/-- serializer が piece と `:` を交互に並べる分。 -/
def sepPieces (ps : List Nat) : List Char :=
  ps.flatMap (fun p => (toHexString p).toList ++ [':'])

@[simp] theorem sepPieces_nil : sepPieces [] = [] := rfl

theorem sepPieces_cons (p : Nat) (ps : List Nat) :
    sepPieces (p :: ps) = (toHexString p).toList ++ ':' :: sepPieces ps := by
  simp [sepPieces]

/-- piece の列を読み切る。 -/
theorem ipv6Loop_pieces : ∀ (ps : List Nat) (fuel : Nat) (tail : List Char) (addr : Ipv6)
    (pi : Nat) (compress : Option Nat),
    (∀ p ∈ ps, p < 65536) → ps.length ≤ fuel → pi + ps.length ≤ 8 → ¬tail = [] →
    ipv6Loop fuel (sepPieces ps ++ tail) addr pi compress
      = ipv6Loop (fuel - ps.length) tail (setPieces addr pi ps) (pi + ps.length) compress := by
  intro ps
  induction ps with
  | nil => intro fuel tail addr pi compress _ _ _ _; simp [setPieces]
  | cons p ps ih =>
    intro fuel tail addr pi compress hp hlen hpi hne
    rw [sepPieces_cons, List.append_assoc, List.cons_append]
    rw [ipv6Loop_piece (hp p (by simp)) fuel (fuel - 1) (by simp at hlen; omega) _ _ _ _
      (by simp at hpi; omega) (by
        intro hx
        exact hne (List.append_eq_nil_iff.mp hx).2)]
    rw [ih (fuel - 1) tail (addr.set pi p) (pi + 1) compress
      (fun x hx => hp x (by simp [hx])) (by simp at hlen; omega) (by simp at hpi; omega) hne]
    simp only [setPieces, List.length_cons]
    congr 1
    · omega
    · omega

/-- 入力が尽きたところ。 -/
theorem ipv6Loop_nil (fuel : Nat) (hf : 0 < fuel) (addr : Ipv6) (pi : Nat)
    (compress : Option Nat) :
    ipv6Loop fuel [] addr pi compress = some (addr, pi, compress) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [ipv6Loop]

/-- `::` の `:`。piece を一つ飛ばして、そこを圧縮の位置として覚える。 -/
theorem ipv6Loop_colon (fuel : Nat) (hf : 0 < fuel) (rest : List Char) (addr : Ipv6) (pi : Nat)
    (hpi : ¬pi = 8) :
    ipv6Loop fuel (':' :: rest) addr pi none
      = ipv6Loop (fuel - 1) rest addr (pi + 1) (some (pi + 1)) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [ipv6Loop]
  rw [if_neg (by simp [hpi])]
  simp

/-- 最後の piece。fuel は 0 でなければよい。 -/
theorem ipv6Loop_last' {p : Nat} (hp : p < 65536) (fuel : Nat) (hf : 0 < fuel) (addr : Ipv6)
    (pi : Nat) (compress : Option Nat) (hpi : ¬pi = 8) :
    ipv6Loop fuel (toHexString p).toList addr pi compress
      = some (addr.set pi p, pi + 1, compress) :=
  ipv6Loop_last hp fuel (fuel - 1) (by omega) addr pi compress hpi

/-- 前半の長さのところに書くと、その一つが差し替わる。 -/
theorem set_append_length : ∀ (l1 : List Nat) (q : Nat) (t : List Nat) (p : Nat),
    (l1 ++ q :: t).set l1.length p = l1 ++ p :: t
  | [], q, t, p => rfl
  | a :: l1, q, t, p => by
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    rw [set_append_length l1 q t p]

/-- piece の列を書き込むと、その分だけ差し替わる。 -/
theorem setPieces_append : ∀ (ps : List Nat) (l1 l2 : Ipv6), ps.length ≤ l2.length →
    setPieces (l1 ++ l2) l1.length ps = l1 ++ ps ++ l2.drop ps.length := by
  intro ps
  induction ps with
  | nil => intro l1 l2 _; simp [setPieces]
  | cons p ps ih =>
    intro l1 l2 h
    cases l2 with
    | nil => simp at h
    | cons q t =>
      rw [setPieces, set_append_length]
      rw [show l1 ++ p :: t = (l1 ++ [p]) ++ t from by simp]
      rw [show l1.length + 1 = (l1 ++ [p]).length from by simp]
      rw [ih (l1 ++ [p]) t (by simp at h ⊢; omega)]
      simp

/-- 先頭から続く 0 は `replicate` である。 -/
theorem takeWhile_zero_replicate : ∀ (l : List Nat),
    l.takeWhile (fun p => p == 0) = List.replicate (l.takeWhile (fun p => p == 0)).length 0
  | [] => rfl
  | q :: t => by
    rw [List.takeWhile_cons]
    split
    · next h =>
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
      refine ⟨by simpa using h, takeWhile_zero_replicate t⟩
    · simp

/-- 0 の並びが切れたところは 0 でない。 -/
theorem head_dropWhile_zero : ∀ (l : List Nat),
    ∀ q ∈ (l.dropWhile (fun p => p == 0)).head?, ¬q = 0
  | [] => by simp
  | a :: t => by
    rw [List.dropWhile_cons]
    split
    · exact head_dropWhile_zero t
    · next h =>
      intro q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      simpa using h

/-- 0 の並びの先頭が分かれば、address をその並びで三つに割れる。 -/
theorem ipv6_run_decompose {a : Ipv6} {c : Nat} (h8 : a.length = 8) (hc1 : c + 1 < 8)
    (hz0 : a.getD c 0 = 0) (hz1 : a.getD (c + 1) 0 = 0) :
    ∃ (L : Nat) (post : List Nat),
      a = a.take c ++ List.replicate L 0 ++ post ∧ 2 ≤ L ∧
        (∀ q ∈ post.head?, ¬q = 0) ∧ c + L + post.length = 8 := by
  have hd0 : (a.drop c).getD 0 0 = 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
    simpa [List.getD_eq_getElem?_getD] using hz0
  have hd1 : (a.drop c).getD 1 0 = 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    simpa [List.getD_eq_getElem?_getD] using hz1
  have hdlen : (a.drop c).length = 8 - c := by simp [h8]
  refine ⟨((a.drop c).takeWhile (fun p => p == 0)).length,
    (a.drop c).dropWhile (fun p => p == 0), ?_, ?_, head_dropWhile_zero _, ?_⟩
  · calc a = a.take c ++ a.drop c := (List.take_append_drop c a).symm
      _ = a.take c ++ ((a.drop c).takeWhile (fun p => p == 0)
            ++ (a.drop c).dropWhile (fun p => p == 0)) := by
          rw [List.takeWhile_append_dropWhile]
      _ = a.take c ++ List.replicate ((a.drop c).takeWhile (fun p => p == 0)).length 0
            ++ (a.drop c).dropWhile (fun p => p == 0) := by
          rw [← takeWhile_zero_replicate, List.append_assoc]
  · cases hd : a.drop c with
    | nil => rw [hd] at hdlen; simp at hdlen; omega
    | cons d0 t =>
      cases t with
      | nil => rw [hd] at hdlen; simp at hdlen; omega
      | cons d1 t2 =>
        have h0 : d0 = 0 := by rw [hd] at hd0; simpa using hd0
        have h1 : d1 = 0 := by rw [hd] at hd1; simpa using hd1
        rw [List.takeWhile_cons, if_pos (by simp [h0]), List.takeWhile_cons,
          if_pos (by simp [h1])]
        simp
  · have h2 := congrArg List.length
      (List.takeWhile_append_dropWhile (p := fun p => p == 0) (l := a.drop c))
    simp only [List.length_append] at h2
    omega

/-- serializer が索引付きの piece を並べる分。 -/
def piecesChars (l : List (Nat × Nat)) : List Char :=
  l.flatMap (fun pi => (toHexString pi.1).toList ++ (if pi.2 = 7 then [] else [':']))

/-- 索引が 7 にならない範囲では、区切りは必ず `:` である。 -/
theorem piecesChars_sep : ∀ (l : List Nat) (n : Nat),
    (∀ i, n ≤ i → i < n + l.length → ¬i = 7) →
    piecesChars (l.zipIdx n) = sepPieces l := by
  intro l
  induction l with
  | nil => intro n _; simp [piecesChars, sepPieces]
  | cons p t ih =>
    intro n h
    rw [List.zipIdx_cons]
    simp only [piecesChars, List.flatMap_cons]
    rw [if_neg (h n (by omega) (by simp))]
    rw [show (t.zipIdx (n + 1)).flatMap
        (fun pi => (toHexString pi.1).toList ++ (if pi.2 = 7 then [] else [':']))
        = sepPieces t from
      ih (n + 1) (fun i h1 h2 => h i (by omega) (by simp at h2 ⊢; omega))]
    rw [sepPieces_cons]
    simp

/-- 最後の piece には区切りが付かない。 -/
theorem piecesChars_snoc (init : List Nat) (q n : Nat) (h : n + init.length = 7) :
    piecesChars ((init ++ [q]).zipIdx n) = sepPieces init ++ (toHexString q).toList := by
  rw [List.zipIdx_append]
  simp only [piecesChars, List.flatMap_append]
  rw [show (init.zipIdx n).flatMap
      (fun pi => (toHexString pi.1).toList ++ (if pi.2 = 7 then [] else [':']))
      = sepPieces init from piecesChars_sep init n (fun i h1 h2 => by omega)]
  rw [h]
  simp

/-- `zipIdx` が付ける索引の範囲。 -/
theorem zipIdx_snd_range : ∀ (l : List Nat) (n : Nat),
    ∀ pi ∈ l.zipIdx n, n ≤ pi.2 ∧ pi.2 < n + l.length
  | [], n => by simp
  | p :: t, n => by
    intro pi hpi
    rw [List.zipIdx_cons] at hpi
    rcases List.mem_cons.mp hpi with rfl | hpi
    · simp
    · have := zipIdx_snd_range t (n + 1) pi hpi
      simp only [List.length_cons]
      omega

/-- `replicate` の piece はどれも 0 である。 -/
theorem zipIdx_replicate_zero : ∀ (L n : Nat), ∀ pi ∈ (List.replicate L 0).zipIdx n, pi.1 = 0
  | 0, n => by simp
  | L + 1, n => by
    intro pi hpi
    rw [List.replicate_succ, List.zipIdx_cons] at hpi
    rcases List.mem_cons.mp hpi with rfl | hpi
    · rfl
    · exact zipIdx_replicate_zero L (n + 1) pi hpi

/-- 圧縮の位置を含まない残り全部。 -/
theorem ipv6Serializer_go_tail (l : List (Nat × Nat)) (c : Nat) (h : ∀ pi ∈ l, ¬pi.2 = c) :
    (ipv6Serializer.go (some c) l false).toList = piecesChars l := by
  have h2 := ipv6Serializer_go_seg l [] c h
  rw [List.append_nil] at h2
  rw [h2]
  simp [ipv6Serializer.go, piecesChars]

/-- 圧縮する場合の serialize の形。 -/
theorem ipv6Serializer_compress_shape {a : Ipv6} {c L : Nat} {pre post : List Nat}
    (hsplit : a = pre ++ List.replicate L 0 ++ post) (hpre : pre.length = c)
    (hL : 2 ≤ L) (hpost : ∀ q ∈ post.head?, ¬q = 0) (hlen : c + L + post.length = 8)
    (hc : ipv6CompressIndex a = some c) :
    (ipv6Serializer a).toList
      = sepPieces pre ++ (if c = 0 then [':', ':'] else [':'])
        ++ piecesChars (post.zipIdx (c + L)) := by
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  show (ipv6Serializer.go (ipv6CompressIndex a) a.zipIdx false).toList = _
  rw [hc, hsplit]
  rw [List.zipIdx_append, List.zipIdx_append, List.append_assoc]
  simp only [hpre, Nat.zero_add]
  rw [ipv6Serializer_go_seg pre.zipIdx _ c (fun pi hpi => by
    have := zipIdx_snd_range pre 0 pi hpi
    omega)]
  rw [show List.flatMap (fun pi => (toHexString pi.fst).toList ++ if pi.snd = 7 then [] else [':'])
      pre.zipIdx = sepPieces pre from piecesChars_sep pre 0 (fun i h1 h2 => by omega)]
  have hlen2 : (pre ++ List.replicate (M + 1) 0).length = c + (M + 1) := by
    simp only [List.length_append, List.length_replicate, hpre]
  rw [hlen2]
  rw [List.replicate_succ, List.zipIdx_cons, List.cons_append]
  rw [ipv6Serializer_go_at c 0 _]
  rw [ipv6Serializer_go_skip ((List.replicate M 0).zipIdx (c + 1)) _ c
    (zipIdx_replicate_zero M (c + 1))]
  cases hpo : post with
  | nil =>
    simp [ipv6Serializer.go, piecesChars]
  | cons q t =>
    have hq : ¬q = 0 := hpost q (by rw [hpo]; simp)
    rw [List.zipIdx_cons]
    rw [ipv6Serializer_go_resume c q (c + (M + 1)) _ hq (by omega)]
    rw [ipv6Serializer_go_tail (t.zipIdx (c + (M + 1) + 1)) c (fun pi hpi => by
      have := zipIdx_snd_range t (c + (M + 1) + 1) pi hpi
      omega)]
    simp only [piecesChars, List.flatMap_cons]
    simp [List.append_assoc]

/-- 末尾に一つ足して書き込む。 -/
theorem setPieces_snoc : ∀ (init : List Nat) (addr : Ipv6) (i q : Nat),
    setPieces addr i (init ++ [q]) = (setPieces addr i init).set (i + init.length) q
  | [], addr, i, q => by simp [setPieces]
  | p :: t, addr, i, q => by
    rw [List.cons_append, setPieces, setPieces, setPieces_snoc t (addr.set i p) (i + 1) q]
    simp only [List.length_cons]
    congr 1
    omega

/-- 圧縮の後ろの piece を読み切る。 -/
theorem ipv6Loop_post {post : List Nat} {c L : Nat} (hpp : ∀ p ∈ post, p < 65536)
    (hlen : c + L + post.length = 8) (_hc1 : c + 1 < 8) (hL : 2 ≤ L)
    (fuel : Nat) (hf : post.length < fuel) (addr : Ipv6) :
    ipv6Loop fuel (piecesChars (post.zipIdx (c + L))) addr (c + 1) (some (c + 1))
      = some (setPieces addr (c + 1) post, c + 1 + post.length, some (c + 1)) := by
  by_cases hpe : post = []
  · subst hpe
    simp only [piecesChars, List.zipIdx_nil, List.flatMap_nil, setPieces, List.length_nil,
      Nat.add_zero]
    exact ipv6Loop_nil fuel (by omega) _ _ _
  · obtain ⟨init, q, hq⟩ : ∃ init q, post = init ++ [q] :=
      ⟨post.dropLast, post.getLast hpe, (List.dropLast_concat_getLast hpe).symm⟩
    subst hq
    have hil : init.length + 1 = (init ++ [q]).length := by simp
    rw [piecesChars_snoc init q (c + L) (by simp at hlen ⊢; omega)]
    rw [ipv6Loop_pieces init fuel _ addr (c + 1) (some (c + 1))
      (fun x hx => hpp x (by simp [hx])) (by simp at hf ⊢; omega) (by simp at hlen ⊢; omega)
      (toHexString_ne_nil q)]
    rw [ipv6Loop_last' (hpp q (by simp)) (fuel - init.length) (by simp at hf ⊢; omega) _ _ _
      (by simp at hlen ⊢; omega)]
    rw [setPieces_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil]
    congr 2

/-- `::` で始まる入力の入口。 -/
theorem ipv6Parser_colon_colon {rest : List Char} {addr : Ipv6} {pi : Nat} {comp : Option Nat}
    (h : ipv6Loop 9 rest ipv6Zero 1 (some 1) = some (addr, pi, comp)) :
    ipv6Parser (':' :: ':' :: rest) = ipv6Parser.ipv6Finish addr pi comp := by
  rw [ipv6Parser, h]

/-- `:` で始まらない入力の入口。 -/
theorem ipv6Parser_no_colon {input : List Char} {d : Char} {rest : List Char}
    {addr : Ipv6} {pi : Nat} {comp : Option Nat}
    (hin : input = d :: rest) (hd : ¬d = ':')
    (h : ipv6Loop 9 input ipv6Zero 0 none = some (addr, pi, comp)) :
    ipv6Parser input = ipv6Parser.ipv6Finish addr pi comp := by
  rw [hin] at h ⊢
  rw [ipv6Parser]
  case x_1 =>
    intro r h2
    simp only [List.cons.injEq] at h2
    exact hd h2.1
  case x_2 =>
    intro r h2
    simp only [List.cons.injEq] at h2
    exact hd h2.1
  rw [h]

/-- 書き込んだ address の形。 -/
theorem setPieces_zero_shape {pre post : List Nat} {c L : Nat} (hpre : pre.length = c)
    (hlen : c + L + post.length = 8) (hL : 2 ≤ L) :
    setPieces (setPieces ipv6Zero 0 pre) (c + 1) post
      = (pre ++ [0]) ++ post ++ List.replicate (L - 1) 0 := by
  have h1 : setPieces ipv6Zero 0 pre = pre ++ List.replicate (8 - c) 0 := by
    have := setPieces_append pre [] ipv6Zero (by simp [ipv6Zero]; omega)
    simp only [List.nil_append, List.length_nil] at this
    rw [this]
    congr 1
    rw [show ipv6Zero = List.replicate 8 0 from rfl, List.drop_replicate, hpre]
  have h2 : List.replicate (8 - c) 0 = (0 : Nat) :: List.replicate (7 - c) 0 := by
    rw [show 8 - c = (7 - c) + 1 from by omega, List.replicate_succ]
  rw [h1, h2]
  rw [show pre ++ (0 : Nat) :: List.replicate (7 - c) 0 = (pre ++ [0]) ++ List.replicate (7 - c) 0
    from by simp]
  have h3 : (pre ++ [(0 : Nat)]).length = c + 1 := by simp [hpre]
  rw [← h3]
  rw [setPieces_append post (pre ++ [0]) (List.replicate (7 - c) 0) (by simp; omega)]
  rw [List.drop_replicate]
  congr 2
  omega

/-- **圧縮する IPv6 address も、serialize して parse し直すと元に戻る。** -/
theorem ipv6Parser_serializer_compress {a : Ipv6} {c : Nat}
    (h8 : a.length = 8) (hp : ∀ p ∈ a, p < 65536) (hc : ipv6CompressIndex a = some c) :
    ipv6Parser (ipv6Serializer a).toList = some a := by
  obtain ⟨hc1, hz0, hz1⟩ : c + 1 < 8 ∧ a.getD c 0 = 0 ∧ a.getD (c + 1) 0 = 0 := by
    match a, h8 with
    | [p0, p1, p2, p3, p4, p5, p6, p7], _ => exact ipv6CompressIndex_run hc
  obtain ⟨L, post, hsplit, hL, hpost, hlen⟩ := ipv6_run_decompose h8 hc1 hz0 hz1
  have hpre : (a.take c).length = c := by rw [List.length_take, h8]; omega
  have hpp : ∀ p ∈ post, p < 65536 := by
    intro p hpm
    exact hp p (by rw [hsplit]; simp [hpm])
  have hprep : ∀ p ∈ a.take c, p < 65536 := fun p hpm => hp p (List.mem_of_mem_take hpm)
  have hfin : ipv6Parser.ipv6Finish
      (setPieces (setPieces ipv6Zero 0 (a.take c)) (c + 1) post) (c + 1 + post.length)
      (some (c + 1)) = some a := by
    simp only [ipv6Parser.ipv6Finish, ipv6Expand]
    rw [setPieces_zero_shape hpre hlen hL]
    have hk : ((a.take c ++ [(0 : Nat)]) ++ (post ++ List.replicate (L - 1) 0)).take (c + 1)
        = a.take c ++ [0] := by
      rw [show c + 1 = (a.take c ++ [(0 : Nat)]).length from by simp [hpre]]
      exact List.take_left
    have hd : ((a.take c ++ [(0 : Nat)]) ++ (post ++ List.replicate (L - 1) 0)).drop (c + 1)
        = post ++ List.replicate (L - 1) 0 := by
      rw [show c + 1 = (a.take c ++ [(0 : Nat)]).length from by simp [hpre]]
      exact List.drop_left
    rw [List.append_assoc (a.take c ++ [0]) post, hk, hd]
    rw [show c + 1 + post.length - (c + 1) = post.length from by omega]
    have htk : (post ++ List.replicate (L - 1) 0).take post.length = post := List.take_left
    rw [htk]
    rw [show 8 - (c + 1) - post.length = L - 1 from by omega]
    rw [hsplit]
    rw [show L = (L - 1) + 1 from by omega, List.replicate_succ]
    have hlt : ((a.take c ++ (0 : Nat) :: List.replicate (L - 1) 0) ++ post).take
        (a.take c).length = a.take c := by
      rw [List.append_assoc]
      exact List.take_left
    rw [hpre] at hlt
    rw [hlt]
    simp
  rw [ipv6Serializer_compress_shape hsplit hpre hL hpost hlen hc]
  by_cases hc0 : c = 0
  · subst hc0
    have hpost0 := ipv6Loop_post (c := 0) (L := L) hpp hlen hc1 hL 9
      (by simp at hlen; omega) ipv6Zero
    simp only [List.take_zero, sepPieces_nil, List.nil_append, ite_true]
    rw [show ([':', ':'] ++ piecesChars (post.zipIdx (0 + L)))
        = ':' :: ':' :: piecesChars (post.zipIdx (0 + L)) from rfl]
    simp only [Nat.zero_add] at hpost0 ⊢
    rw [ipv6Parser_colon_colon hpost0]
    simpa only [List.take_zero, setPieces, Nat.zero_add] using hfin
  · have hpne : ¬(a.take c) = [] := by
      intro hx
      rw [hx] at hpre
      simp at hpre
      omega
    obtain ⟨p0, t0, hpt⟩ : ∃ p0 t0, a.take c = p0 :: t0 := by
      cases hx : a.take c with
      | nil => exact absurd hx hpne
      | cons p0 t0 => exact ⟨p0, t0, rfl⟩
    obtain ⟨d0, tl0, hd0, hdne, -⟩ := toHexString_head (n := p0)
    rw [if_neg hc0, List.append_assoc]
    have hloop : ipv6Loop 9 (sepPieces (a.take c) ++ ([':'] ++ piecesChars (post.zipIdx (c + L))))
        ipv6Zero 0 none
        = some (setPieces (setPieces ipv6Zero 0 (a.take c)) (c + 1) post,
            c + 1 + post.length, some (c + 1)) := by
      rw [ipv6Loop_pieces (a.take c) 9 _ ipv6Zero 0 none hprep (by omega) (by omega) (by simp)]
      rw [hpre]
      rw [List.singleton_append]
      rw [ipv6Loop_colon (9 - c) (by omega) _ _ (0 + c) (by omega)]
      simp only [Nat.zero_add]
      exact ipv6Loop_post hpp hlen hc1 hL (9 - c - 1) (by omega) _
    rw [ipv6Parser_no_colon (d := d0)
      (rest := tl0 ++ ':' :: sepPieces t0 ++ ([':'] ++ piecesChars (post.zipIdx (c + L))))
      (by rw [hpt, sepPieces_cons, hd0]; simp) hdne hloop]
    exact hfin

/-- **IPv6 address は serialize して parse し直すと元に戻る。**（§3.5 → §3.3） -/
theorem ipv6Parser_serializer {a : Ipv6} (h8 : a.length = 8) (hp : ∀ p ∈ a, p < 65536) :
    ipv6Parser (ipv6Serializer a).toList = some a := by
  cases hc : ipv6CompressIndex a with
  | none => exact ipv6Parser_serializer_nocompress h8 hp hc
  | some c => exact ipv6Parser_serializer_compress h8 hp hc

/-- `::1` も戻る。`toHexString` が簡約しないので `decide` では確かめられない分である。 -/
example : ipv6Parser (ipv6Serializer [0, 0, 0, 0, 0, 0, 0, 1]).toList
    = some [0, 0, 0, 0, 0, 0, 0, 1] :=
  ipv6Parser_serializer (by decide) (by decide)

/-- 全部 0 の `::` も戻る。 -/
example : ipv6Parser (ipv6Serializer [0, 0, 0, 0, 0, 0, 0, 0]).toList
    = some [0, 0, 0, 0, 0, 0, 0, 0] :=
  ipv6Parser_serializer (by decide) (by decide)

/-- 真ん中で圧縮する `2001:db8::1` も戻る。 -/
example : ipv6Parser (ipv6Serializer [0x2001, 0xdb8, 0, 0, 0, 0, 0, 1]).toList
    = some [0x2001, 0xdb8, 0, 0, 0, 0, 0, 1] :=
  ipv6Parser_serializer (by decide) (by decide)

/-- 圧縮の無い address の例。`2001:db8:1:2:3:4:5:6` は実際にこの形である。 -/
example : ipv6Parser (ipv6Serializer [0x2001, 0xdb8, 1, 2, 3, 4, 5, 6]).toList
    = some [0x2001, 0xdb8, 1, 2, 3, 4, 5, 6] :=
  ipv6Parser_serializer_nocompress (by decide) (by decide) (by decide)

/-- 0 が一つだけなら圧縮しない。 -/
example : ipv6Parser (ipv6Serializer [1, 0, 2, 3, 4, 5, 6, 7]).toList
    = some [1, 0, 2, 3, 4, 5, 6, 7] :=
  ipv6Parser_serializer_nocompress (by decide) (by decide) (by decide)

end Url
