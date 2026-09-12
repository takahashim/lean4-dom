import Infra.Ascii

/-!
# IPv6 parser

WHATWG URL Standard §3.3 の "IPv6 parser" と、§3.5 の IPv6 serializer
（"find the IPv6 address compressed piece index" を含む）。

仕様は pointer を進める while loop で書かれているが、pointer が戻るのは
IPv4-in-IPv6 の分岐（読んだ hex digit のぶんだけ戻す）だけである。
そこは「読む前の入力」を持っておけば済むので、
残りの入力に対する well-founded な再帰で書ける。
-/

namespace Url

open Infra

/-- IPv6 address。8 個の piece。各 piece は 16 bit。 -/
abbrev Ipv6 := List Nat

/-- 全部 0 の address。 -/
def ipv6Zero : Ipv6 := [0, 0, 0, 0, 0, 0, 0, 0]

/-- 先頭から高々 `n` 個の hex digit を読む。返すのは (値, 読んだ個数, 残り)。 -/
def takeHex : Nat → List Char → Nat × Nat × List Char
  | 0, l => (0, 0, l)
  | _ + 1, [] => (0, 0, [])
  | n + 1, c :: rest =>
    match hexValue c with
    | none => (0, 0, c :: rest)
    | some v =>
      let (v', len, rem) := takeHex n rest
      (v * 16 ^ len + v', len + 1, rem)

/-- 先頭の 10 進 digit を読み切る。返すのは (値, 個数, 残り)。 -/
def takeDec : List Char → Nat → Nat → Nat × Nat × List Char
  | [], acc, len => (acc, len, [])
  | c :: rest, acc, len =>
    match digitValue c with
    | none => (acc, len, c :: rest)
    | some v => takeDec rest (acc * 10 + v) (len + 1)

/--
IPv6 parser の IPv4-in-IPv6 の部分。

dotted decimal を高々 4 個読み、`pieceIndex` から 2 piece に詰める
（`numbersSeen` が 2 または 4 になるたびに piece が進む）。
読み終わりに `numbersSeen` が 4 でなければ失敗する。

`fuel` は読む個数の上限で、4 で足りる。`numbersSeen` は毎回 1 増え、
4 を超えると仕様が失敗にするからである。
-/
def ipv4InIpv6 : Nat → List Char → Ipv6 → Nat → Nat → Option Ipv6
  | 0, input, address, _, numbersSeen =>
    if input.isEmpty && numbersSeen == 4 then some address else none
  | fuel + 1, input, address, pieceIndex, numbersSeen =>
    match input with
    | [] => if numbersSeen == 4 then some address else none
    | _ =>
      -- numbersSeen > 0 なら区切りの U+002E が要る
      let afterDot :=
        if numbersSeen > 0 then
          match input with
          | '.' :: t => if numbersSeen < 4 then some t else none
          | _ => none
        else some input
      match afterDot with
      | none => none
      | some s =>
        match s with
        | [] => none
        | c :: _ =>
          -- 先頭が digit でなければ失敗
          if !isAsciiDigit c then none
          else
            let (piece, len, rest) := takeDec s 0 0
            -- 仕様は「ipv4Piece が 0 のときに続きがあれば失敗」と書く。
            -- 先頭が 0 で 2 桁以上、と同じことである。
            if piece > 255 then none
            else if len > 1 && s.head? == some '0' then none
            else
              let idx := pieceIndex + numbersSeen / 2
              let address := address.set idx (address.getD idx 0 * 0x100 + piece)
              ipv4InIpv6 fuel rest address pieceIndex (numbersSeen + 1)

/--
IPv6 parser の while loop（step 5）。

各 piece を読む。`fuel` は piece の個数の上限で、9 あれば足りる
（piece は高々 8 個、加えて compress の分岐が 1 回）。
`input` は「この piece を読み始める位置」で、IPv4-in-IPv6 の分岐が
pointer を戻す（step 5.5.2）のはここへ戻ることに当たる。
-/
def ipv6Loop : Nat → List Char → Ipv6 → Nat → Option Nat → Option (Ipv6 × Nat × Option Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, input, address, pieceIndex, compress =>
    match input with
    | [] => some (address, pieceIndex, compress)
    | _ =>
      -- step 5.1
      if pieceIndex == 8 then none
      else
        match input with
        -- step 5.2：圧縮は一度だけ
        | ':' :: rest =>
          if compress.isSome then none
          else ipv6Loop fuel rest address (pieceIndex + 1) (some (pieceIndex + 1))
        | _ =>
          -- step 5.3-5.4：hex digit を高々 4 個
          let (value, len, rest) := takeHex 4 input
          match rest with
          -- step 5.5：IPv4-in-IPv6。pointer を len だけ戻すので `input` から読み直す。
          | '.' :: _ =>
            if len == 0 then none
            else if pieceIndex > 6 then none
            else match ipv4InIpv6 4 input address pieceIndex 0 with
              | none => none
              | some address => some (address, pieceIndex + 2, compress)
          -- step 5.6：区切りの U+003A。その後が EOF なら失敗。
          | ':' :: rest' =>
            if rest'.isEmpty then none
            else
              ipv6Loop fuel rest' (address.set pieceIndex value) (pieceIndex + 1) compress
          -- step 5.7：EOF 以外が残っていたら失敗
          | [] => some (address.set pieceIndex value, pieceIndex + 1, compress)
          | _ => none

/-- step 6：圧縮した分を右へ寄せる。 -/
def ipv6Expand (address : Ipv6) (pieceIndex : Nat) (compress : Nat) : Ipv6 :=
  let swaps := pieceIndex - compress
  let kept := address.take compress
  let moved := (address.drop compress).take swaps
  kept ++ List.replicate (8 - compress - swaps) 0 ++ moved

/-- URL Standard §3.3 "IPv6 parser"。失敗したら `none`。 -/
def ipv6Parser (input : List Char) : Option Ipv6 :=
  -- step 5 の前：先頭が U+003A なら "::" でなければならない
  match input with
  | ':' :: ':' :: rest =>
    match ipv6Loop 9 rest ipv6Zero 1 (some 1) with
    | none => none
    | some (address, pieceIndex, compress) => ipv6Finish address pieceIndex compress
  | ':' :: _ => none
  | _ =>
    match ipv6Loop 9 input ipv6Zero 0 none with
    | none => none
    | some (address, pieceIndex, compress) => ipv6Finish address pieceIndex compress
where
  /-- step 6-8。 -/
  ipv6Finish (address : Ipv6) (pieceIndex : Nat) (compress : Option Nat) : Option Ipv6 :=
    match compress with
    | some c => some (ipv6Expand address pieceIndex c)
    | none => if pieceIndex == 8 then some address else none


/-!
## 性質

`Ipv6` は `List Nat` なので、長さも各 piece の範囲も型では言えない。
`ipv6Serializer` は 8 piece を前提に `i == 7` で区切りを落とし、
`ipv6Expand` は `8 - compress - swaps` と自然数減算をするので、
parser が 8 piece を返すことと、どの piece も 16 bit に収まることを
言明しておく必要がある。
-/

/-- `takeHex` が読む個数は上限以下。 -/
theorem takeHex_len : ∀ (n : Nat) (l : List Char), (takeHex n l).2.1 ≤ n
  | 0, l => by simp [takeHex]
  | _ + 1, [] => by simp [takeHex]
  | n + 1, c :: rest => by
    rw [takeHex]
    split
    · simp
    · show (takeHex n rest).2.1 + 1 ≤ n + 1
      have := takeHex_len n rest
      omega

/-- `takeHex` が読む値は桁数ぶんに収まる。 -/
theorem takeHex_lt : ∀ (n : Nat) (l : List Char), (takeHex n l).1 < 16 ^ (takeHex n l).2.1
  | 0, l => by simp [takeHex]
  | _ + 1, [] => by simp [takeHex]
  | n + 1, c :: rest => by
    rw [takeHex]
    split
    · simp
    · next v hv =>
      have hlt := hexValue_lt hv
      have hrec := takeHex_lt n rest
      have hpow : 0 < 16 ^ (takeHex n rest).2.1 := Nat.pow_pos (by omega)
      simp only []
      rw [Nat.pow_succ]
      calc v * 16 ^ (takeHex n rest).2.1 + (takeHex n rest).1
          < v * 16 ^ (takeHex n rest).2.1 + 16 ^ (takeHex n rest).2.1 := by omega
        _ = (v + 1) * 16 ^ (takeHex n rest).2.1 := by rw [Nat.succ_mul]
        _ ≤ 16 * 16 ^ (takeHex n rest).2.1 := Nat.mul_le_mul_right _ (by omega)
        _ = 16 ^ (takeHex n rest).2.1 * 16 := by rw [Nat.mul_comm]

/-- `takeHex 4` が読む値は 16 bit に収まる。 -/
theorem takeHex4_lt (l : List Char) : (takeHex 4 l).1 < 65536 := by
  have h1 := takeHex_lt 4 l
  have h2 := takeHex_len 4 l
  calc (takeHex 4 l).1 < 16 ^ (takeHex 4 l).2.1 := h1
    _ ≤ 16 ^ 4 := Nat.pow_le_pow_right (by omega) h2
    _ = 65536 := by decide

/-- 書き込む値が 16 bit に収まるなら、`set` は範囲を保つ。 -/
theorem set_lt {a : Ipv6} {i v : Nat} (ha : ∀ p ∈ a, p < 65536) (hv : v < 65536) :
    ∀ p ∈ a.set i v, p < 65536 := by
  intro p hp
  rcases List.mem_or_eq_of_mem_set hp with h | h
  · exact ha p h
  · omega

theorem getD_set_self (l : List Nat) (i v d : Nat) (h : i < l.length) :
    (l.set i v).getD i d = v := by simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_other (l : List Nat) (i j v d : Nat) (h : i ≠ j) :
    (l.set i v).getD j d = l.getD j d := by simp [List.getD_eq_getElem?_getD, h]

/-- `ipv4InIpv6` は piece を書き換えるだけで、個数を変えない。 -/
theorem ipv4InIpv6_length : ∀ (fuel : Nat) (input : List Char) (a : Ipv6) (pi ns : Nat) (a' : Ipv6),
    ipv4InIpv6 fuel input a pi ns = some a' → a'.length = a.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro input a pi ns a' h
    simp only [ipv4InIpv6] at h
    split at h
    · exact congrArg List.length (Option.some.inj h).symm
    · simp at h
  | succ f ih =>
    intro input a pi ns a' h
    simp only [ipv4InIpv6] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | exact congrArg List.length (Option.some.inj h).symm
      | (rw [ih _ _ _ _ _ h]; simp)
      | (simp at h; exact congrArg List.length h.symm)

/--
`ipv6Loop` は個数を変えず、`pieceIndex` は 8 以下に留まり、
圧縮位置は `pieceIndex` を超えない。
-/
theorem ipv6Loop_inv : ∀ (fuel : Nat) (input : List Char) (a : Ipv6) (pi : Nat)
    (co : Option Nat) (a' : Ipv6) (pi' : Nat) (co' : Option Nat),
    ipv6Loop fuel input a pi co = some (a', pi', co') →
    pi ≤ 8 → (∀ c, co = some c → c ≤ pi) →
    a'.length = a.length ∧ pi' ≤ 8 ∧ (∀ c, co' = some c → c ≤ pi') := by
  intro fuel
  induction fuel with
  | zero => intro input a pi co a' pi' co' h _ _; simp [ipv6Loop] at h
  | succ f ih =>
    intro input a pi co a' pi' co' h hpi hco
    simp only [ipv6Loop] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨by simp, by first | omega | (simp_all; omega),
           by intro c hc; have := hco c hc; omega⟩)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         refine ⟨ipv4InIpv6_length 4 input a pi 0 _ (by assumption),
           by first | omega | (simp_all; omega), ?_⟩
         intro c hc; have := hco c hc; omega)
      | (have hx := ih _ _ _ _ _ _ _ h (by first | omega | (simp_all; omega))
              (by intro c hc; simp at hc; omega)
         exact ⟨by simpa using hx.1, hx.2.1, hx.2.2⟩)
      | (have hx := ih _ _ _ _ _ _ _ h (by first | omega | (simp_all; omega))
              (by intro c hc; have := hco c hc; omega)
         exact ⟨by simpa using hx.1, hx.2.1, hx.2.2⟩)

/-- `ipv6Expand` は 8 piece を保つ。圧縮位置が `pieceIndex` 以下で、`pieceIndex` が 8 以下なら。 -/
theorem ipv6Expand_length {a : Ipv6} {pi co : Nat} (ha : a.length = 8)
    (hco : co ≤ pi) (hpi : pi ≤ 8) : (ipv6Expand a pi co).length = 8 := by
  unfold ipv6Expand
  simp [List.length_append, List.length_take, List.length_drop, ha]
  omega

/-- step 6-8 は 8 piece を保つ。 -/
theorem ipv6Finish_length {a : Ipv6} {pi : Nat} {co : Option Nat} {a' : Ipv6}
    (ha : a.length = 8) (hpi : pi ≤ 8) (hco : ∀ c, co = some c → c ≤ pi)
    (h : ipv6Parser.ipv6Finish a pi co = some a') : a'.length = 8 := by
  rw [ipv6Parser.ipv6Finish.eq_def] at h
  split at h
  · next c =>
    rw [← Option.some.inj h]
    exact ipv6Expand_length ha (hco c rfl) hpi
  · split at h
    · rw [← Option.some.inj h]; exact ha
    · simp at h

/--
**IPv6 parser が返す address は必ず 8 piece である。**

`ipv6Serializer` は 8 piece を前提に `i == 7` で区切りを落とすので、これが要る。
-/
theorem ipv6Parser_length {input : List Char} {a : Ipv6}
    (h : ipv6Parser input = some a) : a.length = 8 := by
  unfold ipv6Parser at h
  have hz : ipv6Zero.length = 8 := by simp [ipv6Zero]
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (rename_i hr
       obtain ⟨hl, hpi, hc⟩ := ipv6Loop_inv 9 _ ipv6Zero 1 (some 1) _ _ _ hr
         (by omega) (by intro c hc; simp at hc; omega)
       exact ipv6Finish_length (by omega) hpi hc h)
    | (rename_i hr
       obtain ⟨hl, hpi, hc⟩ := ipv6Loop_inv 9 _ ipv6Zero 0 none _ _ _ hr
         (by omega) (by intro c hc; simp at hc)
       exact ipv6Finish_length (by omega) hpi hc h)

/-! ### piece の範囲

長さの次は各 piece が 16 bit に収まること。hex を読む枝は `takeHex4_lt` で足りるが、
IPv4-in-IPv6 の枝は `old * 0x100 + piece` と積み上げるので、
「まだ書いていない piece は 0」「いま書いている piece は 8 bit」を記帳する必要がある。
`numbersSeen` の偶奇がその二つを行き来する。
-/

theorem ipv6Zero_getD : ∀ j, ipv6Zero.getD j 0 = 0
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => rfl

/-- 書き込んだ場所を読み直すと、書いた値か（範囲外なら）既定値である。 -/
theorem getD_set_lt (l : List Nat) (i v b : Nat) (hv : v < b) (hb : 0 < b) :
    (l.set i v).getD i 0 < b := by
  by_cases h : i < l.length
  · rw [getD_set_self l i v 0 h]; exact hv
  · rw [List.getD_eq_getElem?_getD]
    have : (l.set i v)[i]? = none := by
      apply List.getElem?_eq_none
      simpa using h
    rw [this]
    exact hb

/--
`ipv4InIpv6` の 1 歩。

`ns` 番目の 10 進を書き込んでも、piece は 16 bit に収まり、
まだ書いていない piece は 0 のまま、いま書いた piece は 8 bit に収まる。
-/
theorem ipv4InIpv6_step {a : Ipv6} {pi ns piece : Nat} (hp : piece ≤ 255)
    (ha : ∀ p ∈ a, p < 65536)
    (hz : ∀ j, pi + (ns + 1) / 2 ≤ j → a.getD j 0 = 0)
    (hb : a.getD (pi + ns / 2) 0 < 256) :
    (∀ p ∈ a.set (pi + ns / 2) (a.getD (pi + ns / 2) 0 * 0x100 + piece), p < 65536) ∧
    (∀ j, pi + (ns + 1 + 1) / 2 ≤ j →
      (a.set (pi + ns / 2) (a.getD (pi + ns / 2) 0 * 0x100 + piece)).getD j 0 = 0) ∧
    (a.set (pi + ns / 2) (a.getD (pi + ns / 2) 0 * 0x100 + piece)).getD (pi + (ns + 1) / 2) 0
      < 256 := by
  refine ⟨set_lt ha (by omega), ?_, ?_⟩
  · intro j hj
    rw [getD_set_other _ _ _ _ _ (show pi + ns / 2 ≠ j by omega)]
    exact hz j (by omega)
  · by_cases hpar : ns % 2 = 0
    · have hidx : pi + (ns + 1) / 2 = pi + ns / 2 := by omega
      rw [hidx, hz (pi + ns / 2) (by omega)]
      exact getD_set_lt _ _ _ _ (by omega) (by omega)
    · rw [getD_set_other _ _ _ _ _ (show pi + ns / 2 ≠ pi + (ns + 1) / 2 by omega)]
      have := hz (pi + (ns + 1) / 2) (by omega)
      omega

/-- `ipv4InIpv6` が返す address の piece は 16 bit に収まる。 -/
theorem ipv4InIpv6_lt : ∀ (fuel : Nat) (input : List Char) (a : Ipv6) (pi ns : Nat) (a' : Ipv6),
    ipv4InIpv6 fuel input a pi ns = some a' →
    (∀ p ∈ a, p < 65536) →
    (∀ j, pi + (ns + 1) / 2 ≤ j → a.getD j 0 = 0) →
    a.getD (pi + ns / 2) 0 < 256 →
    ∀ p ∈ a', p < 65536 := by
  intro fuel
  induction fuel with
  | zero =>
    intro input a pi ns a' h ha _ _
    simp only [ipv4InIpv6] at h
    split at h
    · rw [← Option.some.inj h]; exact ha
    · simp at h
  | succ f ih =>
    intro input a pi ns a' h ha hz hb
    simp only [ipv4InIpv6] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (rw [← Option.some.inj h]; exact ha)
      | (refine ih _ _ _ _ _ h ?_ ?_ ?_
         · exact (ipv4InIpv6_step (by omega) ha hz hb).1
         · exact (ipv4InIpv6_step (by omega) ha hz hb).2.1
         · exact (ipv4InIpv6_step (by omega) ha hz hb).2.2)

/-- `ipv6Loop` が返す address の piece は 16 bit に収まる。 -/
theorem ipv6Loop_lt : ∀ (fuel : Nat) (input : List Char) (a : Ipv6) (pi : Nat)
    (co : Option Nat) (a' : Ipv6) (pi' : Nat) (co' : Option Nat),
    ipv6Loop fuel input a pi co = some (a', pi', co') →
    (∀ p ∈ a, p < 65536) → (∀ j, pi ≤ j → a.getD j 0 = 0) →
    ∀ p ∈ a', p < 65536 := by
  intro fuel
  induction fuel with
  | zero => intro input a pi co a' pi' co' h _ _; simp [ipv6Loop] at h
  | succ f ih =>
    intro input a pi co a' pi' co' h ha hz
    simp only [ipv6Loop] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         first
           | exact ha
           | exact set_lt ha (takeHex4_lt _)
           | (refine ipv4InIpv6_lt 4 _ a pi 0 _ (by assumption) ha
                (fun j hj => hz j (by omega)) ?_
              have := hz (pi + 0 / 2) (by omega)
              omega))
      | (exact ih _ _ _ _ _ _ _ h ha (fun j hj => hz j (by omega)))
      | (refine ih _ _ _ _ _ _ _ h (set_lt ha (takeHex4_lt _)) (fun j hj => ?_)
         rw [getD_set_other _ _ _ _ _ (show pi ≠ j by omega)]
         exact hz j (by omega))

/-- `ipv6Expand` は 0 を挟むだけなので範囲を保つ。 -/
theorem ipv6Expand_lt {a : Ipv6} {pi co : Nat} (ha : ∀ p ∈ a, p < 65536) :
    ∀ p ∈ ipv6Expand a pi co, p < 65536 := by
  intro p hp
  unfold ipv6Expand at hp
  simp only [List.mem_append] at hp
  rcases hp with (h | h) | h
  · exact ha p (List.mem_of_mem_take h)
  · rw [List.eq_of_mem_replicate h]; omega
  · exact ha p (List.mem_of_mem_drop (List.mem_of_mem_take h))

/-- step 6-8 は範囲を保つ。 -/
theorem ipv6Finish_lt {a : Ipv6} {pi : Nat} {co : Option Nat} {a' : Ipv6}
    (ha : ∀ p ∈ a, p < 65536) (h : ipv6Parser.ipv6Finish a pi co = some a') :
    ∀ p ∈ a', p < 65536 := by
  rw [ipv6Parser.ipv6Finish.eq_def] at h
  split at h
  · rw [← Option.some.inj h]; exact ipv6Expand_lt ha
  · split at h
    · rw [← Option.some.inj h]; exact ha
    · simp at h

/--
**IPv6 parser が返す piece はどれも 16 bit に収まる。**

`ipv6Serializer` は piece を 16 進 4 桁までとして書くので、これが要る。
-/
theorem ipv6Parser_lt {input : List Char} {a : Ipv6} (h : ipv6Parser input = some a) :
    ∀ p ∈ a, p < 65536 := by
  unfold ipv6Parser at h
  have hz : ∀ p ∈ ipv6Zero, p < 65536 := by decide
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (rename_i hr
       exact ipv6Finish_lt (ipv6Loop_lt 9 _ ipv6Zero _ _ _ _ _ hr hz
         (fun j _ => ipv6Zero_getD j)) h)

/-! ## serializer -/

/-- URL Standard §3.5 "find the IPv6 address compressed piece index"。 -/
def ipv6CompressIndex (address : Ipv6) : Option Nat :=
  let final := address.zipIdx.foldl
    (fun (st : Option Nat × Nat × Option Nat × Nat) (pi : Nat × Nat) =>
      let (longestIndex, longestSize, foundIndex, foundSize) := st
      if pi.1 != 0 then
        -- 0 の並びが切れた。いままでで一番長ければ覚える。
        if foundSize > longestSize then (foundIndex, foundSize, none, 0)
        else (longestIndex, longestSize, none, 0)
      else
        -- 0 が続いている。始まりを覚えて長さを伸ばす。
        (longestIndex, longestSize,
          (match foundIndex with | none => some pi.2 | some i => some i), foundSize + 1))
    (none, 1, none, 0)
  let (longestIndex, longestSize, foundIndex, foundSize) := final
  if foundSize > longestSize then foundIndex else longestIndex

/-- 小文字 16 進で、余分な 0 を付けずに表す。 -/
def toHexString (n : Nat) : String :=
  if n == 0 then "0" else String.ofList (go n [])
where
  go : Nat → List Char → List Char
    | 0, acc => acc
    | n + 1, acc =>
      let d := (n + 1) % 16
      go ((n + 1) / 16) (Char.ofNat (if d < 10 then 0x30 + d else 0x61 + d - 10) :: acc)

/-- URL Standard §3.5 IPv6 serializer。 -/
def ipv6Serializer (address : Ipv6) : String :=
  let compress := ipv6CompressIndex address
  let rec go : List (Nat × Nat) → Bool → String
    | [], _ => ""
    | (p, i) :: rest, ignore0 =>
      if ignore0 && p == 0 then go rest true
      else
        let ignore0 := false
        if compress == some i then
          (if i == 0 then "::" else ":") ++ go rest true
        else
          toHexString p ++ (if i == 7 then "" else ":") ++ go rest ignore0
  go address.zipIdx false

end Url
