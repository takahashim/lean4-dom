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
