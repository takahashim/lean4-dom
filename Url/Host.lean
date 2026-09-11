import Url.Ipv4
import Url.Ipv6
import Url.Percent

/-!
# host parser

WHATWG URL Standard §3.2 の "host parser"、"opaque-host parser"、"domain parser"、
および §3.5 の host serializer。

## IDNA を抽象化する

"domain parser" は Unicode の ToASCII（UTS #46）に委ねている。
UTS #46 は数千 code point の写像表と Punycode と正規化と bidi/joiner の検査で、
忠実に写すには Unicode のデータを model に埋め込むことになる。
仕様自身が別仕様へ委譲していること、この model の他の hook（custom element の steps、
MutationObserver の callback）と同じ扱いであることから、
**`DomainToASCII` を外から与える関数として受け取り**、host parser 側をそれに対して相対的に定義する。

差分テストでは実装（Dommy の `Internal::IDNA`）を渡して突き合わせる。
ASCII だけの domain については `asciiDomainToASCII` が仕様どおりに振る舞うので、
そちらは model だけで閉じている。
-/

namespace Url

open Infra

/-- URL Standard §3.2 の host。 -/
inductive Host where
  /-- domain（ASCII に直した後の文字列）。 -/
  | domain (s : String)
  /-- IPv4 address。 -/
  | ipv4 (addr : Nat)
  /-- IPv6 address。 -/
  | ipv6 (addr : Ipv6)
  /-- opaque host。 -/
  | opaque (s : String)
  /-- empty host。 -/
  | empty
deriving DecidableEq, Repr, Inhabited

/-- URL Standard §1.3 forbidden host code point。 -/
def isForbiddenHost (c : Char) : Bool :=
  c.toNat == 0x00 || c.toNat == 0x09 || c.toNat == 0x0A || c.toNat == 0x0D ||
    c == ' ' || c == '#' || c == '/' || c == ':' || c == '<' || c == '>' ||
    c == '?' || c == '@' || c == '[' || c == '\\' || c == ']' || c == '^' || c == '|'

/-- URL Standard §1.3 forbidden domain code point。 -/
def isForbiddenDomain (c : Char) : Bool :=
  isForbiddenHost c || isC0Control c || c == '%' || c.toNat == 0x7F

/-- URL Standard §3.2 "opaque-host parser"。 -/
def opaqueHostParser (input : List Char) : Option Host :=
  if input.any isForbiddenHost then none
  -- 空の結果は empty host である。`.opaque ""` と二通りに表さないようにしておく
  -- （`cannotHaveCredentials` など、empty host を名指しで見る述語があるため）。
  else some (if input.isEmpty then .empty
             else .opaque (String.ofList (utf8PercentEncode c0ControlSet input)))

/--
ASCII だけからなる domain に対する "domain parser"。

UTS #46 の写像は ASCII では ASCII lowercase に一致し、Punycode も走らない。
`xn--` で始まる label は Punycode の decode が要るので、ここでは扱わない
（`domainToASCII` を外から与えればそちらが扱う）。
-/
def asciiDomainToASCII (domain : List Char) : Option String :=
  if domain.all (fun c => isAscii c) then
    asciiDomainCheck (asciiLowercase (String.ofList domain))
  else none
where
  /-- domain parser の step 3-4：空と forbidden domain code point を弾く。 -/
  asciiDomainCheck (lowered : String) : Option String :=
    if lowered.isEmpty then none
    else if lowered.any isForbiddenDomain then none
    else some lowered

/--
URL Standard §3.2 "host parser"。

`domainToASCII` は "domain parser" の ToASCII。ASCII だけの domain なら
`asciiDomainToASCII` で足りる（この model だけで閉じる）。
非 ASCII を含む場合は外から実装を与える。
-/
def hostParser (domainToASCII : List Char → Option String)
    (input : List Char) (isOpaque : Bool := false) : Option Host :=
  match input with
  -- step 1：U+005B で始まるなら IPv6
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: revInner => (ipv6Parser revInner.reverse).map Host.ipv6
    | _ => none
  | _ =>
    -- step 2
    if isOpaque then opaqueHostParser input
    -- step 3 は「input は空でない」という assert である。
    -- 空の host は basic URL parser が別に作るもので、この parser の結果ではない。
    -- 呼ばれてしまった場合は失敗にする（差分の相手も同じ）。
    else if input.isEmpty then none
    else
      -- step 5：percent-decode してから UTF-8 として読む
      let domain := percentDecodeToString input
      -- step 6-7
      match domainToASCII domain with
      | none => none
      | some asciiDomain =>
        -- step 8：数字で終わるなら IPv4 として読む
        if endsInANumber asciiDomain.toList then
          (ipv4Parser asciiDomain.toList).map Host.ipv4
        else some (.domain asciiDomain)

/-- URL Standard §3.5 host serializer。 -/
def hostSerializer : Host → String
  | .domain s => s
  | .ipv4 addr => ipv4Serializer addr
  | .ipv6 addr => "[" ++ ipv6Serializer addr ++ "]"
  | .opaque s => s
  | .empty => ""

/-! ## 性質 -/

/-- opaque host が返るなら、入力に forbidden host code point は無い。 -/
theorem opaqueHostParser_no_forbidden {input : List Char} {h : Host}
    (hp : opaqueHostParser input = some h) : input.any isForbiddenHost = false := by
  unfold opaqueHostParser at hp
  split at hp
  · simp at hp
  · next hn => simpa using hn

/-- ASCII だけの domain parser が返す文字列には forbidden domain code point が無い。 -/
theorem asciiDomainToASCII_no_forbidden {domain : List Char} {s : String}
    (h : asciiDomainToASCII domain = some s) : s.any isForbiddenDomain = false := by
  unfold asciiDomainToASCII at h
  split at h
  · unfold asciiDomainToASCII.asciiDomainCheck at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · next _ hf =>
        rw [← Option.some.inj h]
        simpa using hf
  · simp at h

/-- domain parser が返す文字列は空でない。 -/
theorem asciiDomainToASCII_ne_empty {domain : List Char} {s : String}
    (h : asciiDomainToASCII domain = some s) : s.isEmpty = false := by
  unfold asciiDomainToASCII at h
  split at h
  · unfold asciiDomainToASCII.asciiDomainCheck at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · next he _ =>
        rw [← Option.some.inj h]
        simpa using he
  · simp at h

end Url
