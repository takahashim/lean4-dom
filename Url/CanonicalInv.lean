import Url.Roundtrip.Canonical
import Url.HostRoundtrip

/-!
# parser の出力が canonical であるための不変条件

`basicUrlParse_valid` は「parse が成功したら `ValidUrl`」を言う。ここでは同じ形で
「parse が成功したら `canonicalUrl`」を言うための state 不変条件 `CInv` を立てる。
これが閉じると、parse の像は `ValidUrl ∧ canonicalUrl` にちょうど一致する
（`⊇` は `roundtrip_canonical`）。

## `PInv` との違い

**`CInv` は残りの入力を引数に取る。** `canonicalUrl` の条件のうち二つは、
その根拠が `ctx` ではなく入力にあるためである。

* opaque path の末尾は space でない。opaque path state は、次の文字が `?` か `#` で
  なければ space をそのまま積む。EOF の直前に space が来ないのは、前処理が末尾の
  C0 control or space を落とすからである（`preprocess_getLast`）。
* host が空なら credentials は持てない。authority state は `@` の後の buffer が空なら
  失敗し、そうでなければ buffer を**入力に戻して** host state に読み直させる。
  host state から見ると、根拠は「残りの入力の先頭が terminator でない」という形で届く。

`PInv` は拡張せず、独立に立てる。`PInv` から借りる事実（scheme がまだ空、
file slash state の scheme は `file`、など）は `CInv` に複製してある。
既存の `basicUrlParse_valid` の証明には触れずに済む。

## field の裏づけ

各 field は、証明に入る前に boolean にして parser の途中状態すべてで検査した。
WPT の 820 件と、ランダムな入力 12 万件で違反は無かった。

## ToASCII

いまは `ctx.toAscii = asciiDomainToASCII` に固定している（`toAsciiDef`）。
host の条件は `hostParser_idem` に乗るが、それが既定の ToASCII についての定理だからである。
一般の ToASCII に広げるには冪等性（`t x = some a → t a.toList = some a`）を
仮定にすればよいはずで、その時はこの field を差し替える。
-/

namespace Url

open Infra

/-! ## state の分類 -/

/--
url が scheme 以外まだ何も持たない state。

scheme を書き換える state（scheme / relative / file）はどれもここに入る。
scheme が変わると special かどうかが変わり、query の encode set や
host の読み方が変わるので、そのとき他の成分が空であることが要る。
-/
def earlyState : PState → Bool
  | .schemeStart | .scheme | .noScheme | .specialRelativeOrAuthority | .pathOrAuthority
  | .relative | .relativeSlash | .specialAuthoritySlashes | .specialAuthorityIgnoreSlashes
  | .file => true
  | _ => false

/-- host がまだ null の state。`PInv` の `hostNull` に file state を足したもの。 -/
def hostOpen : PState → Bool
  | .authority | .host => true
  | st => earlyState st

/-- path も query も fragment もまだ書かれていない state。 -/
def pathFresh : PState → Bool
  | .authority | .host | .port | .fileSlash | .fileHost | .pathStart => true
  | st => earlyState st

/--
scheme が確定している state。

scheme start / scheme / no scheme state ではまだ空で、relative state と file state は
入ってから書く。
-/
def schemeSet : PState → Bool
  | .schemeStart | .scheme | .noScheme | .relative | .file => false
  | _ => true

/-- buffer が空の state。 -/
def emptyBuf : PState → Bool
  | .schemeStart | .noScheme | .specialRelativeOrAuthority | .pathOrAuthority | .relative
  | .relativeSlash | .specialAuthoritySlashes | .specialAuthorityIgnoreSlashes | .file
  | .fileSlash | .pathStart | .opaquePath | .fragment => true
  | _ => false

/-- path が確定した後の state。ここでは path が空なのは host を持つ非 special な URL だけ。 -/
def termState : PState → Bool
  | .opaquePath | .query | .fragment => true
  | _ => false

/-- 入力の末尾が space でないことを持ち回る state。scheme state から opaque path state まで。 -/
def inputEndState : PState → Bool
  | .schemeStart | .scheme | .opaquePath => true
  | _ => false

/-- host が決まっている state。port state と path start state へは host を書いてからしか来ない。 -/
def hostSet : PState → Bool
  | .port | .pathStart => true
  | _ => false

/-! ## 成分の条件

`canonicalUrl` の連言を、`CInv` の field として持ちやすい形に切り出したもの。
-/

/--
path の条件。`canonicalUrl` の path の連言から、opaque path の末尾の space を除いたもの。

末尾の space だけは入力を見ないと言えないので、`CInv.trailing` に分けてある。
-/
def pathCanon (special : Bool) : Path → Bool
  | .opaque o =>
    encodedWith c0ControlSet o && o.toList.all (fun c => c != '?' && c != '#') &&
      !(o.toList.head? == some '/')
  | .list segs =>
    segs.all fun seg =>
      encodedWith pathSet seg && !isSingleDot seg.toList && !isDoubleDot seg.toList &&
        (!special || seg.toList.all (fun c => c != '\\'))

/-- file URL の先頭 segment が Windows drive letter なら正規化されている。 -/
def driveOk (scheme : String) : Path → Bool
  | .list (seg :: _) =>
    scheme != "file" || !isWindowsDrive seg.toList || isNormalizedWindowsDrive seg.toList
  | _ => true

/-! ## 不変条件 -/

/--
parse の途中の `(state, 残りの入力, ctx)` が満たすべきこと。

`canonicalUrl` の各条件を state に応じて緩めたものと、それを保つための足場からなる。
`over = none` を要求しているので、`basicUrlParse` についての不変条件である。
-/
structure CInv (base : Option Url) (st : PState) (input : List Char) (ctx : PCtx) : Prop where
  /-- state override は付いていない。 -/
  noOverride : ctx.over = none
  /-- ToASCII は既定のもの（この file の先頭の説明を参照）。 -/
  toAsciiDef : ctx.toAscii = asciiDomainToASCII
  /-- base は妥当な URL record である。 -/
  baseValid : ∀ b, base = some b → ValidUrl b
  /-- base は canonical である。base から写す成分はこれで済む。 -/
  baseCanon : ∀ b, base = some b → canonicalUrl b = true
  /--
  base の成分を写す state に入るのは、base の scheme が `file` でないときだけ。

  relative state が `url.scheme := base.scheme` と書くので、
  host state まで `notFile` を保つのにこれが要る。
  -/
  baseNotFile : usesBasePath st = true → ∀ b, base = some b → b.scheme ≠ "file"
  /-- relative slash state では url の scheme は base の scheme である。 -/
  baseSchemeEq : st = .relativeSlash → ∀ b, base = some b → ctx.url.scheme = b.scheme
  /-- scheme state までは scheme も決まっていない。 -/
  schemeEmpty : freshHost st = true → ctx.url.scheme = ""
  /-- 確定した scheme は canonical である。 -/
  schemeOk : schemeSet st = true → canonicalScheme ctx.url.scheme = true
  /-- scheme state の buffer は、そのまま scheme にして canonical である。 -/
  schemeBuf : st = .scheme → canonicalScheme (String.ofList ctx.buffer) = true
  hostNone : hostOpen st = true → ctx.url.host = none
  portNone : freshPort st = true → ctx.url.port = none
  credNone : freshCred st = true → ctx.url.includesCredentials = false
  pathNil : pathFresh st = true → ctx.url.path = .list []
  queryNone : pathFresh st = true → ctx.url.query = none
  fragmentNone : pathFresh st = true → ctx.url.fragment = none
  /-- 既定 port は書かない。 -/
  portOk : ∀ p, ctx.url.port = some p → defaultPort ctx.url.scheme ≠ some p
  usernameOk : encodedWith userinfoSet ctx.url.username = true
  passwordOk : encodedWith userinfoSet ctx.url.password = true
  queryOk : ∀ q, ctx.url.query = some q →
    encodedWith (if ctx.url.isSpecial then specialQuerySet else querySet) q = true
  fragmentOk : ∀ f, ctx.url.fragment = some f → encodedWith fragmentSet f = true
  pathOk : pathCanon ctx.url.isSpecial ctx.url.path = true
  /--
  opaque path の末尾が space なら、まだ opaque path state にいて、次の文字が来る。

  opaque path state が space をそのまま積むのは、次の文字が `?` でも `#` でもないときだけ。
  -/
  trailing : ∀ o, ctx.url.path = .opaque o → o.toList.getLast? = some ' ' →
    st = .opaquePath ∧ ∃ ch t, input = ch :: t ∧ ch ≠ '?' ∧ ch ≠ '#'
  /-- opaque path の先頭は `/` でない。scheme state は `/` が続くなら opaque path へ行かない。 -/
  opaqueHead : st = .opaquePath → ctx.url.path = .opaque "" → input.head? ≠ some '/'
  /-- 入力の末尾は space でない。前処理が落としている。 -/
  inputEnd : inputEndState st = true → input.getLast? ≠ some ' '
  bufEmpty : emptyBuf st = true → ctx.buffer = []
  /-- path state の buffer は encode 済みで、special なら `\` を含まない。 -/
  pathBuf : st = .path → encodedWith pathSet (String.ofList ctx.buffer) = true ∧
    (ctx.url.isSpecial = true → ∀ c ∈ ctx.buffer, c ≠ '\\')
  driveOk : driveOk ctx.url.scheme ctx.url.path = true
  /-- path が確定した後で path が空なら、host を持つ非 special な URL である。 -/
  termNonEmpty : termState st = true → ctx.url.path = .list [] →
    ctx.url.host.isSome = true ∧ ctx.url.isSpecial = false
  hostSome : hostSet st = true → ctx.url.host.isSome = true
  /-- host を書いた後では、special な URL の host は null でない。 -/
  specialHost : hostOpen st = false → ctx.url.isSpecial = true → ctx.url.host.isSome = true
  /-- host は serialize して読み直すと戻る。 -/
  hostIdem : ∀ h, ctx.url.host = some h → h ≠ Host.empty →
    hostParser ctx.toAscii (hostSerializer h).toList (!ctx.url.isSpecial) = some h
  /-- file URL の host は `localhost` でない（file host state が empty host に直す）。 -/
  notLocal : ctx.url.scheme = "file" → ∀ h, ctx.url.host = some h →
    hostSerializer h ≠ "localhost"
  /-- §4.1「host が空なら credentials は持てない」。 -/
  emptyNoCred : ctx.url.host = some Host.empty → ctx.url.includesCredentials = false
  /-- authority state で credentials があるなら `@` を見ている。 -/
  authAt : st = .authority → ctx.url.includesCredentials = true → ctx.atSignSeen = true
  /-- authority state の buffer に terminator は無い。 -/
  authBuf : st = .authority → ∀ c ∈ ctx.buffer, isTerminator ctx.url.isSpecial (some c) = false
  /--
  host state で buffer が空のまま credentials を持つなら、次の文字は terminator でない。

  authority state の guard（`@` の後の buffer が空なら失敗）が、入力の形で届いたものである。
  これで host state が credentials を持ったまま empty host を書くことは無くなる。
  -/
  hostCred : st = .host → ctx.buffer = [] → ctx.url.includesCredentials = true →
    ∃ ch t, input = ch :: t ∧ isTerminator ctx.url.isSpecial (some ch) = false
  /-- credentials や port を書く state へは、scheme が `file` では入らない。 -/
  notFile : notFileState st = true → ctx.url.scheme ≠ "file"

/-! ## 出口 -/

/-- `canonicalUrl` を成分の条件から組む。 -/
theorem canonicalUrl_of {u : Url} {toAscii : List Char → Option String}
    (h1 : canonicalScheme u.scheme = true)
    (h2 : ∀ p, u.port = some p → defaultPort u.scheme ≠ some p)
    (h3 : encodedWith userinfoSet u.username = true)
    (h4 : encodedWith userinfoSet u.password = true)
    (h5 : ∀ q, u.query = some q →
      encodedWith (if u.isSpecial then specialQuerySet else querySet) q = true)
    (h6 : ∀ f, u.fragment = some f → encodedWith fragmentSet f = true)
    (h7 : pathCanon u.isSpecial u.path = true)
    (h7' : ∀ o, u.path = .opaque o → o.toList.getLast? ≠ some ' ')
    (h8 : u.host = none → u.path ≠ .list [])
    (h9 : u.isSpecial = true → u.path ≠ .list [])
    (h10 : ∀ h, u.host = some h → h ≠ Host.empty →
      hostParser toAscii (hostSerializer h).toList (!u.isSpecial) = some h)
    (h11 : u.scheme = "file" → ∀ h, u.host = some h → hostSerializer h ≠ "localhost")
    (h12 : driveOk u.scheme u.path = true)
    (h13 : u.isSpecial = true → u.host.isSome = true)
    (h14 : u.host = some Host.empty → u.includesCredentials = false) :
    canonicalUrl u toAscii = true := by
  simp only [canonicalUrl, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · cases hp : u.port with
    | none => trivial
    | some p => simpa using h2 p hp
  · cases hq : u.query with
    | none => trivial
    | some q => exact h5 q hq
  · cases hf : u.fragment with
    | none => trivial
    | some f => exact h6 f hf
  · cases hpa : u.path with
    | «opaque» o =>
      rw [hpa] at h7
      simp only [pathCanon, Bool.and_eq_true] at h7
      have := h7' o hpa
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
      exact ⟨⟨⟨h7.1.1, this⟩, h7.1.2⟩, by simpa using h7.2⟩
    | list segs => rw [hpa] at h7; exact h7
  · cases hh : u.host with
    | some _ => trivial
    | none =>
      cases hpa : u.path with
      | «opaque» _ => trivial
      | list segs => cases segs with
        | nil => exact absurd hpa (h8 hh)
        | cons _ _ => trivial
  · cases hs : u.isSpecial with
    | false => trivial
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      cases hpa : u.path with
      | «opaque» _ => trivial
      | list segs => cases segs with
        | nil => exact absurd hpa (h9 hs)
        | cons _ _ => trivial
  · cases hh : u.host with
    | none => trivial
    | some h =>
      cases h with
      | empty => trivial
      | _ => simp [h10 _ hh (by simp)]
  · cases hh : u.host with
    | none => trivial
    | some h =>
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true]
      by_cases hf : u.scheme = "file"
      · exact Or.inr (h11 hf h hh)
      · exact Or.inl hf
  · cases hpa : u.path with
    | «opaque» _ => trivial
    | list segs =>
      rw [hpa] at h12
      cases segs with
      | nil => trivial
      | cons _ _ => exact h12
  · cases hs : u.isSpecial with
    | false => trivial
    | true => simpa using h13 hs
  · cases hh : u.host with
    | none => trivial
    | some h =>
      by_cases he : h = Host.empty
      · subst he; simp [h14 hh]
      · simp [he]

/--
**終端で `CInv` から `canonicalUrl` が出る。**

state が `ctx.url` をそのまま返すとき（opaque path / fragment state の EOF、
special でない path start state の EOF）に使う。path が空でないことだけは
state ごとに事情が違うので、仮定として受け取る。
-/
theorem CInv.canonical {base st input ctx} (h : CInv base st input ctx)
    (ho : hostOpen st = false) (hin : st = .opaquePath → input = [])
    (hss : schemeSet st = true)
    (hpath : ctx.url.path = .list [] → ctx.url.host.isSome = true ∧ ctx.url.isSpecial = false) :
    canonicalUrl ctx.url = true := by
  refine canonicalUrl_of (h.schemeOk hss) h.portOk h.usernameOk h.passwordOk h.queryOk
    h.fragmentOk h.pathOk ?_ ?_ ?_ (h.toAsciiDef ▸ h.hostIdem) h.notLocal h.driveOk
    (h.specialHost ho) h.emptyNoCred
  · intro o hp hl
    obtain ⟨hst, ch, t, hi, -⟩ := h.trailing o hp hl
    rw [hin hst] at hi
    exact absurd hi (by simp)
  · intro hn hp
    have := (hpath hp).1
    rw [hn] at this
    exact absurd this (by simp)
  · intro hs hp
    rw [(hpath hp).2] at hs
    exact absurd hs (by simp)

/-! ## 入口 -/

/-- `dropWhile` の結果の先頭は、落とす条件を満たさない。 -/
theorem head_dropWhile {p : Char → Bool} : ∀ (l : List Char),
    ∀ c ∈ (l.dropWhile p).head?, p c = false
  | [], c, hc => by simp at hc
  | x :: xs, c, hc => by
    rw [List.dropWhile_cons] at hc
    split at hc
    · exact head_dropWhile xs c hc
    · next hx => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc; subst hc; simpa using hx

/-- 末尾が残る文字なら、`filter` した結果の末尾もその文字である。 -/
theorem getLast?_filter_of {p : Char → Bool} {l : List Char} {c : Char}
    (hl : l.getLast? = some c) (hc : p c = true) : (l.filter p).getLast? = some c := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  rw [List.filter_append]
  simp [hc]

/--
**前処理の結果の末尾は C0 control でも space でもない。**

後ろから `dropWhile` した最初の一つが末尾になり、それは tab でも newline でもないので
`stripTabNewline` を生き残る。
-/
theorem preprocess_getLast (str : String) :
    ∀ c ∈ (preprocess str).getLast?, isC0ControlOrSpace c = false := by
  intro c hc
  unfold preprocess at hc
  simp only at hc
  generalize hm : (List.dropWhile isC0ControlOrSpace str.toList).reverse.dropWhile
    isC0ControlOrSpace = m at hc
  have hh := head_dropWhile (p := isC0ControlOrSpace)
    (List.dropWhile isC0ControlOrSpace str.toList).reverse
  rw [hm] at hh
  cases m with
  | nil => simp [stripTabNewline] at hc
  | cons d rest =>
    have hd : isC0ControlOrSpace d = false := hh d rfl
    have hdl : (d :: rest).reverse.getLast? = some d := by simp
    have hkeep : (fun c : Char => !(c.toNat == 0x09 || c.toNat == 0x0A || c.toNat == 0x0D)) d
        = true := by
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le] at hd
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      omega
    unfold stripTabNewline at hc
    rw [getLast?_filter_of hdl hkeep] at hc
    simp only [Option.mem_def, Option.some.injEq] at hc
    exact hc ▸ hd

/-- 前処理の結果の末尾は space でない。 -/
theorem preprocess_getLast_ne_space (str : String) : (preprocess str).getLast? ≠ some ' ' := by
  intro h
  have := preprocess_getLast str ' ' h
  revert this; decide

/--
空の URL record から始める二か所（scheme start state と、"start over" した後の
no scheme state）は `CInv` を満たす。
-/
theorem CInv_empty {base : Option Url} {st : PState} {input : List Char}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b = true)
    (hst : st = .schemeStart ∨ st = .noScheme)
    (hin : inputEndState st = true → input.getLast? ≠ some ' ') :
    CInv base st input { url := {} } := by
  rcases hst with rfl | rfl <;>
  refine ⟨rfl, rfl, hb, hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [usesBasePath, freshHost, schemeSet, hostOpen, earlyState, freshPort, freshCred,
      pathFresh, pathCanon, Url.isSpecial, Url.includesCredentials, isSpecialScheme, defaultPort,
      encodedWith, emptyBuf, driveOk, termState, hostSet, notFileState]

theorem CInv_schemeStart {base : Option Url} {str : String}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b = true) :
    CInv base .schemeStart (preprocess str) { url := {} } :=
  CInv_empty hb hbc (Or.inl rfl) (fun _ => preprocess_getLast_ne_space str)

theorem CInv_noScheme {base : Option Url} {input : List Char}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b = true) :
    CInv base .noScheme input { url := {} } :=
  CInv_empty hb hbc (Or.inr rfl) (fun h => absurd h (by decide))

/--
`CInv` が state machine の 1 歩で保たれれば、parse の結果は `canonicalUrl` を満たす。

`basicUrlParse_valid_of_step` と同じ組み立てである。帰納段は後で `run_canonical` が与える。
-/
theorem basicUrlParse_canonical_of_step
    (hstep : ∀ (base : Option Url) (st : PState) (input : List Char) (ctx : PCtx),
      CInv base st input ctx → ∀ u, run base st input ctx = .ok u → canonicalUrl u = true)
    {input : String} {base : Option Url}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b = true)
    {u : Url} (h : basicUrlParse input base = some u) : canonicalUrl u = true := by
  unfold basicUrlParse at h
  split at h
  · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (CInv_schemeStart hb hbc) u' he
  · simp at h
  · split at h
    · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (CInv_noScheme hb hbc) u' he
    · simp at h

end Url
