import Url.Parser

/-!
# basic URL parser が `ValidUrl` を保つこと

`Url/Record.lean` の `ValidUrl` は URL record の局所不変条件で、
`checkValidUrl` として WPT の全 case で実行時に検査している。
この file はそれを証明に上げる。

## なぜ `ValidUrl` 単独では帰納的でないか

`ValidUrl` をそのまま「parse の途中でも成り立つ」としても、帰納法が回らない。
二か所で実際に破れるからである。

* **authority state は host が決まる前に credentials を書く。**
  `http://user@host/` を読むとき、`@` を見た時点で username に `user` が入るが、
  host はまだ null である。`nullHostNoCredentials` がその間だけ破れる。
* **`specialHasList` が保たれる理由が state に依る。**
  scheme state が `scheme := buffer` と書く瞬間、もし path が opaque だったら
  新しい scheme が special のときに破れる。実際には破れないが、その根拠は
  「opaque path を作るのは scheme state の一分岐だけで、そこから
  scheme state へ戻る道が無い」という *state についての* 事実である。

そこで state で添字づけた `PInv` を使う。上の二つをそれぞれ
「その状況になれるのは authority / host state だけ」
「opaque path を持てるのは opaquePath / query / fragment state だけ」
として持ち回る。
-/

namespace Url

/-! ## 補助

`shortenPath` / `appendSegment` / `appendOpaque` は path 以外の成分を変えず、
path の種類（opaque か list か）も変えない。`PInv` の各成分を運ぶのに要る。
-/

/-- `shortenPath` は元の record か、path の末尾を落としたものである。 -/
theorem shortenPath_spec (u : Url) :
    shortenPath u = u ∨
      ∃ segs, u.path = .list segs ∧ shortenPath u = { u with path := .list segs.dropLast } := by
  unfold shortenPath
  split
  · exact Or.inl rfl
  · next segs hp =>
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨segs, hp, rfl⟩

/-- `appendSegment` は元の record か、path の末尾に segment を足したものである。 -/
theorem appendSegment_spec (u : Url) (s : String) :
    appendSegment u s = u ∨
      ∃ segs, u.path = .list segs ∧ appendSegment u s = { u with path := .list (segs ++ [s]) } := by
  unfold appendSegment
  split
  · exact Or.inl rfl
  · next segs hp => exact Or.inr ⟨segs, hp, rfl⟩

/-- `appendOpaque` は元の record か、opaque path の末尾に文字列を足したものである。 -/
theorem appendOpaque_spec (u : Url) (s : String) :
    appendOpaque u s = u ∨
      ∃ o, u.path = .opaque o ∧ appendOpaque u s = { u with path := .opaque (o ++ s) } := by
  unfold appendOpaque
  split
  · next o hp => exact Or.inr ⟨o, hp, rfl⟩
  · exact Or.inl rfl

section
variable (u : Url) (s : String)

@[simp] theorem shortenPath_scheme : (shortenPath u).scheme = u.scheme := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem shortenPath_host : (shortenPath u).host = u.host := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem shortenPath_port : (shortenPath u).port = u.port := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem shortenPath_username : (shortenPath u).username = u.username := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem shortenPath_password : (shortenPath u).password = u.password := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]

/-- path を短くしても opaque かどうかは変わらない。 -/
@[simp] theorem shortenPath_hasOpaquePath :
    (shortenPath u).hasOpaquePath = u.hasOpaquePath := by
  rcases shortenPath_spec u with h | ⟨segs, hp, h⟩ <;> rw [h]
  simp [Url.hasOpaquePath, hp]

@[simp] theorem appendSegment_scheme : (appendSegment u s).scheme = u.scheme := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendSegment_host : (appendSegment u s).host = u.host := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendSegment_port : (appendSegment u s).port = u.port := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendSegment_username : (appendSegment u s).username = u.username := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendSegment_password : (appendSegment u s).password = u.password := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendSegment_hasOpaquePath :
    (appendSegment u s).hasOpaquePath = u.hasOpaquePath := by
  rcases appendSegment_spec u s with h | ⟨segs, hp, h⟩ <;> rw [h]
  simp [Url.hasOpaquePath, hp]

@[simp] theorem appendOpaque_scheme : (appendOpaque u s).scheme = u.scheme := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendOpaque_host : (appendOpaque u s).host = u.host := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendOpaque_port : (appendOpaque u s).port = u.port := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendOpaque_username : (appendOpaque u s).username = u.username := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendOpaque_password : (appendOpaque u s).password = u.password := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]

@[simp] theorem appendOpaque_hasOpaquePath :
    (appendOpaque u s).hasOpaquePath = u.hasOpaquePath := by
  rcases appendOpaque_spec u s with h | ⟨o, hp, h⟩ <;> rw [h]
  simp [Url.hasOpaquePath, hp]

@[simp] theorem shortenPath_isSpecial : (shortenPath u).isSpecial = u.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem shortenPath_includesCredentials :
    (shortenPath u).includesCredentials = u.includesCredentials := by
  simp [Url.includesCredentials]

@[simp] theorem appendSegment_isSpecial : (appendSegment u s).isSpecial = u.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem appendSegment_includesCredentials :
    (appendSegment u s).includesCredentials = u.includesCredentials := by
  simp [Url.includesCredentials]

@[simp] theorem appendOpaque_isSpecial : (appendOpaque u s).isSpecial = u.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem appendOpaque_includesCredentials :
    (appendOpaque u s).includesCredentials = u.includesCredentials := by
  simp [Url.includesCredentials]

end

/-! ### `portDone` -/

/-- port state の終わりは port 以外の成分を変えない。 -/
theorem portDone_spec {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ∃ p, ctx2.url = { ctx.url with port := p } ∧ ctx2.over = ctx.over := by
  unfold portDone at h
  split at h
  · exact ⟨ctx.url.port, by rw [← Option.some.inj h], by rw [← Option.some.inj h]⟩
  · split at h
    · simp at h
    · refine ⟨portOf ctx.url.scheme (portValue ctx.buffer), ?_, ?_⟩ <;>
        rw [← Option.some.inj h] <;> rfl

@[simp] theorem portDone_scheme {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.scheme = ctx.url.scheme := by
  obtain ⟨_, hu, _⟩ := portDone_spec h; rw [hu]

@[simp] theorem portDone_host {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.host = ctx.url.host := by
  obtain ⟨_, hu, _⟩ := portDone_spec h; rw [hu]

@[simp] theorem portDone_username {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.username = ctx.url.username := by
  obtain ⟨_, hu, _⟩ := portDone_spec h; rw [hu]

@[simp] theorem portDone_password {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.password = ctx.url.password := by
  obtain ⟨_, hu, _⟩ := portDone_spec h; rw [hu]

@[simp] theorem portDone_path {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.path = ctx.url.path := by
  obtain ⟨_, hu, _⟩ := portDone_spec h; rw [hu]

@[simp] theorem portDone_over {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.over = ctx.over := by
  obtain ⟨_, _, ho⟩ := portDone_spec h; exact ho

@[simp] theorem portDone_isSpecial {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.isSpecial = ctx.url.isSpecial := by
  simp [Url.isSpecial, portDone_scheme h]

@[simp] theorem portDone_hasOpaquePath {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.hasOpaquePath = ctx.url.hasOpaquePath := by
  simp [Url.hasOpaquePath, portDone_path h]

@[simp] theorem portDone_includesCredentials {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2) :
    ctx2.url.includesCredentials = ctx.url.includesCredentials := by
  simp [Url.includesCredentials, portDone_username h, portDone_password h]

/-! ### authority state の username / password 振り分け -/

/-- `userinfoStep` は username と password 以外を変えない。 -/
theorem userinfoFold_spec (buf : List Char) (p : Url × Bool) :
    ∃ un pw, (buf.foldl userinfoStep p).1 = { p.1 with username := un, password := pw } := by
  induction buf generalizing p with
  | nil => exact ⟨p.1.username, p.1.password, rfl⟩
  | cons c rest ih =>
    obtain ⟨un, pw, h⟩ := ih (userinfoStep p c)
    refine ⟨un, pw, ?_⟩
    show (rest.foldl userinfoStep (userinfoStep p c)).1 = _
    rw [h]
    unfold userinfoStep
    split
    · rfl
    · split <;> rfl

@[simp] theorem userinfoFold_scheme (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.scheme = p.1.scheme := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

@[simp] theorem userinfoFold_host (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.host = p.1.host := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

@[simp] theorem userinfoFold_port (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.port = p.1.port := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

@[simp] theorem userinfoFold_path (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.path = p.1.path := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

@[simp] theorem userinfoFold_isSpecial (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.isSpecial = p.1.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem userinfoFold_hasOpaquePath (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.hasOpaquePath = p.1.hasOpaquePath := by
  simp [Url.hasOpaquePath]

/-! ## state で添字づけた不変条件 -/

/-- opaque path を持てる state。opaque path を作る scheme state の分岐の行き先である。 -/
def mayOpaque : PState → Bool
  | .opaquePath | .query | .fragment => true
  | _ => false

/-- host が null のまま credentials を持てる state。authority state が書き、host state が閉じる。 -/
def mayCred : PState → Bool
  | .authority | .host => true
  | _ => false

/-- base の path をそのまま取り込む state。 -/
def usesBasePath : PState → Bool
  | .relative | .specialRelativeOrAuthority => true
  | _ => false

/--
parse の途中の `PCtx` が満たすべきこと。

`ValidUrl` を二か所で state に応じて緩めたものである
（この file の先頭の説明を参照）。`over = none` を要求しているので、
これは `basicUrlParse`（url を与えない普通の parse）についての不変条件である。
setter の側（`basicUrlParseOverride`）は入口ごとに事情が違うので別に扱う。
-/
structure PInv (base : Option Url) (st : PState) (ctx : PCtx) : Prop where
  /-- state override は付いていない。 -/
  noOverride : ctx.over = none
  /-- base は妥当な URL record である。 -/
  baseValid : ∀ b, base = some b → ValidUrl b
  /-- base の path を取り込む state に入るのは、その path が opaque でないときだけ。 -/
  basePathList : usesBasePath st = true → ∀ b, base = some b → b.hasOpaquePath = false
  specialHasList : ctx.url.isSpecial = true → ctx.url.hasOpaquePath = false
  nullHostNoPort : ctx.url.host = none → ctx.url.port = none
  opaqueNoCredentials : ctx.url.hasOpaquePath = true → ctx.url.includesCredentials = false
  opaqueNoPort : ctx.url.hasOpaquePath = true → ctx.url.port = none
  opaqueNoHost : ctx.url.hasOpaquePath = true → ctx.url.host = none
  /-- opaque path を持てる state は三つだけ。 -/
  opaqueState : ctx.url.hasOpaquePath = true → mayOpaque st = true
  /-- host が null のまま credentials を持てる state は二つだけ。 -/
  credState : ctx.url.host = none → ctx.url.includesCredentials = true → mayCred st = true
  /--
  port state に入るのは host が決まった後だけ。

  これが無いと `nullHostNoPort` が帰納的にならない。port を書くのは port state だけで、
  そこへは host state が host を入れてからしか来ないが、それは state についての事実である。
  -/
  portHost : st = .port → ctx.url.host.isSome = true

/-- `mayOpaque` が false の state では path は opaque でない。 -/
theorem PInv.notOpaque {base st ctx} (h : PInv base st ctx) (hm : mayOpaque st = false) :
    ctx.url.hasOpaquePath = false := by
  cases ho : ctx.url.hasOpaquePath with
  | false => rfl
  | true => rw [h.opaqueState ho] at hm; exact absurd hm (by simp)

/-- `mayCred` が false の state では `ValidUrl` がそのまま成り立つ。 -/
theorem PInv.valid {base st ctx} (h : PInv base st ctx) (hm : mayCred st = false) :
    ValidUrl ctx.url := by
  refine ⟨h.specialHasList, ?_, h.nullHostNoPort, h.opaqueNoCredentials, h.opaqueNoPort,
    h.opaqueNoHost⟩
  intro hh
  cases hc : ctx.url.includesCredentials with
  | false => rfl
  | true => rw [h.credState hh hc] at hm; exact absurd hm (by simp)

/-- 不変条件の成分から `ValidUrl` を組む。`mayCred` が false の state で使う。 -/
theorem valid_of_inv {u : Url}
    (hsp : u.isSpecial = true → u.hasOpaquePath = false)
    (hnp : u.host = none → u.port = none)
    (hoc : u.hasOpaquePath = true → u.includesCredentials = false)
    (hopo : u.hasOpaquePath = true → u.port = none)
    (hoh : u.hasOpaquePath = true → u.host = none)
    (hcs : u.host = none → u.includesCredentials = true → False) : ValidUrl u := by
  refine ⟨hsp, ?_, hnp, hoc, hopo, hoh⟩
  intro hh
  cases hc : u.includesCredentials with
  | false => rfl
  | true => exact (hcs hh hc).elim

/-! ## 入口 -/

/--
空の URL record はどの state でも `PInv` を満たす。
ただし base の path を読む state と port state は除く（どちらも前提を持つ）。

`basicUrlParse` が state machine を回し始める二か所（scheme start state と、
"start over" した後の no scheme state）がこれに当たる。
-/
theorem PInv_empty {base : Option Url} {st : PState} (hb : ∀ b, base = some b → ValidUrl b)
    (h1 : usesBasePath st = false) (h2 : st ≠ .port) :
    PInv base st { url := {} } := by
  refine ⟨rfl, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [Url.isSpecial, Url.hasOpaquePath, Url.includesCredentials, isSpecialScheme,
      defaultPort]

theorem PInv_schemeStart {base : Option Url} (hb : ∀ b, base = some b → ValidUrl b) :
    PInv base .schemeStart { url := {} } :=
  PInv_empty hb (by decide) (by decide)

theorem PInv_noScheme {base : Option Url} (hb : ∀ b, base = some b → ValidUrl b) :
    PInv base .noScheme { url := {} } :=
  PInv_empty hb (by decide) (by decide)

/--
`PInv` が state machine の 1 歩で保たれれば、parse の結果は `ValidUrl` を満たす。

つまり **残っているのは帰納段だけ**である。入口（空の record が `PInv` を満たすこと）と
出口（`PInv` から `ValidUrl` が出ること）と "start over" の扱いはここで閉じている。

帰納段は `run.induct` による functional induction で 113 の case に分かれ、
いまの自動化で 62 が閉じる。残りの内訳と手当ては `docs/url-status.md` に書いてある。
-/
theorem basicUrlParse_valid_of_step
    (hstep : ∀ (base : Option Url) (st : PState) (input : List Char) (ctx : PCtx),
      PInv base st ctx → ∀ u, run base st input ctx = .ok u → ValidUrl u)
    {input : String} {base : Option Url} (hb : ∀ b, base = some b → ValidUrl b)
    {u : Url} (h : basicUrlParse input base = some u) : ValidUrl u := by
  unfold basicUrlParse at h
  split at h
  · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (PInv_schemeStart hb) u' he
  · simp at h
  · split at h
    · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (PInv_noScheme hb) u' he
    · simp at h

end Url
