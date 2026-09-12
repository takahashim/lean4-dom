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
  simp [Url.hasOpaquePath, Path.isOpaque, hp]

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
  simp [Url.hasOpaquePath, Path.isOpaque, hp]

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
  simp [Url.hasOpaquePath, Path.isOpaque, hp]

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

/-! ### path state が作る url -/

/-- `pathStepUrl` は path 以外の成分を変えない。 -/
theorem pathStepUrl_spec (u : Url) (slash : Bool) (buffer : List Char) :
    ∃ p, pathStepUrl u slash buffer = { u with path := p } := by
  unfold pathStepUrl
  split
  · split
    · rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> exact ⟨_, by rw [h]⟩
    · rcases appendSegment_spec (shortenPath u) "" with h | ⟨_, _, h⟩ <;>
        rcases shortenPath_spec u with h' | ⟨_, _, h'⟩ <;> exact ⟨_, by rw [h, h']⟩
  · split
    · split
      · exact ⟨u.path, rfl⟩
      · rcases appendSegment_spec u "" with h | ⟨_, _, h⟩ <;> exact ⟨_, by rw [h]⟩
    · rcases appendSegment_spec u _ with h | ⟨_, _, h⟩ <;> exact ⟨_, by rw [h]⟩

@[simp] theorem pathStepUrl_scheme (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).scheme = u.scheme := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_host (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).host = u.host := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_port (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).port = u.port := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_username (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).username = u.username := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_password (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).password = u.password := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_query (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).query = u.query := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buffer; rw [h]

@[simp] theorem pathStepUrl_isSpecial (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).isSpecial = u.isSpecial := by
  simp [Url.isSpecial]

@[simp] theorem pathStepUrl_includesCredentials (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).includesCredentials = u.includesCredentials := by
  simp [Url.includesCredentials]

/-! ### `Path.isOpaque` の形に揃える

`Url.hasOpaquePath` は `path.isOpaque` を当てるだけなので、
record 更新をまたぐときは path の側で見たほうが simp が噛む。
-/

@[simp] theorem shortenPath_path_isOpaque (u : Url) :
    (shortenPath u).path.isOpaque = u.path.isOpaque := shortenPath_hasOpaquePath u

@[simp] theorem appendSegment_path_isOpaque (u : Url) (s : String) :
    (appendSegment u s).path.isOpaque = u.path.isOpaque := appendSegment_hasOpaquePath u s

@[simp] theorem appendOpaque_path_isOpaque (u : Url) (s : String) :
    (appendOpaque u s).path.isOpaque = u.path.isOpaque := appendOpaque_hasOpaquePath u s

/-- segment を確定させても path が opaque かどうかは変わらない。 -/
@[simp] theorem pathStepUrl_path_isOpaque (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).path.isOpaque = u.path.isOpaque := by
  unfold pathStepUrl
  split
  · split <;> simp
  · split
    · split <;> simp
    · simp

@[simp] theorem pathStepUrl_hasOpaquePath (u : Url) (slash : Bool) (buffer : List Char) :
    (pathStepUrl u slash buffer).hasOpaquePath = u.hasOpaquePath :=
  pathStepUrl_path_isOpaque u slash buffer

/-! ### file state が base から引き継ぐときの url -/

@[simp] theorem fileBasePath_scheme (u : Url) (input : List Char) :
    (fileBasePath u input).scheme = u.scheme := by
  unfold fileBasePath; split <;> simp

@[simp] theorem fileBasePath_host (u : Url) (input : List Char) :
    (fileBasePath u input).host = u.host := by
  unfold fileBasePath; split <;> simp

@[simp] theorem fileBasePath_port (u : Url) (input : List Char) :
    (fileBasePath u input).port = u.port := by
  unfold fileBasePath; split <;> simp

@[simp] theorem fileBasePath_username (u : Url) (input : List Char) :
    (fileBasePath u input).username = u.username := by
  unfold fileBasePath; split <;> simp

@[simp] theorem fileBasePath_password (u : Url) (input : List Char) :
    (fileBasePath u input).password = u.password := by
  unfold fileBasePath; split <;> simp

/-- base の path が opaque でなければ、引き継いだ後も opaque でない。 -/
@[simp] theorem fileBasePath_path_isOpaque (u : Url) (input : List Char)
    (h : u.path.isOpaque = false) : (fileBasePath u input).path.isOpaque = false := by
  unfold fileBasePath
  split
  · simp [Path.isOpaque]
  · rw [shortenPath_path_isOpaque]; exact h

@[simp] theorem fileSlashDrive_scheme (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).scheme = u.scheme := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

@[simp] theorem fileSlashDrive_host (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).host = u.host := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

@[simp] theorem fileSlashDrive_port (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).port = u.port := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

@[simp] theorem fileSlashDrive_username (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).username = u.username := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

@[simp] theorem fileSlashDrive_password (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).password = u.password := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

@[simp] theorem fileSlashDrive_path_isOpaque (u : Url) (p : Path) (input : List Char) :
    (fileSlashDrive u p input).path.isOpaque = u.path.isOpaque := by
  unfold fileSlashDrive; split <;> (try split) <;> simp

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

/-! ### `ValidUrl` が見ていない成分 -/

/-- `ValidUrl` の六条件はどれも query に触れない。 -/
@[simp] theorem validUrl_setQuery (u : Url) (q : Option String) :
    ValidUrl { u with query := q } ↔ ValidUrl u := by
  constructor <;> intro h <;>
    exact ⟨h.specialHasList, h.nullHostNoCredentials, h.nullHostNoPort,
      h.opaqueNoCredentials, h.opaqueNoPort, h.opaqueNoHost⟩

/-- fragment についても同じ。 -/
@[simp] theorem validUrl_setFragment (u : Url) (f : Option String) :
    ValidUrl { u with fragment := f } ↔ ValidUrl u := by
  constructor <;> intro h <;>
    exact ⟨h.specialHasList, h.nullHostNoCredentials, h.nullHostNoPort,
      h.opaqueNoCredentials, h.opaqueNoPort, h.opaqueNoHost⟩

/-! ## state で添字づけた不変条件 -/

/-- opaque path を持てる state。opaque path を作る scheme state の分岐の行き先である。 -/
def mayOpaque : PState → Bool
  | .opaquePath | .query | .fragment => true
  | _ => false

/-- host が null のまま credentials を持てる state。authority state が書き、host state が閉じる。 -/
def mayCred : PState → Bool
  | .authority | .host => true
  | _ => false

/-- host がまだ決まっていない state。opaque path を作る scheme state の足場になる。 -/
def freshHost : PState → Bool
  | .schemeStart | .scheme | .noScheme => true
  | _ => false

/--
credentials も port もまだ書かれていない state。

credentials を書くのは authority state、port を書くのは port state で、
どちらもここに挙げた state より後にある。base から成分を写す state
（no scheme / file / file slash）が、写さない成分について
`ValidUrl` を出すのにこれが要る。
-/
def freshCredPort : PState → Bool
  | .schemeStart | .scheme | .noScheme | .specialRelativeOrAuthority
  | .relative | .relativeSlash | .specialAuthoritySlashes | .specialAuthorityIgnoreSlashes
  | .pathOrAuthority | .file | .fileSlash | .fileHost => true
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
  /--
  scheme state までは host が決まっていない。

  opaque path を作るのは scheme state の一分岐で、そこで `opaqueNoHost` を
  出すのにこれが要る。host を書く state はすべて scheme state の後にあり、
  そこから scheme state へ戻る道は無い。
  -/
  schemeNoHost : freshHost st = true → ctx.url.host = none
  /-- host を決める前の state には credentials も port も無い。 -/
  freshState : freshCredPort st = true →
    ctx.url.includesCredentials = false ∧ ctx.url.port = none

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

/-- port state から path start state への遷移は `PInv` を保つ。 -/
theorem PInv.portStep {base : Option Url} {ctx ctx2 : PCtx} (h : PInv base .port ctx)
    (hp : portDone ctx = some ctx2) : PInv base .pathStart ctx2 := by
  obtain ⟨p, hu, ho⟩ := portDone_spec hp
  have hop : ctx.url.hasOpaquePath = false := h.notOpaque (by decide)
  have hs : ctx2.url.hasOpaquePath = false := by rw [hu]; exact hop
  have hh : ctx2.url.host = ctx.url.host := by rw [hu]
  have hsome : ctx.url.host.isSome = true := h.portHost rfl
  have hne : ctx2.url.host ≠ none := by
    rw [hh]; intro hn; rw [hn] at hsome; simp at hsome
  refine ⟨by rw [ho]; exact h.noOverride, h.baseValid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro hb; exact absurd hb (by decide)
  · intro _; exact hs
  · intro hn; exact absurd hn hne
  · intro ho'; rw [hs] at ho'; exact absurd ho' (by simp)
  · intro ho'; rw [hs] at ho'; exact absurd ho' (by simp)
  · intro ho'; rw [hs] at ho'; exact absurd ho' (by simp)
  · intro ho'; rw [hs] at ho'; exact absurd ho' (by simp)
  · intro hn; exact absurd hn hne
  · intro he; exact absurd he (by decide)
  · intro he; exact absurd he (by decide)
  · intro he; exact absurd he (by decide)

/-! ## 帰納段

`run.induct`（functional induction）で 113 の case に分かれる。
自動化は三段に分けてある。

1. url を変えない遷移と、失敗・即 `ok` の終端。
2. `isSpecial` / `hasOpaquePath` / `includesCredentials` を開いて判定するもの。
3. 遷移ごとの移送補題（`portStep`、`fileBasePath`、`pathStepUrl` ほか）が要るもの。

`step` の等式 lemma で畳めない case があるので、`eq_def` へ落とす経路も用意してある
（`match base with` が残る case がそれで、`rw [step]` は「equation theorems で
書き換えられない」と言って失敗する）。

この証明の elaborate に 5 分ほどかかる。
-/

/-!
### 自動化で使う simp set

三段で開く範囲が違う。段が進むほど広く開き、そのぶん遅い。
`unusedSimpArgs` linter はこの三つを数十箇所で呼ぶたびに引数ごとの警告を出すので、
この file では切ってある（どの引数がどの case で効くかは case ごとに違う）。
-/

/-! ## 入口 -/

/--
空の URL record はどの state でも `PInv` を満たす。
ただし base の path を読む state と port state は除く（どちらも前提を持つ）。

`basicUrlParse` が state machine を回し始める二か所（scheme start state と、
"start over" した後の no scheme state）がこれに当たる。
-/
theorem PInv_empty {base : Option Url} {st : PState}
    {toAscii : List Char → Option String} (hb : ∀ b, base = some b → ValidUrl b)
    (h1 : usesBasePath st = false) (h2 : st ≠ .port) :
    PInv base st { url := {}, toAscii } := by
  refine ⟨rfl, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

theorem PInv_schemeStart {base : Option Url} {toAscii : List Char → Option String}
    (hb : ∀ b, base = some b → ValidUrl b) :
    PInv base .schemeStart { url := {}, toAscii } :=
  PInv_empty hb (by decide) (by decide)

theorem PInv_noScheme {base : Option Url} {toAscii : List Char → Option String}
    (hb : ∀ b, base = some b → ValidUrl b) :
    PInv base .noScheme { url := {}, toAscii } :=
  PInv_empty hb (by decide) (by decide)

/--
`PInv` が state machine の 1 歩で保たれれば、parse の結果は `ValidUrl` を満たす。

入口（空の record が `PInv` を満たすこと）と出口（`PInv` から `ValidUrl` が出ること）と
"start over" の扱いをここでまとめる。帰納段は `Url/StepValid.lean` の `run_valid` が与える。
-/
theorem basicUrlParse_valid_of_step
    (hstep : ∀ (base : Option Url) (st : PState) (input : List Char) (ctx : PCtx),
      PInv base st ctx → ∀ u, run base st input ctx = .ok u → ValidUrl u)
    {input : String} {base : Option Url} {toAscii : List Char → Option String}
    (hb : ∀ b, base = some b → ValidUrl b)
    {u : Url} (h : basicUrlParse input base toAscii = some u) : ValidUrl u := by
  unfold basicUrlParse at h
  split at h
  · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (PInv_schemeStart hb) u' he
  · simp at h
  · split at h
    · next u' he => exact Option.some.inj h ▸ hstep _ _ _ _ (PInv_noScheme hb) u' he
    · simp at h

end Url
