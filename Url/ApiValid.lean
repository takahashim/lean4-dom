import Url.Api
import Url.Invariant

/-!
# setter が `ValidUrl` を保つこと

`Url/Api.lean` には record の中で閉じる setter（`username` / `password` / 空文字列の `port`）の
保存がある。ここは **parser を通る setter** のうち、通る state が閉じているものを扱う。

`search` と `hash` は query state と fragment state しか通らない。
どちらの state も query / fragment 以外を書かないので、`ValidUrl` の六条件は
どれも影響を受けない。state machine 全体の帰納法（`Url/Invariant.lean` の `run_valid`）を
使わずに、入力の長さについての短い帰納法で閉じる。

残りの setter（`protocol` / `host` / `hostname` / 非空の `port` / `pathname`）も
同じやり方で閉じる。override 付きだと各 state から行ける先が非常に狭いためである。

| 入口 | 行ける state |
| --- | --- |
| `.port` | 自分自身だけ（override では必ず返る） |
| `.fileHost` | 自分自身だけ |
| `.host` | 自分、`.fileHost`、`.port` |
| `.schemeStart` | `.scheme` だけ（そこで返る） |
| `.pathStart` | `.path` だけ |

state 機械全体の帰納法（`Url/Invariant.lean` の `run_valid`、113 case）は要らない。
`run_valid` の `PInv` は `over = none` を要求しているので、override に広げると
その 113 case をやり直すことになる。
-/

-- `cases he : ...` の枝ごとに `he` が要るかどうかが違うので、linter を切る。
set_option linter.unusedSimpArgs false

namespace Url

open Infra

/-- fragment state を回すと fragment しか変わらない。 -/
theorem run_fragment_shape (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .fragment input ctx = .ok u → ∃ f, u = { ctx.url with fragment := f }
  | [], ctx, u, h => by
    rw [run, step] at h
    exact ⟨ctx.url.fragment, by rw [← PResult.ok.inj h]⟩
  | ch :: t, ctx, u, h => by
    rw [run, step] at h
    obtain ⟨f, hf⟩ := run_fragment_shape base t _ u h
    exact ⟨f, hf⟩

/-- override 付きで query state を回すと query しか変わらない。 -/
theorem run_query_shape (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ctx.over.isSome = true → ∀ u, run base .query input ctx = .ok u →
      ∃ q, u = { ctx.url with query := q }
  | [], ctx, _, u, h => by
    rw [run, step] at h
    exact ⟨some (queryOf ctx), by rw [← PResult.ok.inj h]⟩
  | ch :: t, ctx, hov, u, h => by
    rw [run] at h
    by_cases hch : ch = '#'
    · subst hch
      rw [step, if_pos hov] at h
      obtain ⟨q, hq⟩ :=
        run_query_shape base t { ctx with buffer := ctx.buffer ++ ['#'] } hov u h
      exact ⟨q, hq⟩
    · rw [step] at h
      · obtain ⟨q, hq⟩ :=
          run_query_shape base t { ctx with buffer := ctx.buffer ++ [ch] } hov u h
        exact ⟨q, hq⟩
      · exact hch

/-! ## setter への持ち上げ -/

/-- fragment state から始める override は fragment しか変えない。 -/
theorem basicUrlParseOverride_fragment (s : String) (u0 u' : Url)
    (he : basicUrlParseOverride s u0 .fragment = some u') :
    ∃ f, u' = { u0 with fragment := f } := by
  unfold basicUrlParseOverride at he
  split at he
  · next w hw =>
    obtain ⟨f, hf⟩ := run_fragment_shape none _ _ w hw
    exact ⟨f, by rw [← Option.some.inj he, hf]⟩
  · simp at he

/-- query state から始める override は query しか変えない。 -/
theorem basicUrlParseOverride_query (s : String) (u0 u' : Url)
    (he : basicUrlParseOverride s u0 .query = some u') :
    ∃ q, u' = { u0 with query := q } := by
  unfold basicUrlParseOverride at he
  split at he
  · next w hw =>
    obtain ⟨q, hq⟩ := run_query_shape none _ _ rfl w hw
    exact ⟨q, by rw [← Option.some.inj he, hq]⟩
  · simp at he

/-- opaque path の中身だけ変えても `ValidUrl` は変わらない。 -/
theorem validUrl_setOpaque {u : Url} (h : ValidUrl u) (o : String) (hop : u.hasOpaquePath = true) :
    ValidUrl { u with path := .opaque o } :=
  ⟨fun hs => absurd (h.specialHasList hs) (by rw [hop]; simp),
    h.nullHostNoCredentials, h.nullHostNoPort,
    fun _ => h.opaqueNoCredentials hop, fun _ => h.opaqueNoPort hop, fun _ => h.opaqueNoHost hop⟩

theorem stripTrailingSpaces_valid {u : Url} (h : ValidUrl u) :
    ValidUrl (stripTrailingSpaces u) := by
  unfold stripTrailingSpaces
  split
  · exact h
  · next p hp =>
    split
    · exact h
    · exact validUrl_setOpaque h _ (by simp [Url.hasOpaquePath, hp, Path.isOpaque])

/-- **`hash` setter は `ValidUrl` を保つ。** -/
theorem setHash_valid {u : Url} (h : ValidUrl u) (v : String) : ValidUrl (u.setHash v) := by
  have hu0 : ValidUrl { u with fragment := some "" } := (validUrl_setFragment u _).mpr h
  unfold Url.setHash
  split
  · exact stripTrailingSpaces_valid ((validUrl_setFragment u none).mpr h)
  · cases he : basicUrlParseOverride (dropLeading '#' v) { u with fragment := some "" } .fragment with
    | none => simpa [he] using hu0
    | some u' =>
      obtain ⟨f, hf⟩ := basicUrlParseOverride_fragment _ _ _ he
      simp only [Option.getD_some, hf]
      exact (validUrl_setFragment u f).mpr h

/-- **`search` setter は `ValidUrl` を保つ。** -/
theorem setSearch_valid {u : Url} (h : ValidUrl u) (v : String) : ValidUrl (u.setSearch v) := by
  have hu0 : ValidUrl { u with query := some "" } := (validUrl_setQuery u _).mpr h
  unfold Url.setSearch
  split
  · exact stripTrailingSpaces_valid ((validUrl_setQuery u none).mpr h)
  · cases he : basicUrlParseOverride (dropLeading '?' v) { u with query := some "" } .query with
    | none => simpa [he] using hu0
    | some u' =>
      obtain ⟨q, hq⟩ := basicUrlParseOverride_query _ _ _ he
      simp only [Option.getD_some, hq]
      exact (validUrl_setQuery u q).mpr h

/-- override が付いていれば「失敗」はそこまでの record を返す。 -/
theorem fail_over {ctx : PCtx} (h : ctx.over.isSome = true) : fail ctx = PResult.ok ctx.url := by
  unfold fail
  split
  · rfl
  · next hc => rw [hc] at h; simp at h

/-- host が決まっていて opaque でなければ、port を書き換えても `ValidUrl` は保たれる。 -/
theorem validUrl_setPort {u : Url} (h : ValidUrl u) (hh : u.host.isSome = true)
    (ho : u.hasOpaquePath = false) (p : Option Nat) : ValidUrl { u with port := p } := by
  have hne : u.host ≠ none := by intro hn; rw [hn] at hh; simp at hh
  refine ⟨h.specialHasList, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hx
  · exact absurd hx hne
  · exact absurd hx hne
  · exact h.opaqueNoCredentials (by rw [← hx]; rfl)
  · exact absurd (show u.hasOpaquePath = true from hx) (by rw [ho]; simp)
  · exact h.opaqueNoHost (by rw [← hx]; rfl)

/-- override 付きの port state は `ValidUrl` を保つ。 -/
theorem run_port_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .port input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false →
    ctx.url.host.isSome = true → ValidUrl u
  | [], ctx, u, h, hov, hv, ho, hh => by
    rw [run, step] at h
    split at h
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
    · next ctx2 hpd =>
      try rw [if_pos hov] at h
      obtain ⟨p, hu, _⟩ := portDone_spec hpd
      rw [← PResult.ok.inj h, hu]
      exact validUrl_setPort hv hh ho p
  | ch :: t, ctx, u, h, hov, hv, ho, hh => by
    rw [run, step] at h
    split at h
    · exact run_port_valid base t _ u h hov hv ho hh
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · next ctx2 hpd =>
          try rw [if_pos hov] at h
          obtain ⟨p, hu, _⟩ := portDone_spec hpd
          rw [← PResult.ok.inj h, hu]
          exact validUrl_setPort hv hh ho p
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv

/-- opaque でなければ host を書き込んでも `ValidUrl` は保たれる。 -/
theorem validUrl_setHost {u : Url} (h : ValidUrl u) (ho : u.hasOpaquePath = false) (hst : Host) :
    ValidUrl { u with host := some hst } := by
  refine ⟨h.specialHasList, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hx
  · exact absurd hx (by simp)
  · exact absurd hx (by simp)
  · exact h.opaqueNoCredentials (by rw [← hx]; rfl)
  · exact h.opaqueNoPort (by rw [← hx]; rfl)
  · exact absurd (show u.hasOpaquePath = true from hx) (by rw [ho]; simp)

/-- override が付いていれば `isNone` は偽である。 -/
theorem over_isNone_false {ctx : PCtx} (h : ctx.over.isSome = true) : ctx.over.isNone = false := by
  cases hc : ctx.over with
  | none => rw [hc] at h; simp at h
  | some _ => rfl

/-- override 付きの file host state は `ValidUrl` を保つ。 -/
theorem run_fileHost_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .fileHost input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false → ValidUrl u
  | [], ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
    · exact run_fileHost_valid base t _ u h hov hv ho

/-- override 付きの host state は `ValidUrl` を保つ。 -/
theorem run_host_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .host input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false → ValidUrl u
  | [], ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · exact run_fileHost_valid base [] _ u h hov hv ho
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · split at h
          · rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
            · exact run_port_valid base [] _ u h hov (validUrl_setHost hv ho _) ho (by simp)
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [← PResult.ok.inj h]; exact hv
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
              · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · exact run_fileHost_valid base (ch :: t) _ u h hov hv ho
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · split at h
          · rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
            · exact run_port_valid base t _ u h hov (validUrl_setHost hv ho _) ho (by simp)
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [← PResult.ok.inj h]; exact hv
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
              · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _
        · exact run_host_valid base t _ u h hov hv ho

/-! ## scheme -/

theorem validUrl_clearPort {u : Url} (h : ValidUrl u) : ValidUrl { u with port := none } :=
  ⟨h.specialHasList, h.nullHostNoCredentials, fun _ => rfl, h.opaqueNoCredentials,
    fun _ => rfl, h.opaqueNoHost⟩

/-- special かどうかが変わらない scheme の書き換えは `ValidUrl` を保つ。 -/
theorem validUrl_setScheme {u : Url} (h : ValidUrl u) (s : String)
    (hsp : isSpecialScheme s = u.isSpecial) : ValidUrl { u with scheme := s } := by
  refine ⟨fun hx => ?_, h.nullHostNoCredentials, h.nullHostNoPort, h.opaqueNoCredentials,
    h.opaqueNoPort, h.opaqueNoHost⟩
  exact h.specialHasList (by rw [← hsp]; exact hx)

/-- protocol setter の本体は `ValidUrl` を保つ。 -/
theorem schemeOverride_valid {ctx : PCtx} (hv : ValidUrl ctx.url) (u : Url)
    (h : schemeOverride ctx = .ok u) : ValidUrl u := by
  simp +zetaDelta only [schemeOverride] at h
  split at h
  · rw [← PResult.ok.inj h]; exact hv
  · next g1 =>
    split at h
    · rw [← PResult.ok.inj h]; exact hv
    · next g2 =>
      have hsp : isSpecialScheme (String.ofList ctx.buffer) = ctx.url.isSpecial := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at g1 g2
        cases hs : ctx.url.isSpecial <;>
          cases hb : isSpecialScheme (String.ofList ctx.buffer) <;> simp_all
      split at h
      · rw [← PResult.ok.inj h]; exact hv
      · split at h
        · rw [← PResult.ok.inj h]; exact hv
        · split at h
          · rw [← PResult.ok.inj h]
            exact validUrl_clearPort (validUrl_setScheme hv _ hsp)
          · rw [← PResult.ok.inj h]
            exact validUrl_setScheme hv _ hsp

/-- override 付きの scheme state は `ValidUrl` を保つ。 -/
theorem run_scheme_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .scheme input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ValidUrl u
  | [], ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · exact run_scheme_valid base t _ u h hov hv
    · split at h
      · exact schemeOverride_valid hv u h
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv

/-- override 付きの scheme start state は `ValidUrl` を保つ。 -/
theorem run_schemeStart_valid (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .schemeStart input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ValidUrl u
  | [], ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · exact run_scheme_valid base t _ u h hov hv
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv

/-! ## path -/

/-- path の種類が変わらない書き換えは `ValidUrl` を保つ。 -/
theorem validUrl_setPath {u : Url} (h : ValidUrl u) (p : Path)
    (hop : p.isOpaque = u.path.isOpaque) : ValidUrl { u with path := p } :=
  ⟨fun hx => by rw [Url.hasOpaquePath]; rw [hop]; exact h.specialHasList hx,
    h.nullHostNoCredentials, h.nullHostNoPort,
    fun hx => h.opaqueNoCredentials (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx),
    fun hx => h.opaqueNoPort (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx),
    fun hx => h.opaqueNoHost (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx)⟩

theorem validUrl_appendSegment {u : Url} (h : ValidUrl u) (s : String) :
    ValidUrl (appendSegment u s) := by
  obtain he | ⟨segs, hp, he⟩ := appendSegment_spec u s
  · rw [he]; exact h
  · have hiso := appendSegment_path_isOpaque u s
    rw [he] at hiso ⊢
    exact validUrl_setPath h _ hiso

theorem validUrl_pathStepUrl {u : Url} (h : ValidUrl u) (slash : Bool) (buffer : List Char) :
    ValidUrl (pathStepUrl u slash buffer) := by
  obtain ⟨p, hp⟩ := pathStepUrl_spec u slash buffer
  have hiso := pathStepUrl_path_isOpaque u slash buffer
  rw [hp] at hiso ⊢
  exact validUrl_setPath h _ hiso

/-- override 付きの path state は `ValidUrl` を保つ。 -/
theorem run_path_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .path input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ValidUrl u
  | [], ctx, u, h, hov, hv => by
    rw [run, step] at h
    split at h
    · rw [← PResult.ok.inj h]; exact validUrl_pathStepUrl hv _ _
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.or_false] at h
    split at h
    · split at h
      · simp_all
      · simp_all
      · simp_all
      · exact run_path_valid base t _ u h hov (validUrl_pathStepUrl hv _ _)
    · exact run_path_valid base t _ u h hov hv

/-- override 付きの path start state は `ValidUrl` を保つ。 -/
theorem run_pathStart_valid (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .pathStart input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ValidUrl u
  | [], ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_valid base [] _ u h hov hv
      · exact run_path_valid base [] _ u h hov hv
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_appendSegment hv _
      · rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_valid base t _ u h hov hv
      · exact run_path_valid base (ch :: t) _ u h hov hv
    · split at h
      · exact run_path_valid base t _ u h hov hv
      · exact run_path_valid base (ch :: t) _ u h hov hv

/-! ## setter -/

/-- **`protocol` setter は `ValidUrl` を保つ。** -/
theorem setProtocol_valid {u : Url} (h : ValidUrl u) (v : String) :
    ValidUrl (u.setProtocol v) := by
  unfold Url.setProtocol
  cases he : basicUrlParseOverride (v ++ ":") u .scheme with
  | none => simpa [he] using h
  | some u' =>
    simp only [he, Option.getD_some]
    unfold basicUrlParseOverride at he
    split at he
    · next w hw =>
      rw [← Option.some.inj he]
      exact run_schemeStart_valid none _ _ w hw rfl h
    · simp at he

/-- **`host` setter は `ValidUrl` を保つ。** -/
theorem setHost_valid {u : Url} (h : ValidUrl u) (v : String)
    (toAscii : List Char → Option String) : ValidUrl (u.setHost v toAscii) := by
  unfold Url.setHost
  split
  · exact h
  · next hop =>
    have ho : u.hasOpaquePath = false := by simpa using hop
    cases he : basicUrlParseOverride v u .host toAscii with
    | none => simpa [he] using h
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_host_valid none _ _ w hw rfl h ho
      · simp at he

/-- **`hostname` setter は `ValidUrl` を保つ。** -/
theorem setHostname_valid {u : Url} (h : ValidUrl u) (v : String)
    (toAscii : List Char → Option String) : ValidUrl (u.setHostname v toAscii) := by
  unfold Url.setHostname
  split
  · exact h
  · next hop =>
    have ho : u.hasOpaquePath = false := by simpa using hop
    cases he : basicUrlParseOverride v u .hostname toAscii with
    | none => simpa [he] using h
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_host_valid none _ _ w hw rfl h ho
      · simp at he

/-- **`port` setter は `ValidUrl` を保つ。** -/
theorem setPort_valid {u : Url} (h : ValidUrl u) (v : String) : ValidUrl (u.setPort v) := by
  unfold Url.setPort
  split
  · exact h
  · next hc =>
    have hh : u.host.isSome = true := by
      cases hx : u.host with
      | none => rw [Url.cannotHaveCredentials, hx] at hc; simp at hc
      | some _ => rfl
    have ho : u.hasOpaquePath = false := by
      cases hx : u.hasOpaquePath with
      | false => rfl
      | true => rw [h.opaqueNoHost hx] at hh; simp at hh
    split
    · exact validUrl_clearPort h
    · cases he : basicUrlParseOverride v u .port with
      | none => simpa [he] using h
      | some u' =>
        simp only [he, Option.getD_some]
        unfold basicUrlParseOverride at he
        split at he
        · next w hw =>
          rw [← Option.some.inj he]
          exact run_port_valid none _ _ w hw rfl h ho hh
        · simp at he

/-- **`pathname` setter は `ValidUrl` を保つ。** -/
theorem setPathname_valid {u : Url} (h : ValidUrl u) (v : String) :
    ValidUrl (u.setPathname v) := by
  unfold Url.setPathname
  split
  · exact h
  · next hop =>
    have ho : u.hasOpaquePath = false := by simpa using hop
    have h0 : ValidUrl { u with path := Path.list [] } :=
      validUrl_setPath h (Path.list []) (by show false = u.path.isOpaque; exact ho.symm)
    cases he : basicUrlParseOverride v { u with path := Path.list [] } .path with
    | none => simpa [he] using h0
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_pathStart_valid none _ _ w hw rfl h0
      · simp at he

/-- **どの IDL setter も `ValidUrl` を保つ。** -/
theorem setAttr_valid {u : Url} (h : ValidUrl u) (name v : String)
    (toAscii : List Char → Option String) (u' : Url)
    (hs : u.setAttr name v toAscii = some u') : ValidUrl u' := by
  unfold Url.setAttr at hs
  split at hs
  · -- href は base 無しで parse し直す
    rw [← Option.some.inj hs]
    unfold Url.setHref
    cases hp : basicUrlParse v none toAscii with
    | none => simpa [hp] using h
    | some w =>
      simp only [hp, Option.getD_some]
      exact basicUrlParse_valid (fun b hb => absurd hb (by simp)) hp
  · rw [← Option.some.inj hs]; exact setProtocol_valid h v
  · rw [← Option.some.inj hs]; exact setUsername_valid h v
  · rw [← Option.some.inj hs]; exact setPassword_valid h v
  · rw [← Option.some.inj hs]; exact setHost_valid h v toAscii
  · rw [← Option.some.inj hs]; exact setHostname_valid h v toAscii
  · rw [← Option.some.inj hs]; exact setPort_valid h v
  · rw [← Option.some.inj hs]; exact setPathname_valid h v
  · rw [← Option.some.inj hs]; exact setSearch_valid h v
  · rw [← Option.some.inj hs]; exact setHash_valid h v
  · exact absurd hs (by simp)

end Url
