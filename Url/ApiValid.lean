import Url.Api
import Url.Invariant
import Url.StepValid

/-!
# setter が `ValidUrl` を保つこと

`Url/Api.lean` には record の中で閉じる setter（`username` / `password` / 空文字列の `port`）の
保存がある。ここは **parser を通る setter** のうち、通る state が閉じているものを扱う。

`search` と `hash` は query state と fragment state しか通らない。
どちらの state も query / fragment 以外を書かないので、`ValidUrl` の六条件は
どれも影響を受けない。state machine 全体の帰納法（`Url/StepValid.lean` の `run_valid`）を
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

state 機械全体の帰納法（`Url/StepValid.lean` の `run_valid`）は要らない。
`run_valid` の `PInv` は `over = none` を要求しているので、override に広げると
その 119 case をやり直すことになる。
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
    fun _ => h.opaqueNoCredentials hop, fun _ => h.opaqueNoPort hop, fun _ => h.opaqueNoHost hop,
    h.portRange, h.fileNoCredentials, h.fileNoPort, h.hostKind, rfl, h.emptyHostNoPort⟩

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
    (ho : u.hasOpaquePath = false) (p : Option Nat)
    (hpr : ∀ q, p = some q → q < 65536) (hnf : u.scheme ≠ "file")
    (hem : u.host ≠ some Host.empty) : ValidUrl { u with port := p } := by
  have hne : u.host ≠ none := by intro hn; rw [hn] at hh; simp at hh
  refine ⟨h.specialHasList, ?_, ?_, ?_, ?_, ?_, hpr, h.fileNoCredentials,
    fun hf => absurd hf hnf, h.hostKind, h.pathSegs, fun he => absurd he hem⟩ <;> intro hx
  · exact absurd hx hne
  · exact absurd hx hne
  · exact h.opaqueNoCredentials (by rw [← hx]; rfl)
  · exact absurd (show u.hasOpaquePath = true from hx) (by rw [ho]; simp)
  · exact h.opaqueNoHost (by rw [← hx]; rfl)

/-- override 付きの port state は `ValidUrl` を保つ。 -/
theorem run_port_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .port input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false →
    ctx.url.host.isSome = true → ctx.url.scheme ≠ "file" →
    ctx.url.host ≠ some Host.empty → ValidUrl u
  | [], ctx, u, h, hov, hv, ho, hh, hnf, hem => by
    rw [run, step] at h
    split at h
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
    · next ctx2 hpd =>
      try rw [if_pos hov] at h
      obtain ⟨p, hu, _⟩ := portDone_spec hpd
      have hpr : ∀ q, p = some q → q < 65536 := fun q hq =>
        portDone_range hpd hv.portRange q (by rw [hu]; simpa using hq)
      rw [← PResult.ok.inj h, hu]
      exact validUrl_setPort hv hh ho p hpr hnf hem
  | ch :: t, ctx, u, h, hov, hv, ho, hh, hnf, hem => by
    rw [run, step] at h
    split at h
    · exact run_port_valid base t _ u h hov hv ho hh hnf hem
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · next ctx2 hpd =>
          try rw [if_pos hov] at h
          obtain ⟨p, hu, _⟩ := portDone_spec hpd
          have hpr : ∀ q, p = some q → q < 65536 := fun q hq =>
            portDone_range hpd hv.portRange q (by rw [hu]; simpa using hq)
          rw [← PResult.ok.inj h, hu]
          exact validUrl_setPort hv hh ho p hpr hnf hem
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv

/-- opaque でなければ host を書き込んでも `ValidUrl` は保たれる。 -/
theorem validUrl_setHost {u : Url} (h : ValidUrl u) (ho : u.hasOpaquePath = false) (hst : Host)
    (hk : hostKindOkOf u.scheme (some hst) = true)
    (hep : hst = Host.empty → u.port = none) :
    ValidUrl { u with host := some hst } := by
  refine ⟨h.specialHasList, ?_, ?_, ?_, ?_, ?_, h.portRange, h.fileNoCredentials,
    h.fileNoPort, hk, h.pathSegs, fun he => hep (Option.some.inj he)⟩ <;> intro hx
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

/--
`:` の分岐で書かれる host は empty でない。

そこは buffer が空なら失敗するので、host parser には空でない buffer が渡る。
-/
theorem host_ne_empty {ctx : PCtx} {hst : Host} (hb : ¬ctx.buffer.isEmpty = true)
    (hp : hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) = some hst) :
    ¬hst = Host.empty := by
  intro he
  rw [he] at hp
  rw [hostParser_empty hp] at hb
  simp at hb

/--
override 付きで host を空にできるのは、credentials も port も無いときだけ。

host state の終端の guard（`buffer.isEmpty && (credentials || port)` なら何もしない）が
それを見ている。§4.1「host が空なら port は持てない」の setter 側である。
-/
theorem empty_host_port {ctx : PCtx} {hst : Host}
    (hg : ¬(ctx.buffer.isEmpty && (ctx.url.includesCredentials || ctx.url.port.isSome)) = true)
    (hp : hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) = some hst)
    (he : hst = Host.empty) : ctx.url.port = none := by
  rw [he] at hp
  have hb : ctx.buffer.isEmpty = true := by rw [hostParser_empty hp]; rfl
  rw [hb] at hg
  simp only [Bool.true_and, Bool.or_eq_true, not_or] at hg
  cases hpo : ctx.url.port with
  | none => rfl
  | some q => exact absurd (show ctx.url.port.isSome = true by rw [hpo]; rfl) hg.2

/-- `file` URL に empty host は置ける（§4.1 の表）。 -/
theorem empty_kind {u : Url} (hf : u.scheme = "file") :
    hostKindOkOf u.scheme (some Host.empty) = true := by rw [hf]; rfl

/-- file host state が書き込む host は §4.1 の表に合う。`localhost` は empty host になる。 -/
theorem fileHost_kind {ctx : PCtx} (hf : ctx.url.scheme = "file") (hst : Host)
    (hp : hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) = some hst) :
    hostKindOkOf ctx.url.scheme
      (some (if hostSerializer hst == "localhost" then Host.empty else hst)) = true := by
  split
  · rw [hf]; rfl
  · exact hostParser_hostKind hp

/-- override 付きの file host state は `ValidUrl` を保つ。 -/
theorem run_fileHost_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .fileHost input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false →
    ctx.url.scheme = "file" → ValidUrl u
  | [], ctx, u, h, hov, hv, ho, hf => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _ (empty_kind hf) (fun _ => hv.fileNoPort hf)
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · rw [← PResult.ok.inj h]
          exact validUrl_setHost hv ho _ (fileHost_kind hf _ (by assumption))
            (fun _ => hv.fileNoPort hf)
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, ho, hf => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_setHost hv ho _ (empty_kind hf) (fun _ => hv.fileNoPort hf)
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · rw [← PResult.ok.inj h]
          exact validUrl_setHost hv ho _ (fileHost_kind hf _ (by assumption))
            (fun _ => hv.fileNoPort hf)
    · exact run_fileHost_valid base t _ u h hov hv ho hf

/-- override 付きの host state は `ValidUrl` を保つ。 -/
theorem run_host_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .host input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → ctx.url.hasOpaquePath = false → ValidUrl u
  | [], ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · next gf => exact run_fileHost_valid base [] _ u h hov hv ho (by simpa using gf)
    · next gnf =>
      have hnf : ctx.url.scheme ≠ "file" := by simpa using gnf
      split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · split at h
          · rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
            · exact run_port_valid base [] _ u h hov
                (validUrl_setHost hv ho _ (hostParser_hostKind (by assumption))
                  (fun he => absurd he (host_ne_empty (by assumption) (by assumption))))
                ho (by simp) hnf
                (by simpa using host_ne_empty (ctx := ctx) (by assumption) (by assumption))
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [← PResult.ok.inj h]; exact hv
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
              · rw [← PResult.ok.inj h]
                exact validUrl_setHost hv ho _ (hostParser_hostKind (by assumption))
                  (empty_host_port (by assumption) (by assumption))
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, ho => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · next gf => exact run_fileHost_valid base (ch :: t) _ u h hov hv ho (by simpa using gf)
    · next gnf =>
      have hnf : ctx.url.scheme ≠ "file" := by simpa using gnf
      split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
        · split at h
          · rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
            · exact run_port_valid base t _ u h hov
                (validUrl_setHost hv ho _ (hostParser_hostKind (by assumption))
                  (fun he => absurd he (host_ne_empty (by assumption) (by assumption))))
                ho (by simp) hnf
                (by simpa using host_ne_empty (ctx := ctx) (by assumption) (by assumption))
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
          · split at h
            · rw [← PResult.ok.inj h]; exact hv
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
              · rw [← PResult.ok.inj h]
                exact validUrl_setHost hv ho _ (hostParser_hostKind (by assumption))
                  (empty_host_port (by assumption) (by assumption))
        · exact run_host_valid base t _ u h hov hv ho

/-! ## scheme -/

theorem validUrl_clearPort {u : Url} (h : ValidUrl u) : ValidUrl { u with port := none } :=
  ⟨h.specialHasList, h.nullHostNoCredentials, fun _ => rfl, h.opaqueNoCredentials,
    fun _ => rfl, h.opaqueNoHost, by simp, h.fileNoCredentials, fun _ => rfl, h.hostKind,
    h.pathSegs, fun _ => rfl⟩

/-- special かどうかが変わらない scheme の書き換えは `ValidUrl` を保つ。 -/
theorem validUrl_setScheme {u : Url} (h : ValidUrl u) (s : String)
    (hsp : isSpecialScheme s = u.isSpecial)
    (hf : s = "file" → u.includesCredentials = false ∧ u.port = none)
    (hfe : ¬(u.scheme = "file" ∧ u.host = some Host.empty)) :
    ValidUrl { u with scheme := s } := by
  refine ⟨fun hx => ?_, h.nullHostNoCredentials, h.nullHostNoPort, h.opaqueNoCredentials,
    h.opaqueNoPort, h.opaqueNoHost, h.portRange, fun hx => (hf hx).1, fun hx => (hf hx).2, ?_,
    h.pathSegs, h.emptyHostNoPort⟩
  · exact h.specialHasList (by rw [← hsp]; exact hx)
  · exact hostKindOkOf_congr hsp hfe h.hostKind

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
      · next g3 =>
        -- `file` へ書き換える前に credentials と port が空であることを確かめている。
        have hf : String.ofList ctx.buffer = "file" →
            ctx.url.includesCredentials = false ∧ ctx.url.port = none := by
          intro hb
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, not_and, not_or] at g3
          refine ⟨?_, ?_⟩
          · cases hc : ctx.url.includesCredentials with
            | false => rfl
            | true => exact absurd hb (g3 (Or.inl hc))
          · cases hp : ctx.url.port with
            | none => rfl
            | some q => exact absurd hb (g3 (Or.inr (by rw [hp]; rfl)))
        split at h
        · rw [← PResult.ok.inj h]; exact hv
        · next g4 =>
          -- `file` の empty host を別の scheme へ移さない。§4.1 の表の唯一の例外。
          have hfe : ¬(ctx.url.scheme = "file" ∧ ctx.url.host = some Host.empty) := by
            simp only [Bool.and_eq_true, beq_iff_eq, not_and] at g4 ⊢
            exact fun hs hh => g4 hs hh
          split at h
          · rw [← PResult.ok.inj h]
            exact validUrl_clearPort (validUrl_setScheme hv _ hsp hf hfe)
          · rw [← PResult.ok.inj h]
            exact validUrl_setScheme hv _ hsp hf hfe

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
    (hop : p.isOpaque = u.path.isOpaque) (hps : pathSegsOk p = true) :
    ValidUrl { u with path := p } :=
  ⟨fun hx => by rw [Url.hasOpaquePath]; rw [hop]; exact h.specialHasList hx,
    h.nullHostNoCredentials, h.nullHostNoPort,
    fun hx => h.opaqueNoCredentials (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx),
    fun hx => h.opaqueNoPort (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx),
    fun hx => h.opaqueNoHost (by rw [Url.hasOpaquePath] at hx; rw [hop] at hx; exact hx),
    h.portRange, h.fileNoCredentials, h.fileNoPort, h.hostKind, hps, h.emptyHostNoPort⟩

theorem validUrl_appendSegment {u : Url} (h : ValidUrl u) (s : String)
    (hs : noSlash s.toList = true) : ValidUrl (appendSegment u s) := by
  obtain he | ⟨segs, hp, he⟩ := appendSegment_spec u s
  · rw [he]; exact h
  · have hiso := appendSegment_path_isOpaque u s
    have hps := pathSegsOk_appendSegment h.pathSegs hs
    rw [he] at hiso hps ⊢
    exact validUrl_setPath h _ hiso hps

theorem validUrl_pathStepUrl {u : Url} (h : ValidUrl u) (slash : Bool) (buffer : List Char)
    (hb : noSlash buffer = true) : ValidUrl (pathStepUrl u slash buffer) := by
  obtain ⟨p, hp⟩ := pathStepUrl_spec u slash buffer
  have hiso := pathStepUrl_path_isOpaque u slash buffer
  have hps := pathSegsOk_pathStepUrl (u := u) (slash := slash) h.pathSegs hb
  rw [hp] at hiso hps ⊢
  exact validUrl_setPath h _ hiso hps

/-- override 付きの path state は `ValidUrl` を保つ。 -/
theorem run_path_valid (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .path input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → noSlash ctx.buffer = true → ValidUrl u
  | [], ctx, u, h, hov, hv, hb => by
    rw [run, step] at h
    split at h
    · rw [← PResult.ok.inj h]; exact validUrl_pathStepUrl hv _ _ hb
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, hb => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.or_false] at h
    split at h
    · split at h
      · simp_all
      · simp_all
      · simp_all
      · exact run_path_valid base t _ u h hov (validUrl_pathStepUrl hv _ _ hb) rfl
    · next hnt =>
      refine run_path_valid base t _ u h hov hv ?_
      simp only [noSlash_append, hb, Bool.true_and]
      refine encChar_no_slash ?_
      intro heq
      rw [heq] at hnt
      simp at hnt

/-- override 付きの path start state は `ValidUrl` を保つ。 -/
theorem run_pathStart_valid (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .pathStart input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → noSlash ctx.buffer = true → ValidUrl u
  | [], ctx, u, h, hov, hv, hb => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_valid base [] _ u h hov hv hb
      · exact run_path_valid base [] _ u h hov hv hb
    · split at h
      · rw [← PResult.ok.inj h]; exact validUrl_appendSegment hv _ rfl
      · rw [← PResult.ok.inj h]; exact hv
  | ch :: t, ctx, u, h, hov, hv, hb => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_valid base t _ u h hov hv hb
      · exact run_path_valid base (ch :: t) _ u h hov hv hb
    · split at h
      · exact run_path_valid base t _ u h hov hv hb
      · exact run_path_valid base (ch :: t) _ u h hov hv hb

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
            (by intro hf; rw [Url.cannotHaveCredentials, hf] at hc; simp at hc)
            (by intro he; rw [Url.cannotHaveCredentials, he] at hc; simp at hc)
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
      validUrl_setPath h (Path.list []) (by show false = u.path.isOpaque; exact ho.symm) rfl
    cases he : basicUrlParseOverride v { u with path := Path.list [] } .path with
    | none => simpa [he] using h0
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_pathStart_valid none _ _ w hw rfl h0 rfl
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


/-!
## setter が何をするか

`setX_cannot`（できないときは何もしない）と `setX_valid`（`ValidUrl` を壊さない）だけでは、
**引数を無視する setter でも両方を満たす**。ここは肯定側である。
-/

/-- `stripTrailingSpaces` は fragment も query も変えない。 -/
theorem stripTrailingSpaces_fragment (u : Url) : (stripTrailingSpaces u).fragment = u.fragment := by
  unfold stripTrailingSpaces
  split
  · rfl
  · split <;> rfl

theorem stripTrailingSpaces_query (u : Url) : (stripTrailingSpaces u).query = u.query := by
  unfold stripTrailingSpaces
  split
  · rfl
  · split <;> rfl

/-- **`hash` に空文字列を入れると `hash` は空になる。** -/
theorem setHash_empty_hash (u : Url) : (u.setHash "").hash = "" := by
  unfold Url.setHash Url.hash
  rw [if_pos (by rfl), stripTrailingSpaces_fragment]

/-- **`search` に空文字列を入れると `search` は空になる。** -/
theorem setSearch_empty_search (u : Url) : (u.setSearch "").search = "" := by
  unfold Url.setSearch Url.search
  rw [if_pos (by rfl), stripTrailingSpaces_query]

/-- fragment state を走らせると、入力を percent-encode して fragment の末尾に足す。 -/
theorem run_fragment_spec (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    ctx.url.fragment.isSome = true →
    run base .fragment input ctx = .ok u →
    u = { ctx.url with
          fragment := some ((ctx.url.fragment.getD "")
            ++ String.ofList (input.flatMap (fun c => (encChar fragmentSet c).toList))) } := by
  intro input
  induction input with
  | nil =>
    intro ctx u hf h
    rw [run, step] at h
    rw [← PResult.ok.inj h]
    cases hq : ctx.url.fragment with
    | none => rw [hq] at hf; simp at hf
    | some f =>
      have key : ((some f).getD "" ++ String.ofList
          (([] : List Char).flatMap (fun c => (encChar fragmentSet c).toList))) = f := by simp
      rw [key, ← hq]
  | cons c rest ih =>
    intro ctx u hf h
    rw [run, step] at h
    rw [ih _ u (by simp) h]
    simp [String.append_assoc]

/-- fragment state は失敗しない。文字を足して進むだけである。 -/
theorem run_fragment_ok (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∃ u, run base .fragment input ctx = .ok u := by
  intro input
  induction input with
  | nil => intro ctx; exact ⟨ctx.url, by rw [run, step]⟩
  | cons c rest ih =>
    intro ctx
    obtain ⟨u, hu⟩ := ih { ctx with url := { ctx.url with
      fragment := some ((ctx.url.fragment.getD "") ++ encChar fragmentSet c) } }
    exact ⟨u, by rw [run, step]; exact hu⟩

/--
**`hash` setter は、先頭の `#` を落とした残りを percent-encode して fragment に入れる。**

`setHash_valid`（`ValidUrl` を壊さない）と `setHash_empty_hash`（空なら消える）だけでは
「引数を無視する setter」も満たしてしまう。これが肯定側である。
-/
theorem setHash_spec (u : Url) (v : String) (hv : v.isEmpty = false) :
    (u.setHash v).fragment
      = some (String.ofList ((stripTabNewline (dropLeading '#' v).toList).flatMap
          (fun c => (encChar fragmentSet c).toList))) := by
  unfold Url.setHash
  rw [if_neg (by simp [hv])]
  unfold basicUrlParseOverride
  split
  · next u' he =>
    rw [Option.getD_some]
    rw [run_fragment_spec none _ _ u' (by simp) he]
    simp
  · next hnone =>
    exfalso
    obtain ⟨u', hu'⟩ := run_fragment_ok none (stripTabNewline (dropLeading '#' v).toList)
      { url := { u with fragment := some "" }, over := some SOverride.fragment }
    exact hnone u' hu'

/-- override 付きの query state は、入力を全部 buffer に積んで最後に encode する。 -/
theorem run_query_spec (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    ctx.over.isSome = true →
    run base .query input ctx = .ok u →
    u = { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ input }) } := by
  intro input
  induction input with
  | nil =>
    intro ctx u ho h
    rw [run, step] at h
    rw [← PResult.ok.inj h]
    simp
  | cons c rest ih =>
    intro ctx u ho h
    rw [run] at h
    by_cases hc : c = '#'
    · subst hc
      rw [step] at h
      simp only [if_pos ho] at h
      rw [ih { ctx with buffer := ctx.buffer ++ ['#'] } u ho h]
      simp
    · rw [step] at h
      · rw [ih { ctx with buffer := ctx.buffer ++ [c] } u ho h]
        simp
      · exact hc

/-- query state は失敗しない。 -/
theorem run_query_ok (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ctx.over.isSome = true → ∃ u, run base .query input ctx = .ok u := by
  intro input
  induction input with
  | nil => intro ctx _; exact ⟨_, by rw [run, step]⟩
  | cons c rest ih =>
    intro ctx ho
    by_cases hc : c = '#'
    · subst hc
      obtain ⟨u, hu⟩ := ih { ctx with buffer := ctx.buffer ++ ['#'] } ho
      exact ⟨u, by rw [run, step]; simp only [if_pos ho]; exact hu⟩
    · obtain ⟨u, hu⟩ := ih { ctx with buffer := ctx.buffer ++ [c] } ho
      refine ⟨u, ?_⟩
      rw [run, step]
      · exact hu
      · exact hc

/--
**`search` setter は、先頭の `?` を落とした残りを percent-encode して query に入れる。**

`queryOf` は special かどうかで encode set を選ぶので、その判定ごと `queryOf` に委ねてある。
-/
theorem setSearch_spec (u : Url) (v : String) (hv : v.isEmpty = false) :
    (u.setSearch v).query
      = some (queryOf { url := { u with query := some "" },
                        buffer := stripTabNewline (dropLeading '?' v).toList,
                        over := some SOverride.query }) := by
  unfold Url.setSearch
  rw [if_neg (by simp [hv])]
  unfold basicUrlParseOverride
  split
  · next u' he =>
    rw [Option.getD_some, run_query_spec none _ _ u' (by simp) he]
    simp
  · next hnone =>
    exfalso
    obtain ⟨u', hu'⟩ := run_query_ok none (stripTabNewline (dropLeading '?' v).toList)
      { url := { u with query := some "" }, over := some SOverride.query } (by simp)
    exact hnone u' hu'

/-! ### 前処理

setter は入力から tab と newline を落としてから parse する。
どの肯定側の定理も、まずそこを通り抜ける必要がある。
-/

theorem stripTabNewline_eq_self {l : List Char}
    (h : ∀ c ∈ l, c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D) :
    stripTabNewline l = l := by
  unfold stripTabNewline
  refine List.filter_eq_self.mpr ?_
  intro c hc
  have hd := h c hc
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-! ### port

`setPort_valid` は「port setter が `ValidUrl` を壊さない」しか言わない。
引数を無視する setter でもそれは満たすので、ここで「入れた数がそのまま入る」を言う。
-/

/-- digit だけの入力は tab も newline も含まないので、前処理で変わらない。 -/
theorem stripTabNewline_digits {l : List Char} (h : ∀ c ∈ l, isAsciiDigit c = true) :
    stripTabNewline l = l :=
  stripTabNewline_eq_self fun c hc => by
    have hd := h c hc
    simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    omega

/-- 16 bit に収まる 10 進を積んだ buffer は、その値を port に書いて終わる。 -/
theorem portDone_digits {ctx : PCtx} (hne : ctx.buffer ≠ [])
    (hle : portValue ctx.buffer ≤ 65535) :
    portDone ctx = some (portSet ctx (portOf ctx.url.scheme (portValue ctx.buffer))) := by
  unfold portDone
  rw [if_neg (by simpa using hne), if_neg (by simp; omega)]

/-- override 付きの port state は、digit を全部 buffer に積んで最後に `portDone` する。 -/
theorem run_port_spec (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    ctx.over.isSome = true → (∀ c ∈ input, isAsciiDigit c = true) →
    run base .port input ctx = .ok u →
    u = (match portDone { ctx with buffer := ctx.buffer ++ input } with
         | some ctx2 => ctx2.url
         | none => ctx.url) := by
  intro input
  induction input with
  | nil =>
    intro ctx u ho _ h
    have hce : ({ ctx with buffer := ctx.buffer ++ [] } : PCtx) = ctx := by simp
    rw [hce]
    rw [run, step] at h
    split at h
    · next hn =>
      rw [hn]
      rw [fail_over ho] at h
      exact (PResult.ok.inj h).symm
    · next ctx2 hs =>
      rw [hs]
      rw [if_pos ho] at h
      exact (PResult.ok.inj h).symm
  | cons c rest ih =>
    intro ctx u ho hd h
    rw [run, step] at h
    rw [if_pos (hd c (by simp))] at h
    have := ih { ctx with buffer := ctx.buffer ++ [c] } u ho (fun x hx => hd x (by simp [hx])) h
    simpa using this

/-- override 付きの port state は digit だけの入力では失敗しない。 -/
theorem run_port_ok (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ctx.over.isSome = true → (∀ c ∈ input, isAsciiDigit c = true) →
    ∃ u, run base .port input ctx = .ok u := by
  intro input
  induction input with
  | nil =>
    intro ctx ho _
    rw [run, step]
    split
    · exact ⟨ctx.url, fail_over ho⟩
    · next ctx2 _ => exact ⟨ctx2.url, by rw [if_pos ho]⟩
  | cons c rest ih =>
    intro ctx ho hd
    obtain ⟨u, hu⟩ := ih { ctx with buffer := ctx.buffer ++ [c] } ho (fun x hx => hd x (by simp [hx]))
    refine ⟨u, ?_⟩
    rw [run, step, if_pos (hd c (by simp))]
    exact hu

/--
**`port` setter は、与えた 10 進数をそのまま port に入れる。**

既定 port と同じときに null になるところまで込みで `portOf` が言っている。
-/
theorem setPort_spec (u : Url) (v : String) (hc : u.cannotHaveCredentials = false)
    (hv : v.isEmpty = false) (hd : ∀ c ∈ v.toList, isAsciiDigit c = true)
    (hle : portValue v.toList ≤ 65535) :
    (u.setPort v).port = portOf u.scheme (portValue v.toList) := by
  have hne : v.toList ≠ [] := by simp_all
  have hstrip : stripTabNewline v.toList = v.toList := stripTabNewline_digits hd
  unfold Url.setPort
  rw [if_neg (by simp [hc]), if_neg (by simp [hv])]
  unfold basicUrlParseOverride
  split
  · next u' he =>
    rw [Option.getD_some]
    rw [run_port_spec none _ _ u' (by simp) (by rw [hstrip]; exact hd) he]
    rw [portDone_digits (by simp [hstrip, hne]) (by simp [hstrip]; omega)]
    simp [portSet, hstrip]
  · next hnone =>
    exfalso
    obtain ⟨u', hu'⟩ := run_port_ok none (stripTabNewline v.toList)
      { url := u, over := some SOverride.port } (by simp) (by rw [hstrip]; exact hd)
    exact hnone u' hu'

/-! ### protocol

`protocol` setter は scheme start state から scheme state へ入り、`:` で `schemeOverride` に着く。
入力を `v ++ ":"` にしているので、`:` は必ず最後に一つだけある。
-/

theorem run_schemeStart_step (base : Option Url) (ctx : PCtx) (c : Char) (rest : List Char)
    (ha : isAsciiAlpha c = true) :
    run base .schemeStart (c :: rest) ctx
      = run base .scheme rest { ctx with buffer := ctx.buffer ++ [asciiLowerChar c] } := by
  rw [run, step, if_pos ha]
  simp [asciiLowercase]

theorem run_scheme_eq (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ctx.over.isSome = true → (∀ c ∈ input, isAsciiAlphanumeric c = true) →
    run base .scheme (input ++ [':']) ctx
      = schemeOverride { ctx with buffer := ctx.buffer ++ input.map asciiLowerChar } := by
  intro input
  induction input with
  | nil =>
    intro ctx ho _
    simp only [List.nil_append, List.map_nil, List.append_nil]
    rw [run, step, if_neg (by decide), if_pos (by decide), if_pos ho]
  | cons c rest ih =>
    intro ctx ho hd
    simp only [List.cons_append]
    rw [run, step, if_pos (by simp [hd c (by simp)])]
    rw [ih { ctx with buffer := ctx.buffer ++ (asciiLowercase (String.ofList [c])).toList } ho
        (fun x hx => hd x (by simp [hx]))]
    simp [asciiLowercase]

theorem schemeOverride_ok (ctx : PCtx) : ∃ u, schemeOverride ctx = .ok u := by
  simp +zetaDelta only [schemeOverride]
  repeat' split
  all_goals exact ⟨_, rfl⟩

theorem schemeOverride_spec {ctx : PCtx} {u : Url}
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = ctx.url.isSpecial)
    (hf : String.ofList ctx.buffer = "file" →
      ctx.url.includesCredentials = false ∧ ctx.url.port = none)
    (hfe : ¬(ctx.url.scheme = "file" ∧ ctx.url.host = some Host.empty))
    (h : schemeOverride ctx = .ok u) : u.scheme = String.ofList ctx.buffer := by
  have g1 : ¬((ctx.url.isSpecial && !isSpecialScheme (String.ofList ctx.buffer)) = true) := by
    rw [← hsp]; cases isSpecialScheme (String.ofList ctx.buffer) <;> simp
  have g2 : ¬((!ctx.url.isSpecial && isSpecialScheme (String.ofList ctx.buffer)) = true) := by
    rw [← hsp]; cases isSpecialScheme (String.ofList ctx.buffer) <;> simp
  have g3 : ¬(((ctx.url.includesCredentials || ctx.url.port.isSome)
      && (String.ofList ctx.buffer == "file")) = true) := by
    cases hb : (String.ofList ctx.buffer == "file") with
    | false => simp
    | true => have := hf (by simpa using hb); simp [this.1, this.2]
  have g4 : ¬((ctx.url.scheme == "file" && ctx.url.host == some Host.empty) = true) := by
    simp only [Bool.and_eq_true, beq_iff_eq]; exact hfe
  simp +zetaDelta only [schemeOverride] at h
  rw [if_neg g1, if_neg g2, if_neg g3, if_neg g4] at h
  split at h <;> rw [← PResult.ok.inj h]

/--
**`protocol` setter は、与えた scheme を小文字にしてそのまま入れる。**

`setProtocol_valid` は「壊さない」しか言わない。ここは肯定側である。
仮定は §4.4 scheme state の override 分岐の四つの門をそのまま写したものである。
-/
theorem setProtocol_spec (u : Url) (v : String) (c : Char) (rest : List Char)
    (hv : v.toList = c :: rest) (ha : isAsciiAlpha c = true)
    (hr : ∀ x ∈ rest, isAsciiAlphanumeric x = true)
    (hsp : isSpecialScheme (asciiLowercase v) = u.isSpecial)
    (hf : asciiLowercase v = "file" → u.includesCredentials = false ∧ u.port = none)
    (hfe : ¬(u.scheme = "file" ∧ u.host = some Host.empty)) :
    (u.setProtocol v).scheme = asciiLowercase v := by
  have hrange : ∀ x ∈ c :: rest ++ [':'], x.toNat ≠ 0x09 ∧ x.toNat ≠ 0x0A ∧ x.toNat ≠ 0x0D := by
    intro x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | hx) | rfl
    · simp only [isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      omega
    · have := hr x hx
      simp only [isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
        isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    · decide
  have hinput : stripTabNewline (v ++ ":").toList = c :: (rest ++ [':']) := by
    have : (v ++ ":").toList = c :: (rest ++ [':']) := by
      rw [String.toList_append, hv]; rfl
    rw [this]
    exact stripTabNewline_eq_self (by simpa using hrange)
  have hbuf : String.ofList ([] ++ [asciiLowerChar c] ++ rest.map asciiLowerChar)
      = asciiLowercase v := by
    simp [asciiLowercase, hv]
  unfold Url.setProtocol basicUrlParseOverride
  simp only [SOverride.start, hinput]
  rw [run_schemeStart_step none _ c (rest ++ [':']) ha,
    run_scheme_eq none rest _ (by simp) hr]
  obtain ⟨u', hu'⟩ := schemeOverride_ok
    { url := u, buffer := [] ++ [asciiLowerChar c] ++ rest.map asciiLowerChar,
      over := some SOverride.scheme }
  rw [hu', Option.getD_some]
  rw [schemeOverride_spec (by rw [hbuf]; exact hsp) (by rw [hbuf]; exact hf) hfe hu']
  exact hbuf

/-! ### pathname

`pathname` setter は path start state から path state へ入る。override があるので
`?` と `#` は segment の一部になり、query state や fragment state へは移らない。
-/

/-- path state が buffer に積む形。 -/
def pathEncode (l : List Char) : List Char :=
  l.flatMap (fun c => (encChar pathSet c).toList)

/-- override 付きの path state は、区切りを含まない入力を一つの segment にする。 -/
theorem run_path_seg (base : Option Url) : ∀ (seg : List Char) (ctx : PCtx),
    ctx.over.isSome = true → (∀ c ∈ seg, c ≠ '/' ∧ c ≠ '\\') →
    run base .path seg ctx
      = .ok (pathStepUrl ctx.url false (ctx.buffer ++ pathEncode seg)) := by
  intro seg
  induction seg with
  | nil => intro ctx _ _; rw [run, step]; simp [pathEncode]
  | cons c rest ih =>
    intro ctx ho hs
    have h1 := (hs c (by simp)).1
    have h2 := (hs c (by simp)).2
    rw [run, step, if_neg (by simp [h1, h2, over_isNone_false ho])]
    rw [ih { ctx with buffer := ctx.buffer ++ (encChar pathSet c).toList } ho
      (fun x hx => hs x (by simp [hx]))]
    simp [pathEncode]

/-- override 付きの path start state は、先頭の `/` を一つ落として path state へ渡す。 -/
theorem run_pathStart_step (base : Option Url) (ctx : PCtx) (ch : Char) (rest : List Char)
    (ho : ctx.over.isSome = true) (hb : ch ≠ '\\') :
    run base .pathStart (ch :: rest) ctx
      = if ch = '/' then run base .path rest ctx else run base .path (ch :: rest) ctx := by
  rw [run, step]
  by_cases hs : ctx.url.isSpecial = true
  · by_cases hc : ch = '/'
    · subst hc; simp [hs]
    · simp [hs, hc, hb]
  · simp only [Bool.not_eq_true] at hs
    by_cases hc : ch = '/'
    · subst hc; simp [hs, over_isNone_false ho]
    · simp [hs, hc, over_isNone_false ho]

/--
**`pathname` setter は、与えた segment を percent-encode してそのまま入れる。**

区切りを含まない一 segment の場合である。`.` と `..` は落ちたり縮めたりするので除く。
`file` URL は先頭 segment の `c|` を `c:` に直すのでこれも除く。
-/
theorem setPathname_spec (u : Url) (v : String) (seg : List Char)
    (hop : u.hasOpaquePath = false) (hv : v.toList = '/' :: seg)
    (hseg : ∀ c ∈ seg, c ≠ '/' ∧ c ≠ '\\' ∧ c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D)
    (hnf : ¬(u.scheme = "file"))
    (hsd : isSingleDot (pathEncode seg) = false)
    (hdd : isDoubleDot (pathEncode seg) = false) :
    (u.setPathname v).path = .list [String.ofList (pathEncode seg)] := by
  have hstrip : stripTabNewline v.toList = '/' :: seg := by
    rw [hv]
    refine stripTabNewline_eq_self ?_
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact ⟨(hseg c hc).2.2.1, (hseg c hc).2.2.2⟩
  unfold Url.setPathname
  rw [if_neg (by simp [hop])]
  simp only [basicUrlParseOverride, SOverride.start, hstrip]
  rw [run_pathStart_step none _ '/' seg (by simp) (by decide), if_pos rfl]
  rw [run_path_seg none seg _ (by simp) (fun c hc => ⟨(hseg c hc).1, (hseg c hc).2.1⟩)]
  simp only [Option.getD_some]
  unfold pathStepUrl
  rw [if_neg (by simp [hdd]), if_neg (by simp [hsd])]
  simp [appendSegment, pathStepUrl.windowsDriveBuffer, hnf]

/-! ### host / hostname

`host` setter と `hostname` setter は同じ host state から入る。`:` を含まない入力では
二つの違い（port を読むかどうか）が出ないので、同じ形の定理になる。
-/

/-- host state が素直に buffer へ積む文字。区切りと bracket と tab/newline を除く。 -/
def plainHostChar (c : Char) : Bool :=
  c != ':' && c != '/' && c != '?' && c != '#' && c != '\\' && c != '[' && c != ']' &&
    c.toNat != 0x09 && c.toNat != 0x0A && c.toNat != 0x0D

theorem plainHostChar_spec {c : Char} (h : plainHostChar c = true) :
    c ≠ ':' ∧ c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '[' ∧ c ≠ ']' ∧
      c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [plainHostChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- override 付きの host state は、区切りを含まない入力をそのまま `hostParser` に渡す。 -/
theorem run_host_seg (base : Option Url) : ∀ (seg : List Char) (ctx : PCtx),
    ctx.over.isSome = true → ¬(ctx.url.scheme = "file") → ctx.insideBrackets = false →
    (∀ c ∈ seg, plainHostChar c = true) → ctx.buffer ++ seg ≠ [] →
    run base .host seg ctx
      = (match hostParser ctx.toAscii (ctx.buffer ++ seg) (!ctx.url.isSpecial) with
         | none => .ok ctx.url
         | some h => .ok { ctx.url with host := some h }) := by
  intro seg
  induction seg with
  | nil =>
    intro ctx ho hnf hib _ hne
    simp only [List.append_nil] at hne ⊢
    have hbne : ctx.buffer.isEmpty = false := by
      cases hb : ctx.buffer with
      | nil => exact absurd hb hne
      | cons => rfl
    rw [run, step]
    rw [if_neg (by simp [hnf]), if_neg (by simp), if_pos (by simp [isTerminator]),
      if_neg (by simp [hbne]), if_neg (by simp [hbne])]
    cases hp : hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
    | none => simpa using fail_over ho
    | some h => simp [ho]
  | cons c rest ih =>
    intro ctx ho hnf hib hs hne
    have hc := plainHostChar_spec (hs c (by simp))
    rw [run, step]
    rw [if_neg (by simp [hnf]), if_neg (by simp [hc.1]),
      if_neg (by simp [isTerminator, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1])]
    have hib2 : (if (c == '[') = true then true else if (c == ']') = true then false
        else ctx.insideBrackets) = false := by
      simp [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hib]
    simp +zetaDelta only [hib2]
    rw [ih { ctx with buffer := ctx.buffer ++ [c], insideBrackets := false } ho hnf rfl
      (fun x hx => hs x (by simp [hx])) (by simp)]
    simp

/-- plain な文字だけなら前処理で変わらない。 -/
theorem stripTabNewline_host {l : List Char} (h : ∀ c ∈ l, plainHostChar c = true) :
    stripTabNewline l = l :=
  stripTabNewline_eq_self fun c hc => by
    have hx := plainHostChar_spec (h c hc)
    exact ⟨hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2⟩

/--
**`hostname` setter は、`hostParser` が返した host をそのまま入れる。**

`:` を含まない入力の場合である（`:` は hostname setter ではそこで打ち切られる）。
host の中身の意味は §3.2 host parser に委ねてある。
-/
theorem setHostname_spec (u : Url) (v : String) (toAscii : List Char → Option String) (h : Host)
    (hop : u.hasOpaquePath = false) (hnf : ¬(u.scheme = "file"))
    (hc : ∀ c ∈ v.toList, plainHostChar c = true) (hne : v.toList ≠ [])
    (hh : hostParser toAscii v.toList (!u.isSpecial) = some h) :
    (u.setHostname v toAscii).host = some h := by
  unfold Url.setHostname
  rw [if_neg (by simp [hop])]
  simp only [basicUrlParseOverride, SOverride.start, stripTabNewline_host hc]
  rw [run_host_seg none v.toList { url := u, over := some SOverride.hostname, toAscii } (by simp)
    hnf rfl hc (by simpa using hne)]
  simp only [List.nil_append, hh]
  rfl

/-- **`host` setter も、`:` を含まない入力なら同じである。** -/
theorem setHost_spec (u : Url) (v : String) (toAscii : List Char → Option String) (h : Host)
    (hop : u.hasOpaquePath = false) (hnf : ¬(u.scheme = "file"))
    (hc : ∀ c ∈ v.toList, plainHostChar c = true) (hne : v.toList ≠ [])
    (hh : hostParser toAscii v.toList (!u.isSpecial) = some h) :
    (u.setHost v toAscii).host = some h := by
  unfold Url.setHost
  rw [if_neg (by simp [hop])]
  simp only [basicUrlParseOverride, SOverride.start, stripTabNewline_host hc]
  rw [run_host_seg none v.toList { url := u, over := some SOverride.host, toAscii } (by simp)
    hnf rfl hc (by simpa using hne)]
  simp only [List.nil_append, hh]
  rfl

end Url
