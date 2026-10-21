import Url.ParseImage
import Url.Strict

/-!
# §4.1 の残りの三条件

`ValidUrl` に入れていない §4.1 の条件（`Url/Strict.lean` の `checkStrictUrl`）を定理に上げる。

* host が空なら credentials は持てない。
* special な URL の host は null でない。
* IPv6 address は 8 piece で、各 piece は 16 bit に収まる。

`ValidUrl` そのものには足さず、`StrictUrl` として別に立てる。`ValidUrl` に足すと、
`PInv` から `ValidUrl` が出なくなり（前の二つは parse の途中で破れる）、
`basicUrlParse_valid` が `CInv` に依存する向きに変わるためである。

**parse の側**は `canonicalUrl` から出る（`strictConds_of_canonical`）。前の二つは `canonicalUrl` の連言
そのもので、IPv6 の条件は host の条件（serialize して読み直すと戻る）から出る。
読み直した結果は IPv6 parser の出力なので、`ipv6Parser_length` と `ipv6Parser_lt` が使える。

**setter の側**は `Url/ApiValid.lean` と同じく、override 付きで通る state ごとに短い帰納法で閉じる。
多くの state は scheme・host・credentials を変えない（`Frame`）。変えるのは scheme state
（special かどうかは変えられない）と host state / file host state（host parser の出力か empty host を書く）だけである。
-/

-- `cases he : ...` の枝ごとに `he` が要るかどうかが違うので、linter を切る。
set_option linter.unusedSimpArgs false

namespace Url

open Infra

/-- §4.1 のうち `ValidUrl` に入れていない三条件。 -/
structure StrictConds (u : Url) : Prop where
  /-- §4.1「host が空なら credentials は持てない」。 -/
  emptyHostNoCredentials : u.host = some Host.empty → u.includesCredentials = false
  /-- §4.1「special な URL の host は null でない」。 -/
  specialHasHost : u.isSpecial = true → u.host.isSome = true
  /-- §4.1「IPv6 address は 128 bit」。8 piece で、各 piece は 16 bit。 -/
  ipv6 : ∀ a, u.host = some (.ipv6 a) → a.length = 8 ∧ ∀ p ∈ a, p < 65536

/-- **§4.1 の条件のすべて。** `ValidUrl` に残りの三条件を足したもの。 -/
structure StrictUrl (u : Url) : Prop extends ValidUrl u, StrictConds u

/-- **`checkStrictUrl` は `StrictConds` の boolean 版である。** -/
theorem checkStrictUrl_iff (u : Url) : checkStrictUrl u = true ↔ StrictConds u := by
  constructor
  · intro h
    simp only [checkStrictUrl, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨fun he => ?_, fun hs => ?_, fun a ha => ?_⟩
    · simp only [he] at h1; simpa using h1
    · simp only [hs, Bool.not_true, Bool.false_or] at h2; exact h2
    · simp only [ipv6Ok, ha, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        decide_eq_true_eq] at h3
      exact h3
  · intro hs
    simp only [checkStrictUrl, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases hh : u.host with
      | none => simp
      | some h =>
        cases h with
        | empty => simp [hs.emptyHostNoCredentials hh]
        | _ => simp
    · cases hsp : u.isSpecial with
      | false => simp
      | true => simp [hs.specialHasHost hsp]
    · unfold ipv6Ok
      cases hh : u.host with
      | none => rfl
      | some h =>
        cases h with
        | ipv6 a =>
          obtain ⟨hl, hp⟩ := hs.ipv6 a hh
          simpa [hl] using hp
        | _ => rfl

/-! ## parse の側 -/

/-- host parser が返す IPv6 address は 8 piece で 16 bit に収まる。 -/
theorem ipv6_of_hostParser {f : List Char → Option String} {buf : List Char} {b : Bool}
    {h : Host} (hp : hostParser f buf b = some h) :
    ∀ a, h = .ipv6 a → a.length = 8 ∧ ∀ p ∈ a, p < 65536 := by
  intro a ha
  subst ha
  obtain ⟨s, hs⟩ := hostParser_ipv6_eq hp
  exact ⟨ipv6Parser_length hs, ipv6Parser_lt hs⟩

/-- **canonical な record は三条件を満たす。** -/
theorem strictConds_of_canonical {u : Url} {t : List Char → Option String}
    (hc : canonicalUrl u t = true) : StrictConds u := by
  have p := canonical_parts hc
  refine ⟨p.emptyNoCred, p.specialHost, fun a ha => ?_⟩
  exact ipv6_of_hostParser (p.hostIdem _ ha (by simp)) a rfl

/-- **parse が返す record は §4.1 の条件をすべて満たす。** -/
theorem basicUrlParse_strict {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option Url}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b t = true)
    {u : Url} (h : basicUrlParse input base t = some u) : StrictUrl u :=
  { toValidUrl := basicUrlParse_valid hb h
    toStrictConds := strictConds_of_canonical (basicUrlParse_canonical htok hb hbc h) }

/-- `URL(url, base)` の入口についても同じ。 -/
theorem parseUrl_strict {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option String} {u : Url}
    (h : parseUrl input base t = some u) : StrictUrl u :=
  { toValidUrl := parseUrl_valid h
    toStrictConds := strictConds_of_canonical (parseUrl_canonical htok h) }

/-! ## setter の側

多くの state は scheme・host・credentials を変えない。それを `Frame` として持ち回る。
-/

/-- scheme・host・credentials が変わらないこと。三条件はこれだけを見る。 -/
def Frame (u u' : Url) : Prop :=
  u'.scheme = u.scheme ∧ u'.host = u.host ∧ u'.includesCredentials = u.includesCredentials

theorem Frame.refl (u : Url) : Frame u u := ⟨rfl, rfl, rfl⟩

theorem Frame.trans {u v w : Url} (h1 : Frame u v) (h2 : Frame v w) : Frame u w :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem StrictConds.frame {u u' : Url} (h : StrictConds u) (hf : Frame u u') : StrictConds u' := by
  obtain ⟨hs, hh, hc⟩ := hf
  refine ⟨fun he => ?_, fun hsp => ?_, fun a ha => ?_⟩
  · rw [hc]; exact h.emptyHostNoCredentials (hh ▸ he)
  · rw [hh]; exact h.specialHasHost (by simpa [Url.isSpecial, hs] using hsp)
  · exact h.ipv6 a (hh ▸ ha)

/-- override 付きの port state は port しか変えない。 -/
theorem run_port_frame (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .port input ctx = .ok u → ctx.over.isSome = true → Frame ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact Frame.refl _
    · next ctx2 hpd =>
      try rw [if_pos hov] at h
      obtain ⟨p, hu, _⟩ := portDone_spec hpd
      rw [← PResult.ok.inj h, hu]
      exact ⟨rfl, rfl, rfl⟩
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · have := run_port_frame base t _ u h hov
      exact this
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact Frame.refl _
        · next ctx2 hpd =>
          try rw [if_pos hov] at h
          obtain ⟨p, hu, _⟩ := portDone_spec hpd
          rw [← PResult.ok.inj h, hu]
          exact ⟨rfl, rfl, rfl⟩
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact Frame.refl _

theorem frame_pathStepUrl (u : Url) (slash : Bool) (buf : List Char) :
    Frame u (pathStepUrl u slash buf) := ⟨by simp, by simp, by simp⟩

theorem frame_appendSegment (u : Url) (s : String) : Frame u (appendSegment u s) :=
  ⟨by simp, by simp, by simp⟩

/-- override 付きの path state は path しか変えない。 -/
theorem run_path_frame (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .path input ctx = .ok u → ctx.over.isSome = true → Frame ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · rw [← PResult.ok.inj h]; exact frame_pathStepUrl _ _ _
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact Frame.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.or_false] at h
    split at h
    · split at h
      · simp_all
      · simp_all
      · simp_all
      · exact (frame_pathStepUrl _ _ _).trans (run_path_frame base t _ u h hov)
    · have := run_path_frame base t _ u h hov
      exact this

/-- override 付きの path start state も同じ。 -/
theorem run_pathStart_frame (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .pathStart input ctx = .ok u → ctx.over.isSome = true → Frame ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_frame base [] _ u h hov
      · exact run_path_frame base [] _ u h hov
    · split at h
      · rw [← PResult.ok.inj h]; exact frame_appendSegment _ _
      · rw [← PResult.ok.inj h]; exact Frame.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · exact run_path_frame base t _ u h hov
      · exact run_path_frame base (ch :: t) _ u h hov
    · split at h
      · exact run_path_frame base t _ u h hov
      · exact run_path_frame base (ch :: t) _ u h hov

/-! ### host を書く state -/

/-- host を書き込んでも三条件が保たれる条件。 -/
theorem StrictConds.setHost {u : Url} (_h : StrictConds u) (hst : Host)
    (he : hst = Host.empty → u.includesCredentials = false)
    (h6 : ∀ a, hst = .ipv6 a → a.length = 8 ∧ ∀ p ∈ a, p < 65536) :
    StrictConds { u with host := some hst } :=
  ⟨fun hx => he (Option.some.inj hx), fun _ => rfl, fun a hx => h6 a (Option.some.inj hx)⟩

/-- override 付きの file host state は三条件を保つ。`file` は credentials を持てない。 -/
theorem run_fileHost_strict (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .fileHost input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → StrictConds ctx.url →
    ctx.url.scheme = "file" → StrictConds u
  | [], ctx, u, h, hov, hv, hs, hf => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]
        exact hs.setHost _ (fun _ => hv.fileNoCredentials hf) (fun a ha => by cases ha)
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
        · next hst hp =>
          rw [← PResult.ok.inj h]
          refine hs.setHost _ (fun _ => hv.fileNoCredentials hf) ?_
          split
          · intro a ha; cases ha
          · exact ipv6_of_hostParser hp
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
  | ch :: t, ctx, u, h, hov, hv, hs, hf => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]
        exact hs.setHost _ (fun _ => hv.fileNoCredentials hf) (fun a ha => by cases ha)
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
        · next hst hp =>
          rw [← PResult.ok.inj h]
          refine hs.setHost _ (fun _ => hv.fileNoCredentials hf) ?_
          split
          · intro a ha; cases ha
          · exact ipv6_of_hostParser hp
    · exact run_fileHost_strict base t _ u h hov hv hs hf

/--
override 付きで host を空にするのは、credentials も port も無いときだけ（host state の終端の guard）。
-/
theorem empty_host_creds {ctx : PCtx} {hst : Host}
    (hg : ¬(ctx.buffer.isEmpty && (ctx.url.includesCredentials || ctx.url.port.isSome)) = true)
    (hp : hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) = some hst)
    (he : hst = Host.empty) : ctx.url.includesCredentials = false := by
  rw [he] at hp
  have hb : ctx.buffer.isEmpty = true := by rw [hostParser_empty hp]; rfl
  rw [hb] at hg
  simp only [Bool.true_and, Bool.or_eq_true, not_or] at hg
  simpa using hg.1

/-- override 付きの host state は三条件を保つ。 -/
theorem run_host_strict (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .host input ctx = .ok u →
    ctx.over.isSome = true → ValidUrl ctx.url → StrictConds ctx.url → StrictConds u
  | [], ctx, u, h, hov, hv, hs => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · next gf => exact run_fileHost_strict base [] _ u h hov hv hs (by simpa using gf)
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
        · split at h
          · rw [← PResult.ok.inj h]; exact hs
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
            · next hst hp =>
              refine (hs.setHost hst ?_ (ipv6_of_hostParser hp)).frame
                (run_port_frame base [] _ u h hov)
              intro he; exact absurd he (host_ne_empty (by assumption) hp)
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
          · split at h
            · rw [← PResult.ok.inj h]; exact hs
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
              · next hst hp =>
                rw [← PResult.ok.inj h]
                exact hs.setHost hst (empty_host_creds (by assumption) hp) (ipv6_of_hostParser hp)
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
  | ch :: t, ctx, u, h, hov, hv, hs => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · next gf => exact run_fileHost_strict base (ch :: t) _ u h hov hv hs (by simpa using gf)
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
        · split at h
          · rw [← PResult.ok.inj h]; exact hs
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
            · next hst hp =>
              refine (hs.setHost hst ?_ (ipv6_of_hostParser hp)).frame
                (run_port_frame base t _ u h hov)
              intro he; exact absurd he (host_ne_empty (by assumption) hp)
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
          · split at h
            · rw [← PResult.ok.inj h]; exact hs
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
              · next hst hp =>
                rw [← PResult.ok.inj h]
                exact hs.setHost hst (empty_host_creds (by assumption) hp) (ipv6_of_hostParser hp)
        · exact run_host_strict base t _ u h hov hv hs

/-! ### scheme state -/

/--
protocol setter の本体は三条件を保つ。

scheme を書き換えるのは special かどうかが変わらないときだけなので（`schemeOverride` の一つ目と
二つ目の guard）、「special なら host がある」は元の record から運べる。host と credentials は変えない。
-/
theorem schemeOverride_strict {ctx : PCtx} (hs : StrictConds ctx.url) (u : Url)
    (h : schemeOverride ctx = .ok u) : StrictConds u := by
  simp +zetaDelta only [schemeOverride] at h
  split at h
  · rw [← PResult.ok.inj h]; exact hs
  · next g1 =>
    split at h
    · rw [← PResult.ok.inj h]; exact hs
    · next g2 =>
      have hsp : isSpecialScheme (String.ofList ctx.buffer) = ctx.url.isSpecial := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at g1 g2
        cases hs : ctx.url.isSpecial <;>
          cases hb : isSpecialScheme (String.ofList ctx.buffer) <;> simp_all
      have hk : StrictConds { ctx.url with scheme := String.ofList ctx.buffer } :=
        ⟨hs.emptyHostNoCredentials, fun hx => hs.specialHasHost (by
          simpa [Url.isSpecial, hsp] using hx), hs.ipv6⟩
      split at h
      · rw [← PResult.ok.inj h]; exact hs
      · split at h
        · rw [← PResult.ok.inj h]; exact hs
        · split at h
          · rw [← PResult.ok.inj h]
            exact ⟨hk.emptyHostNoCredentials, hk.specialHasHost, hk.ipv6⟩
          · rw [← PResult.ok.inj h]; exact hk

theorem run_scheme_strict (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .scheme input ctx = .ok u →
    ctx.over.isSome = true → StrictConds ctx.url → StrictConds u
  | [], ctx, u, h, hov, hs => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
  | ch :: t, ctx, u, h, hov, hs => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · exact run_scheme_strict base t _ u h hov hs
    · split at h
      · exact schemeOverride_strict hs u h
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs

theorem run_schemeStart_strict (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .schemeStart input ctx = .ok u →
    ctx.over.isSome = true → StrictConds ctx.url → StrictConds u
  | [], ctx, u, h, hov, hs => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs
  | ch :: t, ctx, u, h, hov, hs => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · exact run_scheme_strict base t _ u h hov hs
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact hs

/-! ### setter ごと -/

/-- **`protocol` setter は三条件を保つ。** -/
theorem setProtocol_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setProtocol v) := by
  unfold Url.setProtocol
  cases he : basicUrlParseOverride (v ++ ":") u .scheme with
  | none => simpa [he] using h
  | some u' =>
    simp only [he, Option.getD_some]
    unfold basicUrlParseOverride at he
    split at he
    · next w hw =>
      rw [← Option.some.inj he]
      exact run_schemeStart_strict none _ _ w hw rfl h
    · simp at he

/-- **`username` setter は三条件を保つ。** credentials を書けるのは host が空でないときだけ。 -/
theorem setUsername_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setUsername v) := by
  unfold Url.setUsername
  split
  · exact h
  · next hc =>
    refine ⟨fun he => ?_, h.specialHasHost, h.ipv6⟩
    simp only [Url.cannotHaveCredentials, Bool.or_eq_true, beq_iff_eq, not_or] at hc
    exact absurd he hc.1.2

/-- **`password` setter は三条件を保つ。** -/
theorem setPassword_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setPassword v) := by
  unfold Url.setPassword
  split
  · exact h
  · next hc =>
    refine ⟨fun he => ?_, h.specialHasHost, h.ipv6⟩
    simp only [Url.cannotHaveCredentials, Bool.or_eq_true, beq_iff_eq, not_or] at hc
    exact absurd he hc.1.2

/-- **`host` setter は三条件を保つ。** -/
theorem setHost_strict {u : Url} (hv : ValidUrl u) (h : StrictConds u) (v : String)
    (toAscii : List Char → Option String) : StrictConds (u.setHost v toAscii) := by
  unfold Url.setHost
  split
  · exact h
  · cases he : basicUrlParseOverride v u .host toAscii with
    | none => simpa [he] using h
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_host_strict none _ _ w hw rfl hv h
      · simp at he

/-- **`hostname` setter は三条件を保つ。** -/
theorem setHostname_strict {u : Url} (hv : ValidUrl u) (h : StrictConds u) (v : String)
    (toAscii : List Char → Option String) : StrictConds (u.setHostname v toAscii) := by
  unfold Url.setHostname
  split
  · exact h
  · cases he : basicUrlParseOverride v u .hostname toAscii with
    | none => simpa [he] using h
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact run_host_strict none _ _ w hw rfl hv h
      · simp at he

/-- **`port` setter は三条件を保つ。** port しか変えない。 -/
theorem setPort_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setPort v) := by
  unfold Url.setPort
  split
  · exact h
  · split
    · exact h.frame ⟨rfl, rfl, rfl⟩
    · cases he : basicUrlParseOverride v u .port with
      | none => simpa [he] using h
      | some u' =>
        simp only [he, Option.getD_some]
        unfold basicUrlParseOverride at he
        split at he
        · next w hw =>
          rw [← Option.some.inj he]
          exact h.frame (run_port_frame none _ _ w hw rfl)
        · simp at he

/-- **`pathname` setter は三条件を保つ。** path しか変えない。 -/
theorem setPathname_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setPathname v) := by
  unfold Url.setPathname
  split
  · exact h
  · have h0 : StrictConds { u with path := Path.list [] } := h.frame ⟨rfl, rfl, rfl⟩
    cases he : basicUrlParseOverride v { u with path := Path.list [] } .path with
    | none => simpa [he] using h0
    | some u' =>
      simp only [he, Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next w hw =>
        rw [← Option.some.inj he]
        exact h0.frame (run_pathStart_frame none _ _ w hw rfl)
      · simp at he

/-- **`search` setter は三条件を保つ。** query しか変えない。 -/
theorem setSearch_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setSearch v) := by
  have h0 : ∀ q, StrictConds { u with query := q } := fun _ => h.frame ⟨rfl, rfl, rfl⟩
  unfold Url.setSearch
  split
  · exact h0 none
  · cases he : basicUrlParseOverride (dropLeading '?' v) { u with query := some "" } .query with
    | none => simpa [he] using h0 (some "")
    | some u' =>
      obtain ⟨q, hq⟩ := basicUrlParseOverride_query _ _ _ he
      simp only [Option.getD_some, hq]
      exact h.frame ⟨rfl, rfl, rfl⟩

/-- **`hash` setter は三条件を保つ。** fragment しか変えない。 -/
theorem setHash_strict {u : Url} (h : StrictConds u) (v : String) :
    StrictConds (u.setHash v) := by
  have h0 : ∀ f, StrictConds { u with fragment := f } := fun _ => h.frame ⟨rfl, rfl, rfl⟩
  unfold Url.setHash
  split
  · exact h0 none
  · cases he : basicUrlParseOverride (dropLeading '#' v) { u with fragment := some "" } .fragment with
    | none => simpa [he] using h0 (some "")
    | some u' =>
      obtain ⟨f, hf⟩ := basicUrlParseOverride_fragment _ _ _ he
      simp only [Option.getD_some, hf]
      exact h.frame ⟨rfl, rfl, rfl⟩

/--
**どの IDL setter も §4.1 の条件をすべて保つ。**

`href` は parse し直すので `basicUrlParse_strict` に乗り、ToASCII に `ToAsciiOk` を要る。
ほかの setter は ToASCII に依らない。
-/
theorem setAttr_strict {t : List Char → Option String} (htok : ToAsciiOk t)
    {u : Url} (h : StrictUrl u) (name v : String) (u' : Url)
    (hs : u.setAttr name v t = some u') : StrictUrl u' := by
  have hv : ValidUrl u' := setAttr_valid h.toValidUrl name v t u' hs
  refine { toValidUrl := hv, toStrictConds := ?_ }
  have hc := h.toStrictConds
  unfold Url.setAttr at hs
  split at hs
  · rw [← Option.some.inj hs]
    unfold Url.setHref
    cases hp : basicUrlParse v none t with
    | none => simpa [hp] using hc
    | some w =>
      simp only [hp, Option.getD_some]
      exact (basicUrlParse_strict htok (fun b hb => absurd hb (by simp))
        (fun b hb => absurd hb (by simp)) hp).toStrictConds
  · rw [← Option.some.inj hs]; exact setProtocol_strict hc v
  · rw [← Option.some.inj hs]; exact setUsername_strict hc v
  · rw [← Option.some.inj hs]; exact setPassword_strict hc v
  · rw [← Option.some.inj hs]; exact setHost_strict h.toValidUrl hc v _
  · rw [← Option.some.inj hs]; exact setHostname_strict h.toValidUrl hc v _
  · rw [← Option.some.inj hs]; exact setPort_strict hc v
  · rw [← Option.some.inj hs]; exact setPathname_strict hc v
  · rw [← Option.some.inj hs]; exact setSearch_strict hc v
  · rw [← Option.some.inj hs]; exact setHash_strict hc v
  · exact absurd hs (by simp)

/-! ## opaque path の末尾の空白

§4.1 の条件ではないが、parser と setter から到達できる record の性質として、
**opaque path は生の U+0020 で終わらない**。opaque path state は、空白の次が `?` か `#` なら
`%20` を、そうでなければ U+0020 を書く。入力の末尾の空白は前処理が落としているので、
U+0020 の後には必ず別の文字が続く（`CInv.trailing`）。

固定版の URL Standard（whatwg/url 8e14777c）の `search` / `hash` setter と
`URLSearchParams` の update steps は、query / fragment を null にするだけで path に触れない。
旧版にあった「potentially strip trailing spaces from an opaque path」は固定版には無い。
ここではこの性質が setter を通しても保たれることを示し、その手順が無くても
到達できる record の上では serialize の結果が変わらないことの根拠にする。

`ValidUrl` と `StrictConds` の保存（`setSearch_valid` ほか）はこの性質を要らない。
二つの setter は path に触れないからである（`setSearch_path`、`setHash_path`）。
-/

/-- opaque path が生の U+0020 で終わらない。 -/
def OpaqueNoTrailingSpace (u : Url) : Prop :=
  ∀ o, u.path = .opaque o → o.toList.getLast? ≠ some ' '

/-- **parse が返す record の opaque path は生の U+0020 で終わらない。** -/
theorem parseUrl_opaqueNoTrailingSpace {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option String} {u : Url}
    (h : parseUrl input base t = some u) : OpaqueNoTrailingSpace u :=
  (canonical_parts (parseUrl_canonical htok h)).trailing

/-- `basicUrlParse` を base 無しで呼んだ場合も同じ。`href` setter が使う。 -/
theorem basicUrlParse_opaqueNoTrailingSpace {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {u : Url}
    (h : basicUrlParse input none t = some u) : OpaqueNoTrailingSpace u :=
  (canonical_parts (basicUrlParse_canonical htok (fun b hb => absurd hb (by simp))
    (fun b hb => absurd hb (by simp)) h)).trailing

/--
opaque path を新しく作らないこと。結果の path が opaque なら、元の path と同じである。

override 付きの state はどれも opaque path を作らない（作るのは scheme state の
override 無しの枝だけ）。path を書く state も、`appendSegment` と `shortenPath` は
opaque path をそのまま返す。
-/
def PathKeep (u u' : Url) : Prop :=
  ∀ o, u'.path = .opaque o → u.path = .opaque o

theorem PathKeep.refl (u : Url) : PathKeep u u := fun _ h => h

theorem PathKeep.trans {u v w : Url} (h1 : PathKeep u v) (h2 : PathKeep v w) : PathKeep u w :=
  fun o h => h1 o (h2 o h)

theorem OpaqueNoTrailingSpace.keep {u u' : Url} (h : OpaqueNoTrailingSpace u)
    (hk : PathKeep u u') : OpaqueNoTrailingSpace u' :=
  fun o ho => h o (hk o ho)

theorem pathKeep_shortenPath (u : Url) : PathKeep u (shortenPath u) := by
  intro o ho
  unfold shortenPath at ho
  split at ho
  · exact ho
  · split at ho
    · exact ho
    · simp at ho

theorem pathKeep_appendSegment (u : Url) (s : String) : PathKeep u (appendSegment u s) := by
  intro o ho
  unfold appendSegment at ho
  split at ho
  · exact ho
  · simp at ho

theorem pathKeep_pathStepUrl (u : Url) (slash : Bool) (buf : List Char) :
    PathKeep u (pathStepUrl u slash buf) := by
  unfold pathStepUrl
  split
  · split
    · exact pathKeep_shortenPath u
    · exact (pathKeep_shortenPath u).trans (pathKeep_appendSegment _ _)
  · split
    · split
      · exact PathKeep.refl u
      · exact pathKeep_appendSegment u _
    · exact pathKeep_appendSegment u _

/-- override 付きの port state は path を変えない。 -/
theorem run_port_pathKeep (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .port input ctx = .ok u → ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
    · next ctx2 hpd =>
      try rw [if_pos hov] at h
      obtain ⟨p, hu, _⟩ := portDone_spec hpd
      rw [← PResult.ok.inj h, hu]
      exact fun _ ho => ho
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · have := run_port_pathKeep base t _ u h hov; exact this
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
        · next ctx2 hpd =>
          try rw [if_pos hov] at h
          obtain ⟨p, hu, _⟩ := portDone_spec hpd
          rw [← PResult.ok.inj h, hu]
          exact fun _ ho => ho
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _

/-- override 付きの path state は opaque path を作らない。 -/
theorem run_path_pathKeep (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .path input ctx = .ok u → ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    split at h
    · rw [← PResult.ok.inj h]; exact pathKeep_pathStepUrl _ _ _
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.or_false] at h
    split at h
    · split at h
      · simp_all
      · simp_all
      · simp_all
      · exact (pathKeep_pathStepUrl _ _ _).trans (run_path_pathKeep base t _ u h hov)
    · have := run_path_pathKeep base t _ u h hov; exact this

/-- override 付きの path start state も同じ。 -/
theorem run_pathStart_pathKeep (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .pathStart input ctx = .ok u → ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · have := run_path_pathKeep base [] _ u h hov; exact this
      · have := run_path_pathKeep base [] _ u h hov; exact this
    · split at h
      · rw [← PResult.ok.inj h]; exact pathKeep_appendSegment _ _
      · rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · split at h
      · have := run_path_pathKeep base t _ u h hov; exact this
      · exact run_path_pathKeep base (ch :: t) _ u h hov
    · split at h
      · have := run_path_pathKeep base t _ u h hov; exact this
      · exact run_path_pathKeep base (ch :: t) _ u h hov

/-- override 付きの file host state は path を変えない。 -/
theorem run_fileHost_pathKeep (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .fileHost input ctx = .ok u →
    ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact fun _ ho => ho
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
        · rw [← PResult.ok.inj h]; exact fun _ ho => ho
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [over_isNone_false hov, hov, Bool.false_and, Bool.false_eq_true, if_false,
      if_true] at h
    split at h
    · split at h
      · rw [← PResult.ok.inj h]; exact fun _ ho => ho
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
        · rw [← PResult.ok.inj h]; exact fun _ ho => ho
    · have := run_fileHost_pathKeep base t _ u h hov; exact this

/-- override 付きの host state は path を変えない。 -/
theorem run_host_pathKeep (base : Option Url) : ∀ (input : List Char) (ctx : PCtx),
    ∀ (u : Url), run base .host input ctx = .ok u →
    ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · have := run_fileHost_pathKeep base [] _ u h hov; exact this
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
        · split at h
          · rw [← PResult.ok.inj h]; exact PathKeep.refl _
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
            · have := run_port_pathKeep base [] _ u h hov; exact this
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
          · split at h
            · rw [← PResult.ok.inj h]; exact PathKeep.refl _
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
              · rw [← PResult.ok.inj h]; exact fun _ ho => ho
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, Bool.true_and, if_true] at h
    split at h
    · exact run_fileHost_pathKeep base (ch :: t) _ u h hov
    · split at h
      · split at h
        · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
        · split at h
          · rw [← PResult.ok.inj h]; exact PathKeep.refl _
          · split at h
            · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
            · have := run_port_pathKeep base t _ u h hov; exact this
      · split at h
        · split at h
          · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
          · split at h
            · rw [← PResult.ok.inj h]; exact PathKeep.refl _
            · split at h
              · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
              · rw [← PResult.ok.inj h]; exact fun _ ho => ho
        · have := run_host_pathKeep base t _ u h hov; exact this

/-- protocol setter の本体は path を変えない。 -/
theorem schemeOverride_pathKeep {ctx : PCtx} (u : Url) (h : schemeOverride ctx = .ok u) :
    PathKeep ctx.url u := by
  simp +zetaDelta only [schemeOverride] at h
  repeat' split at h
  all_goals (rw [← PResult.ok.inj h]; exact fun _ ho => ho)

theorem run_scheme_pathKeep (base : Option Url) : ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .scheme input ctx = .ok u → ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · have := run_scheme_pathKeep base t _ u h hov; exact this
    · split at h
      · exact schemeOverride_pathKeep u h
      · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _

theorem run_schemeStart_pathKeep (base : Option Url) :
    ∀ (input : List Char) (ctx : PCtx) (u : Url),
    run base .schemeStart input ctx = .ok u → ctx.over.isSome = true → PathKeep ctx.url u
  | [], ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _
  | ch :: t, ctx, u, h, hov => by
    rw [run, step] at h
    simp only [hov, if_true] at h
    split at h
    · have := run_scheme_pathKeep base t _ u h hov; exact this
    · rw [fail_over hov] at h; rw [← PResult.ok.inj h]; exact PathKeep.refl _

/-- **`search` setter は path に触れない。** 空文字列なら query を null にするだけである。 -/
theorem setSearch_path (u : Url) (v : String) : (u.setSearch v).path = u.path := by
  unfold Url.setSearch
  split
  · rfl
  · cases he : basicUrlParseOverride (dropLeading '?' v) { u with query := some "" } .query with
    | none => rfl
    | some u' =>
      obtain ⟨q, hq⟩ := basicUrlParseOverride_query _ _ _ he
      simp only [Option.getD_some, hq]

/-- **`hash` setter は path に触れない。** 空文字列なら fragment を null にするだけである。 -/
theorem setHash_path (u : Url) (v : String) : (u.setHash v).path = u.path := by
  unfold Url.setHash
  split
  · rfl
  · cases he : basicUrlParseOverride (dropLeading '#' v) { u with fragment := some "" } .fragment with
    | none => rfl
    | some u' =>
      obtain ⟨f, hf⟩ := basicUrlParseOverride_fragment _ _ _ he
      simp only [Option.getD_some, hf]

/--
**どの IDL setter を通しても、opaque path は生の U+0020 で終わらない。**

`href` は parse し直すので `basicUrlParse_opaqueNoTrailingSpace` に乗り、ToASCII に
`ToAsciiOk` を要る。ほかの setter は opaque path を新しく作らない（`PathKeep`）。
`parseUrl_opaqueNoTrailingSpace` と合わせて、parser と setter から到達できる record は
どれもこの性質を持つ。
-/
theorem setAttr_opaqueNoTrailingSpace {t : List Char → Option String} (htok : ToAsciiOk t)
    {u : Url} (h : OpaqueNoTrailingSpace u) (name v : String) (u' : Url)
    (hs : u.setAttr name v t = some u') : OpaqueNoTrailingSpace u' := by
  unfold Url.setAttr at hs
  split at hs
  · rw [← Option.some.inj hs]
    unfold Url.setHref
    cases hp : basicUrlParse v none t with
    | none => simpa [hp] using h
    | some w =>
      simp only [Option.getD_some]
      exact basicUrlParse_opaqueNoTrailingSpace htok hp
  · rw [← Option.some.inj hs]
    refine h.keep ?_
    unfold Url.setProtocol
    cases he : basicUrlParseOverride (v ++ ":") u .scheme with
    | none => exact PathKeep.refl _
    | some w =>
      simp only [Option.getD_some]
      unfold basicUrlParseOverride at he
      split at he
      · next x hx =>
        rw [← Option.some.inj he]
        exact run_schemeStart_pathKeep none _ _ x hx rfl
      · simp at he
  · rw [← Option.some.inj hs]
    unfold Url.setUsername
    split
    · exact h
    · exact h
  · rw [← Option.some.inj hs]
    unfold Url.setPassword
    split
    · exact h
    · exact h
  · rw [← Option.some.inj hs]
    refine h.keep ?_
    unfold Url.setHost
    split
    · exact PathKeep.refl _
    · cases he : basicUrlParseOverride v u .host t with
      | none => exact PathKeep.refl _
      | some w =>
        simp only [Option.getD_some]
        unfold basicUrlParseOverride at he
        split at he
        · next x hx =>
          rw [← Option.some.inj he]
          exact run_host_pathKeep none _ _ x hx rfl
        · simp at he
  · rw [← Option.some.inj hs]
    refine h.keep ?_
    unfold Url.setHostname
    split
    · exact PathKeep.refl _
    · cases he : basicUrlParseOverride v u .hostname t with
      | none => exact PathKeep.refl _
      | some w =>
        simp only [Option.getD_some]
        unfold basicUrlParseOverride at he
        split at he
        · next x hx =>
          rw [← Option.some.inj he]
          exact run_host_pathKeep none _ _ x hx rfl
        · simp at he
  · rw [← Option.some.inj hs]
    refine h.keep ?_
    unfold Url.setPort
    split
    · exact PathKeep.refl _
    · split
      · exact fun _ ho => ho
      · cases he : basicUrlParseOverride v u .port with
        | none => exact PathKeep.refl _
        | some w =>
          simp only [Option.getD_some]
          unfold basicUrlParseOverride at he
          split at he
          · next x hx =>
            rw [← Option.some.inj he]
            exact run_port_pathKeep none _ _ x hx rfl
          · simp at he
  · rw [← Option.some.inj hs]
    unfold Url.setPathname
    split
    · exact h
    · show OpaqueNoTrailingSpace ((basicUrlParseOverride v { u with path := Path.list [] } .path).getD
        { u with path := Path.list [] })
      have h0 : OpaqueNoTrailingSpace { u with path := Path.list [] } := fun _ ho => by cases ho
      cases he : basicUrlParseOverride v { u with path := Path.list [] } .path with
      | none => exact h0
      | some w =>
        simp only [Option.getD_some]
        unfold basicUrlParseOverride at he
        split at he
        · next x hx =>
          rw [← Option.some.inj he]
          exact h0.keep (run_pathStart_pathKeep none _ _ x hx rfl)
        · simp at he
  · rw [← Option.some.inj hs]
    exact fun o ho => h o (by rw [← setSearch_path u v]; exact ho)
  · rw [← Option.some.inj hs]
    exact fun o ho => h o (by rw [← setHash_path u v]; exact ho)
  · exact absurd hs (by simp)

end Url
