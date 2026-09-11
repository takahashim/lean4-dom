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

残りの setter（`protocol` / `host` / `hostname` / 非空の `port` / `pathname`）は
host や port や path を書くので、`run_valid` を override 付きに広げる必要がある。
そちらは `docs/url-status.md` の未着手にある。
-/

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

end Url
