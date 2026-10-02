import Url.Roundtrip
import Url.StepCanonical

/-!
# parse の像

二つの向きを合わせる。

* `roundtrip_canonical`：`ValidUrl` と `canonicalUrl` を満たす record は、serialize して parse すると戻る。
* `basicUrlParse_valid` と `basicUrlParse_canonical`：parse が返す record は二つの述語を満たす。

合わせると、**parse の像は `ValidUrl ∧ canonicalUrl` にちょうど一致する**（`parse_image`）。
`canonicalUrl` は「往復の仮定」ではなく「parser が返しうる record の定義」になる。

`ValidUrl` だけを満たす record には往復が成り立たない（`a b` のまま encode していない username など）。
したがって `roundtrip_canonical` の `canonicalUrl` の仮定は外せない。外せるのは、
「parse の結果である」という仮定に置き換えたときである（`parse_serialize_of_parse`）。

ToASCII は `ToAsciiOk` を満たすものなら一般でよい（`Url/HostRoundtrip.lean`）。
既定の `asciiDomainToASCII` は `toAsciiOk_ascii` で満たす。
-/

namespace Url

/-- `ToAsciiOk` な ToASCII の出力には forbidden domain code point が無い。往復の仮定の形にしたもの。 -/
theorem ToAsciiOk.noForbidden {t : List Char → Option String} (htok : ToAsciiOk t) :
    ∀ x a, t x = some a → a.any isForbiddenDomain = false := by
  intro x a h
  have hall := (htok.out x a h).2
  cases hx : a.any isForbiddenDomain with
  | false => rfl
  | true =>
    simp [String.any] at hx
    obtain ⟨c, hc, hf⟩ := hx
    rw [(hall c hc).2] at hf
    cases hf

/--
**parse した結果は、serialize して parse し直すと戻る。**

base を与えた parse でもよい。base は妥当で canonical であることを仮定する。
`parseUrl` では base も parse で作るので、この仮定は外れる（`parseUrl_serialize`）。
-/
theorem parse_serialize_of_parse {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option Url}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b t = true)
    {u : Url} (h : basicUrlParse input base t = some u) :
    basicUrlParse (urlSerializer u) none t = some u :=
  roundtrip_canonical_of htok.noForbidden (basicUrlParse_valid hb h)
    (basicUrlParse_canonical htok hb hbc h)

/-- **`URL(url, base)` の結果は、serialize して `URL(href)` し直すと戻る。** -/
theorem parseUrl_serialize {t : List Char → Option String} (htok : ToAsciiOk t)
    {input : String} {base : Option String} {u : Url}
    (h : parseUrl input base t = some u) : parseUrl (urlSerializer u) none t = some u :=
  roundtrip_canonical_of htok.noForbidden (parseUrl_valid h) (parseUrl_canonical htok h)

/--
**parse の像は `ValidUrl ∧ canonicalUrl` にちょうど一致する。**

右から左は serialize した文字列を入力にすればよい（`roundtrip_canonical_of`）。
-/
theorem parse_image {t : List Char → Option String} (htok : ToAsciiOk t) (u : Url) :
    (∃ input, basicUrlParse input none t = some u) ↔ ValidUrl u ∧ canonicalUrl u t = true := by
  constructor
  · rintro ⟨input, h⟩
    have hb : ∀ b, (none : Option Url) = some b → ValidUrl b := fun _ hb => absurd hb (by simp)
    have hbc : ∀ b, (none : Option Url) = some b → canonicalUrl b t = true :=
      fun _ hb => absurd hb (by simp)
    exact ⟨basicUrlParse_valid hb h, basicUrlParse_canonical htok hb hbc h⟩
  · rintro ⟨hv, hc⟩
    exact ⟨urlSerializer u, roundtrip_canonical_of htok.noForbidden hv hc⟩

/--
**base を与えても像は広がらない。**

`URL(url, base)` が返す record は、どれも base 無しの parse で作れる。
-/
theorem parseUrl_image {t : List Char → Option String} (htok : ToAsciiOk t) (u : Url) :
    (∃ input base, parseUrl input base t = some u) ↔ ValidUrl u ∧ canonicalUrl u t = true := by
  constructor
  · rintro ⟨input, base, h⟩
    exact ⟨parseUrl_valid h, parseUrl_canonical htok h⟩
  · rintro ⟨hv, hc⟩
    exact ⟨urlSerializer u, none, roundtrip_canonical_of htok.noForbidden hv hc⟩

/--
**serialize してから parse することは、parse の結果を変えない。**

`parse ∘ serialize ∘ parse = parse` を `Option` の上で述べたもの。
-/
theorem parse_serialize_parse {t : List Char → Option String} (htok : ToAsciiOk t)
    (input : String) :
    (basicUrlParse input none t).bind (fun u => basicUrlParse (urlSerializer u) none t)
      = basicUrlParse input none t := by
  cases h : basicUrlParse input none t with
  | none => rfl
  | some u =>
    exact parse_serialize_of_parse htok (fun _ hb => absurd hb (by simp))
      (fun _ hb => absurd hb (by simp)) h

end Url
