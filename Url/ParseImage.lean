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

ToASCII は既定の `asciiDomainToASCII` である（`Url/CanonicalInv.lean` の先頭を参照）。
-/

namespace Url

/--
**parse した結果は、serialize して parse し直すと戻る。**

base を与えた parse でもよい。base は妥当で canonical であることを仮定する。
`parseUrl` では base も parse で作るので、この仮定は外れる（`parseUrl_serialize`）。
-/
theorem parse_serialize_of_parse {input : String} {base : Option Url}
    (hb : ∀ b, base = some b → ValidUrl b) (hbc : ∀ b, base = some b → canonicalUrl b = true)
    {u : Url} (h : basicUrlParse input base = some u) :
    basicUrlParse (urlSerializer u) none = some u :=
  roundtrip_canonical (basicUrlParse_valid hb h) (basicUrlParse_canonical hb hbc h)

/-- **`URL(url, base)` の結果は、serialize して `URL(href)` し直すと戻る。** -/
theorem parseUrl_serialize {input : String} {base : Option String} {u : Url}
    (h : parseUrl input base = some u) : parseUrl (urlSerializer u) none = some u :=
  roundtrip_canonical (parseUrl_valid h) (parseUrl_canonical h)

/--
**parse の像は `ValidUrl ∧ canonicalUrl` にちょうど一致する。**

右から左は serialize した文字列を入力にすればよい（`roundtrip_canonical`）。
-/
theorem parse_image (u : Url) :
    (∃ input, basicUrlParse input none = some u) ↔ ValidUrl u ∧ canonicalUrl u = true := by
  constructor
  · rintro ⟨input, h⟩
    have hb : ∀ b, (none : Option Url) = some b → ValidUrl b := fun _ hb => absurd hb (by simp)
    have hbc : ∀ b, (none : Option Url) = some b → canonicalUrl b = true :=
      fun _ hb => absurd hb (by simp)
    exact ⟨basicUrlParse_valid hb h, basicUrlParse_canonical hb hbc h⟩
  · rintro ⟨hv, hc⟩
    exact ⟨urlSerializer u, roundtrip_canonical hv hc⟩

/--
**base を与えても像は広がらない。**

`URL(url, base)` が返す record は、どれも base 無しの parse で作れる。
-/
theorem parseUrl_image (u : Url) :
    (∃ input base, parseUrl input base = some u) ↔ ValidUrl u ∧ canonicalUrl u = true := by
  constructor
  · rintro ⟨input, base, h⟩
    exact ⟨parseUrl_valid h, parseUrl_canonical h⟩
  · rintro ⟨hv, hc⟩
    exact ⟨urlSerializer u, none, roundtrip_canonical hv hc⟩

/--
**serialize してから parse することは、parse の結果を変えない。**

`parse ∘ serialize ∘ parse = parse` を `Option` の上で述べたもの。
-/
theorem parse_serialize_parse (input : String) :
    (basicUrlParse input none).bind (fun u => basicUrlParse (urlSerializer u) none)
      = basicUrlParse input none := by
  cases h : basicUrlParse input none with
  | none => rfl
  | some u =>
    exact parse_serialize_of_parse (fun _ hb => absurd hb (by simp))
      (fun _ hb => absurd hb (by simp)) h

end Url
