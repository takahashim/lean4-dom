import Url.Invariant

/-!
# 遷移ごとに `PInv` を移す補題

`Url/StepValid.lean` の各 state の証明は、`step` を分岐に割ってから一つずつ閉じる。
再帰する分岐では、移った先の `PInv` を示す必要がある。成分を一つずつ `simp_all` で
示すと、大きな文脈で 27 回の `simp_all` が走って重い。ここでは遷移の種類ごとに、
`PInv` が移ることを一度だけ示しておく。各分岐で残るのは、URL record の変わり方の照合
（`with_reducible rfl`）と、移る先の state についての `decide`、それに分岐の条件だけである。
-/

namespace Url

/--
state を `st` から `st'` へ移すときに、state に依存する `PInv` の成分が移ること。

「`st'` で前提が立つなら `st` でも立つ」成分（`hostNull` ほか）と、
「`st` で結論が立つなら `st'` でも立つ」成分（`mayOpaque` と `mayCred`）、
それに state を名指しする成分（relative slash と port）を一つの真偽値にまとめた。
具体的な state の組では `decide` で決まる。
-/
def StateMono (st st' : PState) : Bool :=
  (!hostNull st' || hostNull st) &&
  (!freshHost st' || freshHost st) &&
  (!freshCred st' || freshCred st) &&
  (!freshPort st' || freshPort st) &&
  (!mayOpaque st || mayOpaque st') &&
  (!mayCred st || mayCred st') &&
  (st' != .relativeSlash || st == .relativeSlash) &&
  (st' != .port || st == .port)

/--
`PInv` が URL record について見る成分。query と fragment は見ない。

`abbrev` にしてあるのは、`with_reducible rfl` で比べるためである。
`{ ctx.url with query := … }` の成分は射影を簡約するだけで元と一致する。
-/
abbrev UrlCore (u : Url) : String × String × String × Option Host × Option Nat × Path :=
  (u.scheme, u.username, u.password, u.host, u.port, u.path)

/-- `UrlCore` から path を除いたもの。path だけを書き換える遷移で使う。 -/
abbrev UrlAuth (u : Url) : String × String × String × Option Host × Option Nat :=
  (u.scheme, u.username, u.password, u.host, u.port)

/--
**path だけを書き換える遷移では `PInv` が移る。**

URL record の path 以外の成分（`UrlAuth`）が同じで、新しい path が opaque かどうかを変えず、
`/` を含む segment を持たないなら、URL record についての成分は元のまま成り立つ。
state に依存する成分は `StateMono` から、buffer の成分は `hbuf` から出る。

base を使う state（`usesBasePath`）、`file` を許さない state（`notFileState`）、`file` に決まった
state（`fileState`）へ移るときの条件は、移る元の state からは出ないことがある
（no scheme state から relative state へ、host state から file host state へ）。
そこは分岐の条件から出すので、前提として受け取る。自己遷移では `PInv` の成分がそのまま当たる。
-/
theorem PInv.transferPath {base : Option Url} {st st' : PState} {ctx ctx' : PCtx}
    (h : PInv base st ctx) (hauth : UrlAuth ctx'.url = UrlAuth ctx.url)
    (hiso : ctx'.url.path.isOpaque = ctx.url.path.isOpaque)
    (hps : pathSegsOk ctx'.url.path = true)
    (hover : ctx'.over = ctx.over) (hmono : StateMono st st' = true)
    (hbp : usesBasePath st' = true → ∀ b, base = some b → b.hasOpaquePath = false)
    (hbnf : usesBasePath st' = true → ∀ b, base = some b → b.scheme ≠ "file")
    (hnf : notFileState st' = true → ctx'.url.scheme ≠ "file")
    (hfsc : fileState st' = true → ctx'.url.scheme = "file")
    (hbuf : looseBuffer st' = false → noSlash ctx'.buffer = true) : PInv base st' ctx' := by
  simp only [UrlAuth, Prod.mk.injEq] at hauth
  obtain ⟨hs, hu, hp, hh, hpo⟩ := hauth
  have eS : ctx'.url.isSpecial = ctx.url.isSpecial := by simp only [Url.isSpecial, hs]
  have eO : ctx'.url.hasOpaquePath = ctx.url.hasOpaquePath := by simp only [Url.hasOpaquePath, hiso]
  have eC : ctx'.url.includesCredentials = ctx.url.includesCredentials := by
    simp only [Url.includesCredentials, hu, hp]
  simp only [StateMono, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq, beq_iff_eq] at hmono
  obtain ⟨⟨⟨⟨⟨⟨⟨hhn, hfh⟩, hfc⟩, hfp⟩, hmo⟩, hmc⟩, hrs⟩, hpt⟩ := hmono
  have imp {p q : Bool} (hpq : p = false ∨ q = true) (hp : p = true) : q = true := by
    rcases hpq with h' | h' <;> simp_all
  have stEq {s : PState} (hs : ¬st' = s ∨ st = s) (h' : st' = s) : st = s :=
    hs.resolve_left (· h')
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := hbp
      baseNotFile := hbnf
      baseSchemeEq := fun hst b hb => by rw [hs]; exact h.baseSchemeEq (stEq hrs hst) b hb
      specialHasList := by rw [eS, eO]; exact h.specialHasList
      nullHostNoPort := by rw [hh, hpo]; exact h.nullHostNoPort
      opaqueNoCredentials := by rw [eO, eC]; exact h.opaqueNoCredentials
      opaqueNoPort := by rw [eO, hpo]; exact h.opaqueNoPort
      opaqueNoHost := by rw [eO, hh]; exact h.opaqueNoHost
      portRange := by rw [hpo]; exact h.portRange
      fileNoCredentials := by rw [hs, eC]; exact h.fileNoCredentials
      fileNoPort := by rw [hs, hpo]; exact h.fileNoPort
      hostKind := by rw [hs, hh]; exact h.hostKind
      pathSegs := hps
      emptyHostNoPort := by rw [hh, hpo]; exact h.emptyHostNoPort
      notFile := hnf
      fileScheme := hfsc
      portHostNotEmpty := fun hst => by rw [hh]; exact h.portHostNotEmpty (stEq hpt hst)
      bufferNoSlash := hbuf
      opaqueState := fun ho => imp hmo (h.opaqueState (by rw [← eO]; exact ho))
      credState := fun hh' hc => imp hmc (h.credState (by rw [← hh]; exact hh')
        (by rw [← eC]; exact hc))
      portHost := fun hst => by rw [hh]; exact h.portHost (stEq hpt hst)
      schemeNoHost := fun hn => by rw [hh]; exact h.schemeNoHost (imp hhn hn)
      schemeEmpty := fun hn => by rw [hs]; exact h.schemeEmpty (imp hfh hn)
      freshState := fun hn => by rw [eC]; exact h.freshState (imp hfc hn)
      freshPortState := fun hn => by rw [hpo]; exact h.freshPortState (imp hfp hn) }

/--
**URL record の `UrlCore` を変えない遷移では `PInv` が移る。**

state と buffer だけを変えるか、query と fragment だけを書く遷移である。
`transferPath` で path も同じにしたもの。
-/
theorem PInv.transfer {base : Option Url} {st st' : PState} {ctx ctx' : PCtx}
    (h : PInv base st ctx) (hcore : UrlCore ctx'.url = UrlCore ctx.url)
    (hover : ctx'.over = ctx.over) (hmono : StateMono st st' = true)
    (hbp : usesBasePath st' = true → ∀ b, base = some b → b.hasOpaquePath = false)
    (hbnf : usesBasePath st' = true → ∀ b, base = some b → b.scheme ≠ "file")
    (hnf : notFileState st' = true → ctx'.url.scheme ≠ "file")
    (hfsc : fileState st' = true → ctx'.url.scheme = "file")
    (hbuf : looseBuffer st' = false → noSlash ctx'.buffer = true) : PInv base st' ctx' := by
  simp only [UrlCore, Prod.mk.injEq] at hcore
  obtain ⟨hs, hu, hp, hh, hpo, hpa⟩ := hcore
  exact h.transferPath (by simp only [UrlAuth, hs, hu, hp, hh, hpo]) (by rw [hpa])
    (by rw [hpa]; exact h.pathSegs) hover hmono hbp hbnf hnf hfsc hbuf

/-- path state から出る遷移の、移る先の state だけで決まる条件。 -/
def PathTarget (st : PState) : Bool :=
  StateMono .path st && !usesBasePath st && !notFileState st && !fileState st

/--
**path state が segment を確定させる遷移**（path state に留まるか、query か fragment へ移る）。

`pathStepUrl` は path だけを書き換え、opaque かどうかを変えず、buffer に `/` が無ければ
`/` を含む segment を作らない。path state の buffer に `/` が無いことは `PInv` が言う。
-/
theorem PInv.pathStep {base : Option Url} {st' : PState} {ctx ctx' : PCtx}
    {slash : Bool} (h : PInv base .path ctx)
    (hcore : UrlCore ctx'.url = UrlCore (pathStepUrl ctx.url slash ctx.buffer))
    (hover : ctx'.over = ctx.over) (ht : PathTarget st' = true)
    (hbuf : looseBuffer st' = false → noSlash ctx'.buffer = true) : PInv base st' ctx' := by
  simp only [PathTarget, Bool.and_eq_true, Bool.not_eq_true'] at ht
  obtain ⟨⟨⟨hm, hub⟩, hnfs⟩, hfs⟩ := ht
  obtain ⟨p, hp⟩ := pathStepUrl_spec ctx.url slash ctx.buffer
  have hiso := pathStepUrl_path_isOpaque ctx.url slash ctx.buffer
  have hps := pathSegsOk_pathStepUrl (slash := slash) h.pathSegs (h.bufferNoSlash rfl)
  simp only [UrlCore, Prod.mk.injEq] at hcore
  obtain ⟨hs, hu, hpw, hh, hpo, hpa⟩ := hcore
  rw [hp] at hs hu hpw hh hpo hpa hiso hps
  refine h.transferPath (by simp only [UrlAuth, hs, hu, hpw, hh, hpo]) (by rw [hpa]; exact hiso)
    (by rw [hpa]; exact hps) hover hm (fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp))
    (fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp))
    (fun hn => by rw [hnfs] at hn; exact absurd hn (by simp))
    (fun hf => by rw [hfs] at hf; exact absurd hf (by simp)) hbuf

/--
**opaque path state が opaque path の末尾に文字列を足す遷移。**

`appendOpaque` は path だけを書き換え、opaque かどうかを変えない。opaque path は
`pathSegsOk` を常に満たす。
-/
theorem PInv.opaqueAppend {base : Option Url} {ctx ctx' : PCtx} {s : String}
    (h : PInv base .opaquePath ctx) (hurl : ctx'.url = appendOpaque ctx.url s)
    (hover : ctx'.over = ctx.over) (hbuf : ctx'.buffer = ctx.buffer) :
    PInv base .opaquePath ctx' := by
  have hiso := appendOpaque_path_isOpaque ctx.url s
  rw [← hurl] at hiso
  refine h.transferPath ?_ hiso ?_ hover (by decide) (fun hu => absurd hu (by decide))
    (fun hu => absurd hu (by decide)) (fun hn => absurd hn (by decide))
    (fun hf => absurd hf (by decide)) (fun hl => by rw [hbuf]; exact h.bufferNoSlash hl)
  · rcases appendOpaque_spec ctx.url s with he | ⟨o, _, he⟩ <;> rw [hurl, he]
  · rcases appendOpaque_spec ctx.url s with he | ⟨o, ho, he⟩
    · rw [hurl, he]; exact h.pathSegs
    · rw [hurl, he]; rfl

/-- scheme state を出て scheme を書いた後に入れる state の、state だけで決まる条件。 -/
def SchemeTarget (st : PState) : Bool :=
  !freshHost st && !fileState st && st != .port

/-- host も credentials も port も書かれておらず、path が opaque でない state。 -/
def FreshSource (st : PState) : Bool :=
  hostNull st && freshCred st && freshPort st && !mayOpaque st

/--
**host も credentials も port も無い state から、scheme を書いて移る遷移。**

scheme state の `:` の分岐と、relative state が base の scheme を写して relative slash state へ
移る分岐がこれに当たる。そうした state（`FreshSource`）では host も port も credentials も無く、
path は opaque でない。scheme を書いても、それらに関する成分はそのまま成り立つ。
残るのは、移る先が `file` を許さないこと（`hnf`）、base を使う state なら
base の path が opaque でなく scheme が `file` でないこと（`hbase`）、
relative slash state なら scheme が base の scheme であること（`hbse`）である。
-/
theorem PInv.setScheme {base : Option Url} {st st' : PState} {ctx ctx' : PCtx} {s : String}
    (h : PInv base st ctx) (hsrc : FreshSource st = true)
    (hurl : ctx'.url = { ctx.url with scheme := s })
    (hover : ctx'.over = ctx.over) (ht : SchemeTarget st' = true)
    (hnf : notFileState st' = true → s ≠ "file")
    (hbase : usesBasePath st' = true → ∀ b, base = some b →
      b.hasOpaquePath = false ∧ b.scheme ≠ "file")
    (hbse : st' = .relativeSlash → ∀ b, base = some b → s = b.scheme)
    (hbuf : looseBuffer st' = false → noSlash ctx'.buffer = true) :
    PInv base st' ctx' := by
  simp only [FreshSource, Bool.and_eq_true, Bool.not_eq_true'] at hsrc
  obtain ⟨⟨⟨hhn, hfc⟩, hfp⟩, hmo⟩ := hsrc
  have hho : ctx.url.host = none := h.schemeNoHost hhn
  have hpo : ctx.url.port = none := h.freshPortState hfp
  have hcr : ctx.url.includesCredentials = false := h.freshState hfc
  have hop : ctx.url.hasOpaquePath = false := h.notOpaque hmo
  simp only [SchemeTarget, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at ht
  obtain ⟨⟨hfh, hfs⟩, hpt⟩ := ht
  have eO : ctx'.url.hasOpaquePath = false := by
    rw [hurl]; simpa [Url.hasOpaquePath] using hop
  have eC : ctx'.url.includesCredentials = false := by
    rw [hurl]; simpa [Url.includesCredentials] using hcr
  have eH : ctx'.url.host = none := by rw [hurl]; exact hho
  have eP : ctx'.url.port = none := by rw [hurl]; exact hpo
  have eS : ctx'.url.scheme = s := by rw [hurl]
  have ePa : ctx'.url.path = ctx.url.path := by rw [hurl]
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu b hb => (hbase hu b hb).1
      baseNotFile := fun hu b hb => (hbase hu b hb).2
      baseSchemeEq := fun hst b hb => by rw [eS]; exact hbse hst b hb
      specialHasList := fun _ => eO
      nullHostNoPort := fun _ => eP
      opaqueNoCredentials := fun _ => eC
      opaqueNoPort := fun _ => eP
      opaqueNoHost := fun _ => eH
      portRange := fun p hp => by rw [eP] at hp; exact absurd hp (by simp)
      fileNoCredentials := fun _ => eC
      fileNoPort := fun _ => eP
      hostKind := by rw [eH]; rfl
      pathSegs := by rw [ePa]; exact h.pathSegs
      emptyHostNoPort := fun _ => eP
      notFile := fun hn => by rw [eS]; exact hnf hn
      fileScheme := fun hn => by rw [hfs] at hn; exact absurd hn (by simp)
      portHostNotEmpty := fun hst => absurd hst hpt
      bufferNoSlash := hbuf
      opaqueState := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      credState := fun _ hc => by rw [eC] at hc; exact absurd hc (by simp)
      portHost := fun hst => absurd hst hpt
      schemeNoHost := fun _ => eH
      schemeEmpty := fun hn => by rw [hfh] at hn; exact absurd hn (by simp)
      freshState := fun _ => eC
      freshPortState := fun _ => eP }

/--
**scheme state の `:` の分岐で、非 special な scheme を書いて opaque path を始める遷移。**

`setScheme` と同じく host も port も credentials も無いので、path を opaque にしても
`ValidUrl` の成分は崩れない。special でないこと（`hsp`）だけが要る。
-/
theorem PInv.setSchemeOpaque {base : Option Url} {ctx ctx' : PCtx} {s : String}
    (h : PInv base .scheme ctx)
    (hurl : ctx'.url = { ctx.url with scheme := s, path := .opaque "" })
    (hover : ctx'.over = ctx.over) (hbuf : ctx'.buffer = [])
    (hsp : isSpecialScheme s = false) :
    PInv base .opaquePath ctx' := by
  have hho : ctx.url.host = none := h.schemeNoHost rfl
  have hpo : ctx.url.port = none := h.freshPortState rfl
  have hcr : ctx.url.includesCredentials = false := h.freshState rfl
  have eC : ctx'.url.includesCredentials = false := by
    rw [hurl]; simpa [Url.includesCredentials] using hcr
  have eH : ctx'.url.host = none := by rw [hurl]; exact hho
  have eP : ctx'.url.port = none := by rw [hurl]; exact hpo
  have eS : ctx'.url.isSpecial = false := by rw [hurl]; exact hsp
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu => absurd hu (by decide)
      baseNotFile := fun hu => absurd hu (by decide)
      baseSchemeEq := fun hst => absurd hst (by decide)
      specialHasList := fun hs => by rw [eS] at hs; exact absurd hs (by simp)
      nullHostNoPort := fun _ => eP
      opaqueNoCredentials := fun _ => eC
      opaqueNoPort := fun _ => eP
      opaqueNoHost := fun _ => eH
      portRange := fun p hp => by rw [eP] at hp; exact absurd hp (by simp)
      fileNoCredentials := fun _ => eC
      fileNoPort := fun _ => eP
      hostKind := by rw [eH]; rfl
      pathSegs := by rw [hurl]; rfl
      emptyHostNoPort := fun _ => eP
      notFile := fun hn => absurd hn (by decide)
      fileScheme := fun hn => absurd hn (by decide)
      portHostNotEmpty := fun hst => absurd hst (by decide)
      bufferNoSlash := fun _ => by rw [hbuf]; rfl
      opaqueState := fun _ => rfl
      credState := fun _ hc => by rw [eC] at hc; exact absurd hc (by simp)
      portHost := fun hst => absurd hst (by decide)
      schemeNoHost := fun _ => eH
      schemeEmpty := fun hn => absurd hn (by decide)
      freshState := fun _ => eC
      freshPortState := fun _ => eP }

/-- query state と fragment state。base の成分を写した URL record を受け取れる。 -/
def LooseLate (st : PState) : Bool :=
  mayOpaque st && looseBuffer st && !mayCred st && !usesBasePath st && !notFileState st &&
    !fileState st && !hostNull st && !freshHost st && !freshCred st && !freshPort st &&
    st != .relativeSlash && st != .port

/--
**URL record の `UrlCore` を base のものにして、query state か fragment state へ移る遷移。**

relative state、file state、no scheme state が base の成分を写して `?` や `#` へ進む分岐である。
URL record についての成分は base の `ValidUrl` から出る。query state と fragment state では
state に依存する成分はどれも空になる。
-/
theorem PInv.fromBase {b : Url} {st st' : PState} {ctx ctx' : PCtx}
    (h : PInv (some b) st ctx) (hcore : UrlCore ctx'.url = UrlCore b)
    (hover : ctx'.over = ctx.over) (ht : LooseLate st' = true) : PInv (some b) st' ctx' := by
  have hv := h.baseValid b rfl
  simp only [UrlCore, Prod.mk.injEq] at hcore
  obtain ⟨hs, hu, hp, hh, hpo, hpa⟩ := hcore
  have eS : ctx'.url.isSpecial = b.isSpecial := by simp only [Url.isSpecial, hs]
  have eO : ctx'.url.hasOpaquePath = b.hasOpaquePath := by simp only [Url.hasOpaquePath, hpa]
  have eC : ctx'.url.includesCredentials = b.includesCredentials := by
    simp only [Url.includesCredentials, hu, hp]
  simp only [LooseLate, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmo, hlb⟩, hmc⟩, hub⟩, hnfs⟩, hfs⟩, hhn⟩, hfh⟩, hfc⟩, hfp⟩, hrs⟩, hpt⟩ := ht
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp)
      baseNotFile := fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp)
      baseSchemeEq := fun hst => absurd hst hrs
      specialHasList := by rw [eS, eO]; exact hv.specialHasList
      nullHostNoPort := by rw [hh, hpo]; exact hv.nullHostNoPort
      opaqueNoCredentials := by rw [eO, eC]; exact hv.opaqueNoCredentials
      opaqueNoPort := by rw [eO, hpo]; exact hv.opaqueNoPort
      opaqueNoHost := by rw [eO, hh]; exact hv.opaqueNoHost
      portRange := by rw [hpo]; exact hv.portRange
      fileNoCredentials := by rw [hs, eC]; exact hv.fileNoCredentials
      fileNoPort := by rw [hs, hpo]; exact hv.fileNoPort
      hostKind := by rw [hs, hh]; exact hv.hostKind
      pathSegs := by rw [hpa]; exact hv.pathSegs
      emptyHostNoPort := by rw [hh, hpo]; exact hv.emptyHostNoPort
      notFile := fun hn => by rw [hnfs] at hn; exact absurd hn (by simp)
      fileScheme := fun hn => by rw [hfs] at hn; exact absurd hn (by simp)
      portHostNotEmpty := fun hst => absurd hst hpt
      bufferNoSlash := fun hl => by rw [hlb] at hl; exact absurd hl (by simp)
      opaqueState := fun _ => hmo
      credState := fun hh' hc => by
        rw [hh] at hh'; rw [eC, hv.nullHostNoCredentials hh'] at hc; exact absurd hc (by simp)
      portHost := fun hst => absurd hst hpt
      schemeNoHost := fun hn => by rw [hhn] at hn; exact absurd hn (by simp)
      schemeEmpty := fun hn => by rw [hfh] at hn; exact absurd hn (by simp)
      freshState := fun hn => by rw [hfc] at hn; exact absurd hn (by simp)
      freshPortState := fun hn => by rw [hfp] at hn; exact absurd hn (by simp) }

/-- host を書いて移る先の state の、state だけで決まる条件。 -/
def HostTarget (st : PState) : Bool :=
  !usesBasePath st && st != .relativeSlash && !hostNull st && !freshHost st && !mayCred st

/--
**host を書いて（あわせて scheme も書いて）移る遷移。**

host state と file host state が host を確定させる分岐と、file state が scheme を `file`、
host を空にして進む分岐である。移る元では path が opaque でない（`mayOpaque` が false）。
host が null でなくなるので、host が null のときの成分はどれも空になる。
残るのは、scheme と host の組み合わせ（`hk`）、`file` なら credentials も port も無いこと、
空の host なら port が無いこと、移る先の state が求めることで、副条件として受け取る。
-/
theorem PInv.setHost {base : Option Url} {st st' : PState} {ctx ctx' : PCtx} {s : String}
    {hst : Host} (h : PInv base st ctx) (hmo : mayOpaque st = false)
    (hcore : UrlCore ctx'.url = UrlCore { ctx.url with scheme := s, host := some hst })
    (hover : ctx'.over = ctx.over) (ht : HostTarget st' = true)
    (hk : hostKindOkOf s (some hst) = true)
    (hfc : s = "file" → ctx.url.includesCredentials = false)
    (hfp : s = "file" → ctx.url.port = none)
    (hep : hst = Host.empty → ctx.url.port = none)
    (hnf : notFileState st' = true → s ≠ "file")
    (hfs : fileState st' = true → s = "file")
    (hpne : st' = .port → hst ≠ Host.empty)
    (hcr : freshCred st' = true → ctx.url.includesCredentials = false)
    (hpo : freshPort st' = true → ctx.url.port = none)
    (hbuf : looseBuffer st' = false → noSlash ctx'.buffer = true) : PInv base st' ctx' := by
  have hop : ctx.url.hasOpaquePath = false := h.notOpaque hmo
  simp only [UrlCore, Prod.mk.injEq] at hcore
  obtain ⟨hs, hu, hp, hh, hpt, hpa⟩ := hcore
  have eO : ctx'.url.hasOpaquePath = false := by
    simp only [Url.hasOpaquePath, hpa]; exact hop
  have eC : ctx'.url.includesCredentials = ctx.url.includesCredentials := by
    simp only [Url.includesCredentials, hu, hp]
  simp only [HostTarget, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at ht
  obtain ⟨⟨⟨⟨hub, hrs⟩, hhn⟩, hfh⟩, hmc⟩ := ht
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp)
      baseNotFile := fun hu' => by rw [hub] at hu'; exact absurd hu' (by simp)
      baseSchemeEq := fun hst' => absurd hst' hrs
      specialHasList := fun _ => eO
      nullHostNoPort := fun hn => by rw [hh] at hn; exact absurd hn (by simp)
      opaqueNoCredentials := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoPort := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoHost := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      portRange := by rw [hpt]; exact h.portRange
      fileNoCredentials := fun hf => by rw [eC]; exact hfc (by rw [← hs]; exact hf)
      fileNoPort := fun hf => by rw [hpt]; exact hfp (by rw [← hs]; exact hf)
      hostKind := by rw [hs, hh]; exact hk
      pathSegs := by rw [hpa]; exact h.pathSegs
      emptyHostNoPort := fun he => by
        rw [hpt]; rw [hh] at he; exact hep (Option.some.inj he)
      notFile := fun hn => by rw [hs]; exact hnf hn
      fileScheme := fun hn => by rw [hs]; exact hfs hn
      portHostNotEmpty := fun hst' he => by
        rw [hh] at he; exact hpne hst' (Option.some.inj he)
      bufferNoSlash := hbuf
      opaqueState := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      credState := fun hn => by rw [hh] at hn; exact absurd hn (by simp)
      portHost := fun _ => by rw [hh]; rfl
      schemeNoHost := fun hn => by rw [hhn] at hn; exact absurd hn (by simp)
      schemeEmpty := fun hn => by rw [hfh] at hn; exact absurd hn (by simp)
      freshState := fun hn => by rw [eC]; exact hcr hn
      freshPortState := fun hn => by rw [hpt]; exact hpo hn }

/--
**path state へ移る遷移で、URL record の path 以外を妥当な URL `v` から取るもの。**

relative state と file state が base の成分を写して path state へ進む分岐、
relative slash state と file slash state が base の host などを写す分岐である。
path state では state に依存する成分はほとんど空になり、残るのは `ValidUrl` の成分である。
path が opaque でなければ、path 以外の成分は `v` の `ValidUrl` から、path の成分は
`hps` から出る。
-/
theorem PInv.toPathOf {base : Option Url} {st : PState} {ctx ctx' : PCtx} {v : Url}
    (h : PInv base st ctx) (hv : ValidUrl v) (hauth : UrlAuth ctx'.url = UrlAuth v)
    (hiso : ctx'.url.path.isOpaque = false) (hps : pathSegsOk ctx'.url.path = true)
    (hover : ctx'.over = ctx.over) (hbuf : noSlash ctx'.buffer = true) :
    PInv base .path ctx' := by
  simp only [UrlAuth, Prod.mk.injEq] at hauth
  obtain ⟨hs, hu, hp, hh, hpo⟩ := hauth
  have eO : ctx'.url.hasOpaquePath = false := by simp only [Url.hasOpaquePath, hiso]
  have eC : ctx'.url.includesCredentials = v.includesCredentials := by
    simp only [Url.includesCredentials, hu, hp]
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu' => absurd hu' (by decide)
      baseNotFile := fun hu' => absurd hu' (by decide)
      baseSchemeEq := fun hst => absurd hst (by decide)
      specialHasList := fun _ => eO
      nullHostNoPort := by rw [hh, hpo]; exact hv.nullHostNoPort
      opaqueNoCredentials := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoPort := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoHost := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      portRange := by rw [hpo]; exact hv.portRange
      fileNoCredentials := by rw [hs, eC]; exact hv.fileNoCredentials
      fileNoPort := by rw [hs, hpo]; exact hv.fileNoPort
      hostKind := by rw [hs, hh]; exact hv.hostKind
      pathSegs := hps
      emptyHostNoPort := by rw [hh, hpo]; exact hv.emptyHostNoPort
      notFile := fun hn => absurd hn (by decide)
      fileScheme := fun hn => absurd hn (by decide)
      portHostNotEmpty := fun hst => absurd hst (by decide)
      bufferNoSlash := fun _ => hbuf
      opaqueState := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      credState := fun hh' hc => by
        rw [hh] at hh'; rw [eC, hv.nullHostNoCredentials hh'] at hc; exact absurd hc (by simp)
      portHost := fun hst => absurd hst (by decide)
      schemeNoHost := fun hn => absurd hn (by decide)
      schemeEmpty := fun hn => absurd hn (by decide)
      freshState := fun hn => absurd hn (by decide)
      freshPortState := fun hn => absurd hn (by decide) }

/--
**authority state が `@` を見て、buffer を username と password に写す遷移。**

`userinfoStep` は username と password だけを書く。authority state では path は opaque でなく、
scheme は `file` でなく、host が null のまま credentials を持つことが許されている。
-/
theorem PInv.userinfo {base : Option Url} {ctx ctx' : PCtx} {p : Url × Bool} {buf : List Char}
    (h : PInv base .authority ctx)
    (hcore : UrlCore ctx'.url = UrlCore (buf.foldl userinfoStep p).1) (hp1 : p.1 = ctx.url)
    (hover : ctx'.over = ctx.over) : PInv base .authority ctx' := by
  obtain ⟨un, pw, hf⟩ := userinfoFold_spec buf p
  rw [hf, hp1] at hcore
  simp only [UrlCore, Prod.mk.injEq] at hcore
  obtain ⟨hs, _, _, hh, hpo, hpa⟩ := hcore
  have hop : ctx.url.hasOpaquePath = false := h.notOpaque rfl
  have hnf : ctx.url.scheme ≠ "file" := h.notFile rfl
  have eO : ctx'.url.hasOpaquePath = false := by simp only [Url.hasOpaquePath, hpa]; exact hop
  have eS : ctx'.url.isSpecial = ctx.url.isSpecial := by simp only [Url.isSpecial, hs]
  refine
    { noOverride := by rw [hover]; exact h.noOverride
      baseValid := h.baseValid
      basePathList := fun hu' => absurd hu' (by decide)
      baseNotFile := fun hu' => absurd hu' (by decide)
      baseSchemeEq := fun hst => absurd hst (by decide)
      specialHasList := fun _ => eO
      nullHostNoPort := by rw [hh, hpo]; exact h.nullHostNoPort
      opaqueNoCredentials := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoPort := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      opaqueNoHost := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      portRange := by rw [hpo]; exact h.portRange
      fileNoCredentials := fun hf' => by rw [hs] at hf'; exact absurd hf' hnf
      fileNoPort := fun hf' => by rw [hs] at hf'; exact absurd hf' hnf
      hostKind := by rw [hs, hh]; exact h.hostKind
      pathSegs := by rw [hpa]; exact h.pathSegs
      emptyHostNoPort := by rw [hh, hpo]; exact h.emptyHostNoPort
      notFile := fun _ => by rw [hs]; exact hnf
      fileScheme := fun hn => absurd hn (by decide)
      portHostNotEmpty := fun hst => absurd hst (by decide)
      bufferNoSlash := fun hl => absurd hl (by decide)
      opaqueState := fun ho => by rw [eO] at ho; exact absurd ho (by simp)
      credState := fun _ _ => rfl
      portHost := fun hst => absurd hst (by decide)
      schemeNoHost := fun _ => by rw [hh]; exact h.schemeNoHost rfl
      schemeEmpty := fun hn => absurd hn (by decide)
      freshState := fun hn => absurd hn (by decide)
      freshPortState := fun _ => by rw [hpo]; exact h.freshPortState rfl }

end Url
