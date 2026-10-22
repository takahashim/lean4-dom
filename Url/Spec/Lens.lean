import Url.Spec.Setters
import Url.CanonicalParts
import Url.StrictValid
import Url.Roundtrip.Port
import Url.StepCanonical
import Url.StepValid
import Url.Eval

/-!
# getter と setter の往復、setter の冪等性（§6.1）

`URL` の IDL 属性は getter と setter の組である。ここでは二つの性質を示す。

* **冪等性。** どの setter も、同じ値を二度入れると一度入れたのと同じになる。前提は要らない。
* **往復。** parse の結果 `u` について、getter の値を同じ属性の setter に戻すと `u` に戻る。
  例外はちょうど三つで、どれも「空の成分」と「null の成分」を getter が区別しないことから来る。
  * fragment が空（`#` で終わる）：`hash` は `""` を返し、`hash` setter は `""` で fragment を null にする。
  * query が空（`?` で終わる）：`search` についても同じ。
  * host が null で special でない URL（`sc:/a`）：`host` / `hostname` は `""` を返し、setter は `""` で
    空の host を作る（`sc:///a` になる）。

往復と冪等性は、WPT の URL と乱数の URL（約 9 万件）、25 通りの値で先に確かめた。
-/

namespace Url.Spec

open Infra Url

/-! ## `hash` と `search` の setter の等式 -/

theorem fragmentText_eq (l : List Char) :
    fragmentText l = String.ofList (utf8PercentEncode fragmentSet l) := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp [fragmentText, ih, encChar, utf8PercentEncode, String.ofList_append]

/-- **`hash` setter。** 空文字列なら fragment を null に、そうでなければ先頭の `#` を一つ落として encode する。 -/
theorem setHash_eq (u : Url) (v : String) :
    u.setHash v = if v.isEmpty then { u with fragment := none }
      else { u with fragment := some (String.ofList (utf8PercentEncode fragmentSet
              (stripTabNewline (dropLeading '#' v).toList))) } := by
  unfold Url.setHash
  split
  · rfl
  · simp only [basicUrlParseOverride, SOverride.start]
    rw [Spec.run_fragment none _ _ "" rfl]
    simp [fragmentText_eq]

/-- override 付きの query state は `#` も query の中に読む。 -/
theorem run_query_over (base : Option Url) : ∀ (l : List Char) (ctx : PCtx), ctx.over.isSome = true →
    run base .query l ctx = .ok { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ l }) }
  | [], ctx, _ => by rw [run, step]; simp
  | c :: t, ctx, hov => by
    have hrec := run_query_over base t { ctx with buffer := ctx.buffer ++ [c] } hov
    by_cases hc : c = '#'
    · subst hc
      rw [run, step, if_pos hov, hrec]
      simp
    · rw [run, step, hrec]
      · simp
      · exact hc

/-- **`search` setter。** 空文字列なら query を null に、そうでなければ先頭の `?` を一つ落として encode する。 -/
theorem setSearch_eq (u : Url) (v : String) :
    u.setSearch v = if v.isEmpty then { u with query := none }
      else { u with query := some (String.ofList (utf8PercentEncode
              (if u.isSpecial then specialQuerySet else querySet)
              (stripTabNewline (dropLeading '?' v).toList))) } := by
  unfold Url.setSearch
  split
  · rfl
  · simp only [basicUrlParseOverride, SOverride.start]
    rw [run_query_over none _ _ rfl]
    simp [queryOf, Url.isSpecial]
    rfl

/-! ## 冪等性 -/

theorem setHash_idem (u : Url) (v : String) : (u.setHash v).setHash v = u.setHash v := by
  rw [setHash_eq u v]; split <;> rw [setHash_eq] <;> simp_all

theorem setSearch_idem (u : Url) (v : String) : (u.setSearch v).setSearch v = u.setSearch v := by
  rw [setSearch_eq u v]; split <;> rw [setSearch_eq] <;> simp_all [Url.isSpecial] <;> rfl

theorem setUsername_idem (u : Url) (v : String) :
    (u.setUsername v).setUsername v = u.setUsername v := by
  unfold Url.setUsername; split <;> simp_all [Url.cannotHaveCredentials]

theorem setPassword_idem (u : Url) (v : String) :
    (u.setPassword v).setPassword v = u.setPassword v := by
  unfold Url.setPassword; split <;> simp_all [Url.cannotHaveCredentials]

theorem setPort_idem (u : Url) (v : String) : (u.setPort v).setPort v = u.setPort v := by
  rw [setPort_eq u v, setPort_eq]
  unfold portSpec
  split
  · simp_all
  · split
    · simp_all
    · split <;> simp_all

theorem setPathname_idem (u : Url) (v : String) :
    (u.setPathname v).setPathname v = u.setPathname v := by
  by_cases hop : u.hasOpaquePath = true
  · have : u.setPathname v = u := by simp [Url.setPathname, hop]
    rw [this, this]
  · have hop' : u.hasOpaquePath = false := by simpa using hop
    rw [setPathname_eq u v hop', setPathname_eq _ v (by simp [Url.hasOpaquePath, Path.isOpaque])]
    simp [pathnameSpec, Url.isSpecial]
    rfl

theorem setProtocol_idem (u : Url) (v : String) :
    (u.setProtocol v).setProtocol v = u.setProtocol v := by
  rw [setProtocol_eq u v, setProtocol_eq]
  unfold protocolSpec
  split
  · simp_all
  · next s _ _ =>
    simp only
    split
    · simp_all
    · split
      · simp_all
      · split
        · simp_all
        · next h1 h2 h3 =>
          have hsp : u.isSpecial = isSpecialScheme s := by simpa using h1
          by_cases hd : defaultPort s = u.port
          · simp only [hd, if_true]
            rw [if_neg (by simp [Url.isSpecial])]
            repeat' split
            all_goals first | rfl | simp_all [Url.includesCredentials]
          · simp only [hd, if_false]
            rw [if_neg (by simp [Url.isSpecial])]
            repeat' split
            all_goals first | rfl | simp_all [Url.includesCredentials]

theorem hostSetterSpec_idem (t : List Char → Option String) (u : Url) (v : String) (b : Bool) :
    hostSetterSpec t (hostSetterSpec t u v b) v b = hostSetterSpec t u v b := by
  by_cases hop : u.hasOpaquePath = true
  · simp [hostSetterSpec, hop]
  have hop' : u.hasOpaquePath = false := by simpa using hop
  generalize hR : hostSetterSpec t u v b = R
  unfold hostSetterSpec at hR
  simp only [hop', Bool.false_eq_true, if_false] at hR
  by_cases hf : u.scheme = "file"
  · simp only [hf, if_true] at hR
    generalize hT : (stripTabNewline v.toList).takeWhile (fun c => !fileHostDelim c) = hp at hR
    unfold hostSetterSpec
    have hRo : R.hasOpaquePath = false := by
      rw [← hR]; split <;> (try split) <;> simp_all [Url.hasOpaquePath]
    have hRf : R.scheme = "file" := by
      rw [← hR]; split <;> (try split) <;> simp_all
    simp only [hRo, hRf, Bool.false_eq_true, if_false, if_true, hT]
    rw [← hR]
    split
    · simp
    · split <;> simp_all
  · simp only [hf, if_false] at hR
    generalize hT : (stripTabNewline v.toList).takeWhile (fun c => !hostDelim u.isSpecial c) = hp at hR
    unfold hostSetterSpec
    have hfacts : R.hasOpaquePath = false ∧ R.scheme = u.scheme ∧ R.username = u.username ∧
        R.password = u.password ∧ ((splitHostPort false hp).2 = none → R.port = u.port) := by
      rw [← hR]
      split <;> (repeat' split) <;> simp_all [Url.hasOpaquePath]
    obtain ⟨hRo, hRs, hRu, hRp, hRport⟩ := hfacts
    have hRsp : R.isSpecial = u.isSpecial := by simp [Url.isSpecial, hRs]
    simp only [hRo, hRs, hf, Bool.false_eq_true, if_false, hRsp, hT]
    rw [← hR]
    have hRport' : ∀ h, splitHostPort false hp = (h, none) → R.port = u.port :=
      fun h he => hRport (by rw [he])
    rcases hs : splitHostPort false hp with ⟨h, _ | p⟩ <;> simp only <;> (repeat' split) <;>
      simp_all [Url.includesCredentials]

theorem setHost_idem (u : Url) (v : String) (t : List Char → Option String) :
    (u.setHost v t).setHost v t = u.setHost v t := by
  rw [setHost_eq, setHost_eq]; exact hostSetterSpec_idem t u v false

theorem setHostname_idem (u : Url) (v : String) (t : List Char → Option String) :
    (u.setHostname v t).setHostname v t = u.setHostname v t := by
  rw [setHostname_eq, setHostname_eq]; exact hostSetterSpec_idem t u v true

/--
**どの IDL setter も冪等である。** 同じ値を二度入れても一度入れたのと同じになる。前提は要らない。

`href` setter は失敗したら元の URL を残すので、二度目も同じ結果になる。
-/
theorem setAttr_idem (u : Url) (name v : String) (t : List Char → Option String) :
    (u.setAttr name v t).bind (fun u' => u'.setAttr name v t) = u.setAttr name v t := by
  unfold Url.setAttr
  split <;> simp only [Option.bind_some, Option.bind_none]
  · cases Url.setHref v t <;> rfl
  · rw [setProtocol_idem]
  · rw [setUsername_idem]
  · rw [setPassword_idem]
  · rw [setHost_idem]
  · rw [setHostname_idem]
  · rw [setPort_idem]
  · rw [setPathname_idem]
  · rw [setSearch_idem]
  · rw [setHash_idem]

/-! ## 往復：encode 済みの成分 -/

theorem encodedWith_all {set : Char → Bool} {s : String} (h : encodedWith set s = true) :
    ∀ c ∈ s.toList, set c = false := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

theorem noTab_of_c0 {c : Char} (h : c0ControlSet c = false) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [c0ControlSet, isC0Control, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  omega

theorem c0_of_fragmentSet {c : Char} (h : fragmentSet c = false) : c0ControlSet c = false := by
  simp only [fragmentSet, Bool.or_eq_false_iff] at h; exact h.1.1.1.1.1

theorem c0_of_querySet {c : Char} (h : querySet c = false) : c0ControlSet c = false := by
  simp only [querySet, Bool.or_eq_false_iff] at h; exact h.1.1.1.1.1

theorem c0_of_specialQuerySet {c : Char} (h : specialQuerySet c = false) : c0ControlSet c = false := by
  simp only [specialQuerySet, Bool.or_eq_false_iff] at h; exact c0_of_querySet h.1

theorem c0_of_pathSet {c : Char} (h : pathSet c = false) : c0ControlSet c = false := by
  simp only [pathSet, Bool.or_eq_false_iff] at h; exact c0_of_querySet h.1.1.1.1.1

theorem c0_of_userinfoSet {c : Char} (h : userinfoSet c = false) : c0ControlSet c = false := by
  simp only [userinfoSet, Bool.or_eq_false_iff] at h; exact c0_of_pathSet h.1.1.1.1.1.1.1

/-- encode 済みの文字列は、tab と newline の除去も encode も素通りする。 -/
theorem encode_strip_id {set : Char → Bool} (hc0 : ∀ c, set c = false → c0ControlSet c = false)
    {s : String} (h : encodedWith set s = true) :
    String.ofList (utf8PercentEncode set (stripTabNewline s.toList)) = s := by
  have hall := encodedWith_all h
  rw [stripTabNewline_eq_self (fun c hc => noTab_of_c0 (hc0 c (hall c hc))),
    utf8PercentEncode_id hall, String.ofList_toList]

theorem dropLeading_cons (d : Char) (s : String) : dropLeading d (String.ofList [d] ++ s) = s := by
  simp [dropLeading]

/-- **fragment が空でなければ、`hash` を戻すと変わらない。** -/
theorem setHash_hash {u : Url} {t : List Char → Option String} (hc : canonicalUrl u t = true)
    (hf : u.fragment ≠ some "") : u.setHash u.hash = u := by
  have hp := canonical_parts hc
  rw [setHash_eq]
  unfold Url.hash
  cases hfr : u.fragment with
  | none => simp; cases u; simp_all
  | some f =>
    have hne : f ≠ "" := fun e => hf (by rw [hfr, e])
    have hfe : f.isEmpty = false := by simpa using hne
    simp only [hfe, Bool.false_eq_true, if_false]
    rw [if_neg (by simp)]
    rw [show ("#" ++ f) = String.ofList ['#'] ++ f from rfl, dropLeading_cons,
      encode_strip_id (fun c h => c0_of_fragmentSet h) (hp.fragment f hfr)]
    cases u; simp_all

/-- **query が空でなければ、`search` を戻すと変わらない。** -/
theorem setSearch_search {u : Url} {t : List Char → Option String} (hc : canonicalUrl u t = true)
    (hq : u.query ≠ some "") : u.setSearch u.search = u := by
  have hp := canonical_parts hc
  rw [setSearch_eq]
  unfold Url.search
  cases hqr : u.query with
  | none => simp; cases u; simp_all
  | some q =>
    have hne : q ≠ "" := fun e => hq (by rw [hqr, e])
    have hqe : q.isEmpty = false := by simpa using hne
    simp only [hqe, Bool.false_eq_true, if_false]
    rw [if_neg (by simp)]
    rw [show ("?" ++ q) = String.ofList ['?'] ++ q from rfl, dropLeading_cons]
    have henc := hp.query q hqr
    have : String.ofList (utf8PercentEncode (if u.isSpecial then specialQuerySet else querySet)
        (stripTabNewline q.toList)) = q := by
      split at henc
      · next hsp => rw [if_pos hsp]; exact encode_strip_id (fun c h => c0_of_specialQuerySet h) henc
      · next hsp => rw [if_neg hsp]; exact encode_strip_id (fun c h => c0_of_querySet h) henc
    rw [this]
    cases u; simp_all

/-- **`username` を戻すと変わらない。** -/
theorem setUsername_username {u : Url} {t : List Char → Option String} (hc : canonicalUrl u t = true) :
    u.setUsername u.username = u := by
  have hp := canonical_parts hc
  unfold Url.setUsername
  split
  · rfl
  · rw [userinfoEncode, utf8PercentEncode_id (encodedWith_all hp.username), String.ofList_toList]

/-- **`password` を戻すと変わらない。** -/
theorem setPassword_password {u : Url} {t : List Char → Option String} (hc : canonicalUrl u t = true) :
    u.setPassword u.password = u := by
  have hp := canonical_parts hc
  unfold Url.setPassword
  split
  · rfl
  · rw [userinfoEncode, utf8PercentEncode_id (encodedWith_all hp.password), String.ofList_toList]

/-! ## 往復：port と protocol -/

theorem digit_noTab {c : Char} (h : isAsciiDigit c = true) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem takeWhile_all {p : Char → Bool} : ∀ {l : List Char}, (∀ c ∈ l, p c = true) → l.takeWhile p = l
  | [], _ => rfl
  | c :: l, h => by
    rw [List.takeWhile_cons, if_pos (h c (by simp)), takeWhile_all (fun x hx => h x (by simp [hx]))]

/-- port を書けない URL は port を持たない（parse の結果なら）。 -/
theorem port_none_of_cannot {u : Url} (hv : ValidUrl u) (h : u.cannotHaveCredentials = true) :
    u.port = none := by
  simp only [Url.cannotHaveCredentials, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact hv.nullHostNoPort h
  · exact hv.emptyHostNoPort h
  · exact hv.fileNoPort h

/-- **`port` を戻すと変わらない。** -/
theorem setPort_portAttr {u : Url} {t : List Char → Option String} (hv : ValidUrl u)
    (hc : canonicalUrl u t = true) : u.setPort u.portAttr = u := by
  have hp := canonical_parts hc
  rw [setPort_eq]
  unfold portSpec Url.portAttr
  cases hpo : u.port with
  | none =>
    split
    · rfl
    · rw [if_pos (by decide)]
      cases u; simp_all
  | some p =>
    have hcan : u.cannotHaveCredentials = false := by
      cases h : u.cannotHaveCredentials
      · rfl
      · rw [port_none_of_cannot hv h] at hpo; cases hpo
    simp only [Url.cannotHaveCredentials, Bool.or_eq_false_iff] at hcan
    simp only at *
    rw [if_neg (by simp [hcan.1.1, hcan.1.2, hcan.2])]
    have hne : (toString p).isEmpty = false := by
      cases h : (toString p).isEmpty
      · rfl
      · exact absurd (by simp at h) (toString_ne_nil p)
    rw [if_neg (by simp)]
    have hd : (stripTabNewline (toString p).toList).takeWhile isAsciiDigit = (toString p).toList := by
      rw [stripTabNewline_eq_self (fun c hc => digit_noTab (toString_digits p c hc)),
        takeWhile_all (toString_digits p)]
    have hval : decimalOf (toString p).toList = p := by
      rw [decimalOf_eq_portValue, portValue_toString]
    rw [hd, hval]
    have hlt := hv.portRange p hpo
    have hnd := hp.port p hpo
    rw [if_neg (by simp; omega), if_neg hnd]
    cases u; simp_all

theorem canonicalScheme_chars {s : String} (h : canonicalScheme s = true) :
    ∃ a pre, s.toList = a :: pre ∧ isAsciiLowerAlpha a = true ∧
      ∀ c ∈ pre, (isAsciiDigit c || isAsciiLowerAlpha c || c == '+' || c == '-' || c == '.') = true := by
  unfold canonicalScheme at h
  split at h
  · simp at h
  · next a pre he =>
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨a, pre, he, h.1, h.2⟩

/-- **`protocol` を戻すと変わらない。** getter は `:` まで返し、setter は後ろに `:` を足すが、最初の `:` で止まる。 -/
theorem setProtocol_protocol {u : Url} {t : List Char → Option String} (hv : ValidUrl u)
    (hc : canonicalUrl u t = true) : u.setProtocol u.protocol = u := by
  have hp := canonical_parts hc
  rw [setProtocol_eq]
  unfold protocolSpec Url.protocol
  obtain ⟨a, pre, he, ha, hpre⟩ := canonicalScheme_chars hp.scheme
  have hlowA : asciiLowerChar a = a := by
    simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp [asciiLowerChar, isAsciiUpperAlpha]; omega
  have hlow : ∀ c ∈ pre, asciiLowerChar c = c := by
    intro c hc
    have := hpre c hc
    simp only [isAsciiDigit, isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at this
    simp only [asciiLowerChar, isAsciiUpperAlpha]
    rcases this with (((h | h) | h) | h) | h
    · simp; omega
    · simp; omega
    all_goals (subst h; decide)
  have htail : ∀ c ∈ pre, isSchemeTail c = true := by
    intro c hc
    have := hpre c hc
    simp only [isSchemeTail, isAsciiAlphanumeric, isAsciiAlpha, Bool.or_eq_true] at this ⊢
    rcases this with (((h | h) | h) | h) | h <;> simp [h]
  have hnoTab : ∀ c ∈ u.scheme.toList ++ [':', ':'], c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
    intro c hc
    rw [he] at hc
    simp only [List.cons_append, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl | rfl
    · simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha; omega
    · have := hpre c hc
      simp only [isAsciiDigit, isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at this
      rcases this with (((h | h) | h) | h) | h
      · omega
      · omega
      all_goals (subst h; decide)
    all_goals decide
  have hl : (u.scheme ++ ":").toList ++ [':'] = u.scheme.toList ++ [':', ':'] := by simp
  rw [hl, stripTabNewline_eq_self hnoTab, he]
  have hsplit : splitScheme (a :: pre ++ [':', ':']) = some (u.scheme, [':']) := by
    have hdw : (pre ++ [':', ':']).dropWhile isSchemeTail = [':', ':'] := by
      rw [List.dropWhile_append_of_pos (fun c hc => htail c hc)]
      rfl
    have htw : (pre ++ [':', ':']).takeWhile isSchemeTail = pre := by
      rw [List.takeWhile_append_of_pos (fun c hc => htail c hc)]
      show pre ++ [] = pre
      simp
    have hmap : (a :: pre).map asciiLowerChar = a :: pre := by
      simp only [List.map_cons, hlowA, List.cons.injEq, true_and]
      have : pre.map asciiLowerChar = pre.map id := List.map_congr_left hlow
      simpa using this
    simp only [splitScheme, List.cons_append]
    rw [if_pos (by simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq] at ha
                   simp [isAsciiAlpha, isAsciiLowerAlpha]; omega), hdw, htw, hmap, ← he,
      String.ofList_toList]
    rfl
  rw [hsplit]
  simp only
  rw [if_neg (by simp [Url.isSpecial])]
  rw [if_neg (by
    intro h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h.1 with h1 | h1
    · rw [hv.fileNoCredentials h.2] at h1; cases h1
    · rw [hv.fileNoPort h.2] at h1; cases h1)]
  split
  · rfl
  · cases hpo : u.port with
    | none => cases u; simp_all
    | some p =>
      rw [if_neg (by exact hp.port p hpo)]
      cases u; simp_all

/-! ## `pathname` の往復 -/

/-- 区切りを含まない segment を区切りで繋いだものを割ると、元の segment の列に戻る。 -/
theorem splitBy_intercal (p : Char → Bool) (hsep : p '/' = true) : ∀ (segs : List String),
    segs ≠ [] → (∀ s ∈ segs, ∀ c ∈ s.toList, p c = false) →
    splitBy p (intercal segs) = segs.map String.toList
  | [], h, _ => absurd rfl h
  | [s], _, hall => by
    have := splitBy_append_nosep p s.toList [] (hall s (by simp))
    simp only [List.append_nil] at this
    simp [intercal, this, splitBy]
  | s :: t :: r, _, hall => by
    show splitBy p (s.toList ++ '/' :: intercal (t :: r)) = _
    rw [splitBy_append_nosep p s.toList _ (hall s (by simp)), splitBy, if_pos hsep,
      splitBy_intercal p hsep (t :: r) (by simp) (fun x hx => hall x (by simp [hx]))]
    simp

theorem driveColon_of_norm : ∀ {l : List Char}, isNormalizedWindowsDrive l = true → driveColon l = l
  | [], h => by simp [isNormalizedWindowsDrive] at h
  | [_], h => by simp [isNormalizedWindowsDrive] at h
  | [a, b], h => by
    simp only [isNormalizedWindowsDrive, Bool.and_eq_true, beq_iff_eq] at h
    simp [driveColon, h.2]
  | _ :: _ :: _ :: _, h => by simp [isNormalizedWindowsDrive] at h

/-- dot でなく、drive letter なら正規化済みの segment は、そのまま足される。 -/
theorem segStep_keep {isFile : Bool} {acc : List String} {s : String} {last : Bool}
    (h1 : isSingleDot s.toList = false) (h2 : isDoubleDot s.toList = false)
    (hd : isFile = true → acc = [] → isWindowsDrive s.toList = true →
      isNormalizedWindowsDrive s.toList = true) :
    segStep isFile acc s.toList last = acc ++ [s] := by
  unfold segStep
  rw [if_neg (by simp [h2]), if_neg (by simp [h1])]
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rw [driveColon_of_norm (hd h.1.1 h.1.2 h.2), String.ofList_toList]
  · rw [String.ofList_toList]

theorem foldSegs_keep {isFile : Bool} : ∀ (l acc : List String), acc ≠ [] →
    (∀ s ∈ l, isSingleDot s.toList = false ∧ isDoubleDot s.toList = false) →
    foldSegs isFile acc (l.map String.toList) = acc ++ l
  | [], acc, _, _ => by simp [foldSegs]
  | s :: r, acc, hne, hall => by
    have hs := hall s (by simp)
    have ih := foldSegs_keep (isFile := isFile) r (acc ++ [s]) (by simp) (fun x hx => hall x (by simp [hx]))
    simp only [foldSegs, List.map_cons, List.foldl_cons] at ih ⊢
    rw [segStep_keep hs.1 hs.2 (fun _ h => absurd h hne), ih]
    simp

/-- **正規な segment の列は、`resolveSegs` で畳んでも変わらない。** -/
theorem resolveSegs_keep {isFile : Bool} (segs : List String) (hne : segs ≠ [])
    (hall : ∀ s ∈ segs, isSingleDot s.toList = false ∧ isDoubleDot s.toList = false)
    (hd : ∀ s, segs.head? = some s → isFile = true → isWindowsDrive s.toList = true →
      isNormalizedWindowsDrive s.toList = true) :
    resolveSegs isFile [] (segs.map String.toList) = segs := by
  rcases List.eq_nil_or_concat segs with h | ⟨L, b, h⟩
  · exact absurd h hne
  subst h
  have hb := hall b (by simp)
  simp only [List.concat_eq_append] at hall hd hb ⊢
  unfold resolveSegs
  simp only [List.map_append, List.map_cons, List.map_nil, List.dropLast_concat,
    List.getLast?_concat, Option.getD_some]
  cases L with
  | nil =>
    simp only [List.map_nil, foldSegs, List.foldl_nil, List.nil_append]
    exact segStep_keep hb.1 hb.2 (fun hf _ hw => hd b rfl hf hw)
  | cons i r =>
    have hi := hall i (by simp)
    have hfold : foldSegs isFile [] ((i :: r).map String.toList) = i :: r := by
      simp only [foldSegs, List.map_cons, List.foldl_cons]
      rw [segStep_keep hi.1 hi.2 (fun hf _ hw => hd i rfl hf hw)]
      have := foldSegs_keep (isFile := isFile) r [i] (by simp) (fun x hx => hall x (by simp [hx]))
      simpa [foldSegs] using this
    rw [hfold, segStep_keep hb.1 hb.2 (fun _ h => absurd h (by simp))]

/--
**`pathname` の往復。** list path の正規な URL では、`pathname` getter の値を setter に戻すと元に戻る。

opaque path の URL では `pathname` setter が何もしないので、往復は自明に成り立つ。
-/
theorem setPathname_pathname {u : Url} {t : List Char → Option String} (hv : ValidUrl u)
    (hc : canonicalUrl u t = true) : u.setPathname u.pathname = u := by
  have hp := canonical_parts hc
  cases hop : u.hasOpaquePath with
  | true =>
    unfold Url.setPathname
    rw [if_pos (by simp [hop])]
  | false =>
  rw [setPathname_eq _ _ hop]
  cases hpa : u.path with
  | «opaque» o => simp [Url.hasOpaquePath, hpa, Path.isOpaque] at hop
  | list segs =>
  have hsp := hv.pathSegs
  have hpc := hp.path
  have hdr := hp.drive
  rw [hpa] at hsp hpc hdr
  simp only [pathSegsOk, pathCanon, List.all_eq_true] at hsp hpc
  suffices hs : pathnameSpec u u.pathname = segs by
    rw [hs, ← hpa]
  unfold Url.pathname
  rw [hpa]
  cases segs with
  | nil =>
    unfold pathnameSpec
    rw [show (pathSerializer (.list [])).toList = [] from rfl, show stripTabNewline [] = [] from rfl]
    simp only
    rw [if_neg]
    intro h
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    rcases h with h | h
    · exact hp.specialPath h hpa
    · exact hp.hostPath h hpa
  | cons s0 rest =>
  have hne : s0 :: rest ≠ [] := by simp
  have hseg : ∀ s ∈ s0 :: rest, ∀ c ∈ s.toList,
      pathSet c = false ∧ c ≠ '/' ∧ (u.isSpecial = true → c ≠ '\\') := by
    intro s hs c hcs
    have h1 := hpc s hs
    have h2 := hsp s hs
    simp only [segOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h1
    simp only [noSlash, List.all_eq_true, bne_iff_ne, ne_eq] at h2
    refine ⟨encodedWith_all h1.1.1.1 c hcs, h2 c hcs, fun hs' => ?_⟩
    rcases h1.2 with h | h
    · rw [hs'] at h; cases h
    · have := List.all_eq_true.mp h c hcs
      simpa using this
  unfold pathnameSpec
  rw [pathSerializer_intercal _ hne]
  rw [stripTabNewline_eq_self (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    rcases intercal_mem _ c hc with rfl | ⟨x, hx, hcx⟩
    · decide
    · exact noTab_of_c0 (c0_of_pathSet (hseg x hx c hcx).1))]
  simp only
  rw [if_pos (by simp [isPathSep])]
  unfold pathSegments splitSegs
  rw [splitBy_intercal _ (by simp [isPathSep]) _ hne (by
    intro x hx c hcx
    obtain ⟨_, h2, h3⟩ := hseg x hx c hcx
    simp only [isPathSep, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff]
    refine ⟨h2, ?_⟩
    cases hsp' : u.isSpecial
    · exact Or.inl rfl
    · exact Or.inr (h3 hsp'))]
  rw [List.map_map]
  rw [List.map_congr_left (f := encodeSeg ∘ String.toList) (g := String.toList) (fun x hx =>
    show encodeSeg x.toList = x.toList from utf8PercentEncode_id (fun c hc => (hseg x hx c hc).1))]
  refine resolveSegs_keep _ hne (fun x hx => ?_) ?_
  · have h1 := hpc x hx
    simp only [segOk, Bool.and_eq_true, Bool.not_eq_true'] at h1
    exact ⟨h1.1.1.2, h1.1.2⟩
  · intro x hx hf hw
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    simp only [driveOk, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hdr
    simp only [beq_iff_eq] at hf
    rcases hdr with (h | h) | h
    · exact absurd hf h
    · rw [hw] at h; cases h
    · exact h

/-! ## `host` と `hostname` の往復 -/

/-- bracket の数え方を変えない文字は、`splitHostPort` を素通りする。 -/
theorem splitHostPort_pass (b : Bool) (rest : List Char) : ∀ (l : List Char),
    (∀ c ∈ l, c ≠ '[' ∧ c ≠ ']' ∧ (b = false → c ≠ ':')) →
    splitHostPort b (l ++ rest) = (l ++ (splitHostPort b rest).1, (splitHostPort b rest).2)
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := splitHostPort_pass b rest l (fun x hx => h x (by simp [hx]))
    simp only [List.cons_append, splitHostPort]
    rw [if_neg (by cases b <;> simp_all), if_neg (by simpa using hc.1),
      if_neg (by simpa using hc.2.1), ih]

/-- **serialize した host は、`splitHostPort` で一つの host として読まれる。** -/
theorem splitHostPort_host {sp : Bool} {h : Host} (hr : hostReadable sp h) (rest : List Char) :
    splitHostPort false ((hostSerializer h).toList ++ rest)
      = ((hostSerializer h).toList ++ (splitHostPort false rest).1, (splitHostPort false rest).2) := by
  rcases hr with hr | ⟨inner, he, hr⟩
  · exact splitHostPort_pass false rest _ (fun c hc =>
      have hn := not_forbidden_host (hr c hc)
      ⟨hn.2.2.1, hn.2.2.2.1, fun _ => hn.2.1⟩)
  · rw [he]
    simp only [List.cons_append, List.append_assoc, splitHostPort]
    rw [if_neg (by decide), if_pos (by decide : ('[' == '[') = true), List.nil_append,
      splitHostPort_pass true _ inner (fun c hc => ⟨(hr c hc).2.1, (hr c hc).2.2.1, by simp⟩)]
    simp only [List.nil_append, splitHostPort]
    simp

/-- serialize した host の文字は、区切りでも tab・改行でもない。 -/
theorem hostSer_chars {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hp : CanonParts u t) {h : Host} (hh : u.host = some h) :
    hostReadable u.isSpecial h ∧
      ∀ c ∈ (hostSerializer h).toList, hostDelim u.isSpecial c = false ∧
        c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  have hcan : h = Host.empty ∨ hostParser t (hostSerializer h).toList (!u.isSpecial) = some h := by
    by_cases he : h = Host.empty
    · exact Or.inl he
    · exact Or.inr (hp.hostIdem h hh he)
  obtain ⟨hok, hnc⟩ := hostReadable_of_canonical htok.noForbidden hcan
  refine ⟨hok, fun c hc => ⟨?_, ?_⟩⟩
  · rw [← isTerminator_eq_hostDelim]
    exact (hostReadable_auth hok c hc).2
  · have := hnc c hc
    simp only [isC0ControlOrSpace, decide_eq_false_iff_not] at this
    omega

/-- port を付けない形の往復。`hostname` と、port の無い `host` に使う。 -/
theorem hostSetterSpec_noPort {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hv : ValidUrl u) (hc : canonicalUrl u t = true) {h : Host} (hh : u.host = some h)
    (hop : u.hasOpaquePath = false) (isHostname : Bool) (hnf : u.scheme ≠ "file") :
    hostSetterSpec t u (hostSerializer h) isHostname = u := by
  have hp := canonical_parts hc
  obtain ⟨hok, hch⟩ := hostSer_chars htok hp hh
  unfold hostSetterSpec
  rw [if_neg (by simp [hop]), stripTabNewline_eq_self (fun c hc => (hch c hc).2)]
  simp only
  rw [if_neg hnf, takeWhile_all (fun c hc => by simp [(hch c hc).1])]
  have hs := splitHostPort_host hok []
  simp only [List.append_nil, splitHostPort] at hs
  rw [hs]
  simp only
  by_cases he : h = Host.empty
  · subst he
    have hsp : u.isSpecial = false := by
      have := hv.hostKind
      rw [hh] at this
      simp only [hostKindOkOf, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
      rcases this with h1 | h1
      · simpa [Url.isSpecial] using h1
      · exact absurd h1 hnf
    have hcred := hp.emptyNoCred hh
    have hpo := hv.emptyHostNoPort hh
    rw [if_neg (by simp [hsp, hcred, hpo])]
    rw [show (hostSerializer Host.empty).toList = [] from rfl, hsp]
    simp only [Bool.not_false]
    rw [show hostParser t [] true = some Host.empty from rfl]
    cases u; simp_all
  · have hne : (hostSerializer h).toList.isEmpty = false := by
      cases hx : (hostSerializer h).toList.isEmpty
      · rfl
      · have := hp.hostIdem h hh he
        rw [List.isEmpty_iff.mp hx] at this
        cases hb : u.isSpecial <;> simp [hb, hostParser, opaqueHostParser] at this
        exact absurd this.symm he
    rw [if_neg (by simp [hne]), hp.hostIdem h hh he]
    cases u; simp_all

/-- 空でない host の serialize は空でない。 -/
theorem hostSer_ne_nil {u : Url} {t : List Char → Option String} (hp : CanonParts u t) {h : Host}
    (hh : u.host = some h) (he : h ≠ Host.empty) : (hostSerializer h).toList.isEmpty = false := by
  cases hx : (hostSerializer h).toList.isEmpty
  · rfl
  · have := hp.hostIdem h hh he
    rw [List.isEmpty_iff.mp hx] at this
    cases hb : u.isSpecial <;> simp [hb, hostParser, opaqueHostParser] at this
    exact absurd this.symm he

/-- `file` URL の往復。`file` URL は port を持たないので `host` と `hostname` で同じである。 -/
theorem hostSetterSpec_file {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hc : canonicalUrl u t = true) {h : Host} (hh : u.host = some h)
    (hop : u.hasOpaquePath = false) (isHostname : Bool) (hf : u.scheme = "file") :
    hostSetterSpec t u (hostSerializer h) isHostname = u := by
  have hp := canonical_parts hc
  have hsp : u.isSpecial = true := by simp [Url.isSpecial, hf, isSpecialScheme]
  obtain ⟨_, hch⟩ := hostSer_chars htok hp hh
  rw [hsp] at hch
  unfold hostSetterSpec
  rw [if_neg (by simp [hop]), stripTabNewline_eq_self (fun c hc => (hch c hc).2)]
  simp only
  rw [if_pos hf, takeWhile_all (fun c hc => by
    have := (hch c hc).1
    simp only [hostDelim, Bool.or_eq_false_iff, Bool.true_and] at this
    simp [fileHostDelim, this.1.1.1, this.1.1.2, this.1.2, this.2])]
  by_cases he : h = Host.empty
  · subst he
    rw [if_pos (by rfl)]
    cases u; simp_all
  · have hidem := hp.hostIdem h hh he
    rw [hsp, Bool.not_true] at hidem
    rw [if_neg (by simp [hostSer_ne_nil hp hh he]), hidem]
    simp only
    rw [if_neg (hp.notLocal hf h hh)]
    cases u; simp_all

/-- port のある URL の `host` の往復。 -/
theorem hostSetterSpec_port {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hv : ValidUrl u) (hc : canonicalUrl u t = true) {h : Host} (hh : u.host = some h)
    {p : Nat} (hpo : u.port = some p) (hop : u.hasOpaquePath = false) (hnf : u.scheme ≠ "file") :
    hostSetterSpec t u (hostSerializer h ++ ":" ++ toString p) false = u := by
  have hp := canonical_parts hc
  obtain ⟨hok, hch⟩ := hostSer_chars htok hp hh
  have he : h ≠ Host.empty := by
    intro he; subst he
    rw [hv.emptyHostNoPort hh] at hpo; cases hpo
  have hl : (hostSerializer h ++ ":" ++ toString p).toList
      = (hostSerializer h).toList ++ ':' :: (toString p).toList := by simp
  have hdig := toString_digits p
  unfold hostSetterSpec
  rw [if_neg (by simp [hop]), hl, stripTabNewline_eq_self (by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (hch c hc).2
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · exact digit_noTab (hdig c hc))]
  simp only
  rw [if_neg hnf, takeWhile_all (by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · simp [(hch c hc).1]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [hostDelim]
    · have := hdig c hc
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
      have h1 : c ≠ '/' := fun h => by subst h; simp at this
      have h2 : c ≠ '?' := fun h => by subst h; simp at this
      have h3 : c ≠ '#' := fun h => by subst h; simp at this
      have h4 : c ≠ '\\' := fun h => by subst h; simp at this
      simp [hostDelim, h1, h2, h3, h4])]
  rw [splitHostPort_host hok]
  simp only [splitHostPort, show (':' == ':' && !false) = true from rfl, if_true, List.append_nil]
  rw [if_neg (by simp [hostSer_ne_nil hp hh he]), hp.hostIdem h hh he]
  simp only
  rw [takeWhile_all hdig]
  have hne : (toString p).toList.isEmpty = false := by
    cases h : (toString p).toList.isEmpty
    · rfl
    · exact absurd (by simp at h) (toString_ne_nil p)
  have hval : decimalOf (toString p).toList = p := by
    rw [decimalOf_eq_portValue, portValue_toString]
  rw [hval]
  have hlt := hv.portRange p hpo
  rw [if_neg (by simp; omega), if_neg (hp.port p hpo)]
  cases u; simp_all

/--
**`hostname` の往復。** 正規な URL では、`hostname` getter の値を setter に戻すと元に戻る。

例外は host が null で list path を持つ URL（`sc:/a`）で、`hostname` は `""` を返し、
setter は `""` で空の host を作る。
-/
theorem setHostname_hostname {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hv : ValidUrl u) (hc : canonicalUrl u t = true)
    (hex : u.host = none → u.hasOpaquePath = true) : u.setHostname u.hostname t = u := by
  rw [setHostname_eq]
  cases hop : u.hasOpaquePath with
  | true => unfold hostSetterSpec; rw [if_pos hop]
  | false =>
  cases hh : u.host with
  | none => rw [hex hh] at hop; cases hop
  | some h =>
  unfold Url.hostname
  rw [hh]
  by_cases hf : u.scheme = "file"
  · exact hostSetterSpec_file htok hc hh hop true hf
  · exact hostSetterSpec_noPort htok hv hc hh hop true hf

/-- **`host` の往復。** 例外は `hostname` と同じである。 -/
theorem setHost_hostAttr {u : Url} {t : List Char → Option String} (htok : ToAsciiOk t)
    (hv : ValidUrl u) (hc : canonicalUrl u t = true)
    (hex : u.host = none → u.hasOpaquePath = true) : u.setHost u.hostAttr t = u := by
  rw [setHost_eq]
  cases hop : u.hasOpaquePath with
  | true => unfold hostSetterSpec; rw [if_pos hop]
  | false =>
  cases hh : u.host with
  | none => rw [hex hh] at hop; cases hop
  | some h =>
  unfold Url.hostAttr
  rw [hh]
  by_cases hf : u.scheme = "file"
  · rw [hv.fileNoPort hf]
    exact hostSetterSpec_file htok hc hh hop false hf
  · cases hpo : u.port with
    | none => exact hostSetterSpec_noPort htok hv hc hh hop false hf
    | some p => exact hostSetterSpec_port htok hv hc hh hpo hop hf

/-! ## parse の結果についてまとめる -/

/--
**parse の結果では、getter の値を同じ属性の setter に戻すと URL は変わらない。**

`href` は `setHref_href`（`Url/Spec/Setters.lean`）にある。例外は三つで、どれも下の `example` に固定した。

* `hash`：fragment が空のとき。
* `search`：query が空のとき。
* `host` と `hostname`：host が null で list path を持つとき。
-/
theorem parseUrl_lens {t : List Char → Option String} (htok : ToAsciiOk t) {input : String}
    {base : Option String} {u : Url} (h : parseUrl input base t = some u) :
    u.setProtocol u.protocol = u ∧
    u.setUsername u.username = u ∧
    u.setPassword u.password = u ∧
    u.setPort u.portAttr = u ∧
    u.setPathname u.pathname = u ∧
    (u.fragment ≠ some "" → u.setHash u.hash = u) ∧
    (u.query ≠ some "" → u.setSearch u.search = u) ∧
    ((u.host = none → u.hasOpaquePath = true) →
      u.setHost u.hostAttr t = u ∧ u.setHostname u.hostname t = u) := by
  have hv := parseUrl_valid h
  have hc := parseUrl_canonical htok h
  exact ⟨setProtocol_protocol hv hc, setUsername_username hc, setPassword_password hc,
    setPort_portAttr hv hc, setPathname_pathname hv hc, setHash_hash hc, setSearch_search hc,
    fun hex => ⟨setHost_hostAttr htok hv hc hex, setHostname_hostname htok hv hc hex⟩⟩

/-! ## 往復の反例

どれも parse の結果である（`sc:/a#`、`sc:/a?`、`sc:/a`）。
-/

set_option maxRecDepth 8000 in
/-- **空の fragment は往復しない。** `hash` は `""` を返し、`hash` setter は `""` で fragment を null にする。 -/
example :
    parseUrl "sc:/a#" none asciiDomainToASCII
      = some { scheme := "sc", path := .list ["a"], fragment := some "" } ∧
    (({ scheme := "sc", path := .list ["a"], fragment := some "" } : Url).setHash "")
      = { scheme := "sc", path := .list ["a"] } ∧
    ({ scheme := "sc", path := .list ["a"], fragment := some "" } : Url).hash = "" := by
  refine ⟨by url_eval, by url_eval, rfl⟩

set_option maxRecDepth 8000 in
/-- **空の query は往復しない。** `search` についても同じである。 -/
example :
    parseUrl "sc:/a?" none asciiDomainToASCII
      = some { scheme := "sc", path := .list ["a"], query := some "" } ∧
    (({ scheme := "sc", path := .list ["a"], query := some "" } : Url).setSearch "")
      = { scheme := "sc", path := .list ["a"] } ∧
    ({ scheme := "sc", path := .list ["a"], query := some "" } : Url).search = "" := by
  refine ⟨by url_eval, by url_eval, rfl⟩

set_option maxRecDepth 8000 in
/--
**host が null で list path の URL は `host` / `hostname` で往復しない。**
getter は `""` を返し、setter は `""` で空の host を作る（`sc:/a` が `sc:///a` になる）。
-/
example :
    parseUrl "sc:/a" none asciiDomainToASCII = some { scheme := "sc", path := .list ["a"] } ∧
    (({ scheme := "sc", path := .list ["a"] } : Url).setHost "")
      = { scheme := "sc", host := some .empty, path := .list ["a"] } ∧
    (({ scheme := "sc", path := .list ["a"] } : Url).setHostname "")
      = { scheme := "sc", host := some .empty, path := .list ["a"] } ∧
    ({ scheme := "sc", path := .list ["a"] } : Url).hostAttr = "" ∧
    ({ scheme := "sc", path := .list ["a"] } : Url).hostname = "" := by
  refine ⟨by url_eval, by url_eval, by url_eval, rfl, rfl⟩

end Url.Spec
