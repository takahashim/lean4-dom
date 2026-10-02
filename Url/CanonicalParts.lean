import Url.CanonicalInv

/-!
# `CInv` の帰納段の足場

state machine の各遷移が `canonicalUrl` の成分を保つことを、遷移が使う関数ごとに示す。
`Url/StepCanonical.lean` の帰納段は、ここの補題を simp に渡して閉じる。
-/

namespace Url

open Infra

/-! ## percent-encode の出力 -/

@[simp] theorem encodedWith_empty (set : Char → Bool) : encodedWith set "" = true := rfl

@[simp] theorem encodedWith_append (set : Char → Bool) (s t : String) :
    encodedWith set (s ++ t) = (encodedWith set s && encodedWith set t) := by
  simp [encodedWith, String.toList_append, List.all_append]

theorem encodedWith_ofList (set : Char → Bool) (l : List Char) :
    encodedWith set (String.ofList l) = l.all (fun c => !set c) := by
  simp [encodedWith]

/--
percent-encode しても出てこない set。

encode が足すのは `%` と 16 進の数字だけなので、その二つを含まない set なら、
encode した結果はその set について encode 済みである。URL Standard の
percent-encode set はどれもこれを満たす。
-/
structure PctSafe (set : Char → Bool) : Prop where
  pct : set '%' = false
  alnum : ∀ c, isAsciiAlphanumeric c = true → set c = false

/-- **encode した結果は encode 済みである。** -/
theorem encodedWith_utf8PercentEncode {set : Char → Bool} (hs : PctSafe set) (l : List Char) :
    encodedWith set (String.ofList (utf8PercentEncode set l)) = true := by
  rw [encodedWith_ofList, List.all_eq_true]
  intro c hc
  unfold utf8PercentEncode at hc
  obtain ⟨x, -, hc⟩ := List.mem_flatMap.mp hc
  split at hc
  · obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp hc
    have ha := percentEncodeByte_alnum b c hb
    simp only [Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with rfl | ha
    · simp [hs.pct]
    · simp [hs.alnum c ha]
  · next hx =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simpa using hx

theorem encodedWith_encChar {set : Char → Bool} (hs : PctSafe set) (c : Char) :
    encodedWith set (encChar set c) = true :=
  encodedWith_utf8PercentEncode hs [c]

/-- alphanumeric な文字は、どの percent-encode set にも入らない。 -/
theorem alnum_range {c : Char} (h : isAsciiAlphanumeric c = true) :
    (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) ∨ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) ∨
      (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A) := by
  simp only [isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
    isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- 文字の比較を code point の比較に落とす。 -/
theorem char_ne_of_toNat {c d : Char} (h : c.toNat ≠ d.toNat) : c ≠ d := by
  intro he; exact h (he ▸ rfl)

local macro "pct_safe" : tactic =>
  `(tactic| (refine ⟨by decide, fun c hc => ?_⟩
             have hr := alnum_range hc
             simp only [userinfoSet, pathSet, querySet, specialQuerySet, fragmentSet,
               c0ControlSet, isC0Control, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
               decide_eq_false_iff_not, Bool.and_eq_false_iff, Nat.not_le, ne_eq]
             and_intros
             all_goals
               first
               | omega
               | (intro h; subst h; simp at hr)
               | (rcases hr with hr | hr | hr <;> omega)))

theorem pctSafe_c0 : PctSafe c0ControlSet := by pct_safe
theorem pctSafe_fragment : PctSafe fragmentSet := by pct_safe
theorem pctSafe_query : PctSafe querySet := by pct_safe
theorem pctSafe_specialQuery : PctSafe specialQuerySet := by pct_safe
theorem pctSafe_path : PctSafe pathSet := by pct_safe
theorem pctSafe_userinfo : PctSafe userinfoSet := by pct_safe

@[simp] theorem encodedWith_encChar_userinfo (c : Char) :
    encodedWith userinfoSet (encChar userinfoSet c) = true := encodedWith_encChar pctSafe_userinfo c
@[simp] theorem encodedWith_encChar_fragment (c : Char) :
    encodedWith fragmentSet (encChar fragmentSet c) = true := encodedWith_encChar pctSafe_fragment c
@[simp] theorem encodedWith_encChar_c0 (c : Char) :
    encodedWith c0ControlSet (encChar c0ControlSet c) = true := encodedWith_encChar pctSafe_c0 c
@[simp] theorem encodedWith_encChar_path (c : Char) :
    encodedWith pathSet (encChar pathSet c) = true := encodedWith_encChar pctSafe_path c

/-- percent-encode は、`%` でも alphanumeric でもない文字 `d` を作らない。 -/
theorem encChar_avoid {set : Char → Bool} {c d : Char} (h1 : isAsciiAlphanumeric d = false)
    (h2 : d ≠ '%') (h : c ≠ d) : ∀ x ∈ (encChar set c).toList, x ≠ d := by
  intro x hx
  unfold encChar at hx
  rw [String.toList_ofList] at hx
  exact utf8PercentEncode_avoid h1 h2
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; exact h)
    x hx

/-! ## path -/

theorem isDoubleDot_drive (a : Char) : isDoubleDot [a, ':'] = false := by
  unfold isDoubleDot asciiLowercase
  simp only [String.toList_ofList, List.map]
  rw [show asciiLowerChar ':' = ':' by decide]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro h <;> have := congrArg String.toList h <;>
    simp at this

theorem isSingleDot_drive (a : Char) : isSingleDot [a, ':'] = false := by
  unfold isSingleDot asciiLowercase
  simp only [String.toList_ofList, List.map]
  rw [show asciiLowerChar ':' = ':' by decide]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨?_, ?_⟩ <;> intro h <;> have := congrArg String.toList h <;>
    simp at this

@[simp] theorem segOk_empty (sp : Bool) : segOk sp "" = true := by
  simp [segOk]; decide

/-- buffer を segment にするときの条件。`.` と `..` は `pathStepUrl` が分岐で除く。 -/
theorem segOk_of_buffer {sp : Bool} {buf : List Char}
    (he : encodedWith pathSet (String.ofList buf) = true)
    (hb : sp = true → ∀ c ∈ buf, c ≠ '\\')
    (hs : isSingleDot buf = false) (hd : isDoubleDot buf = false) :
    segOk sp (String.ofList buf) = true := by
  simp only [segOk, String.toList_ofList, he, hs, hd, Bool.not_false, Bool.and_true,
    Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, bne_iff_ne, ne_eq]
  cases sp with
  | false => exact Or.inl rfl
  | true => exact Or.inr (hb rfl)

/-- Windows drive letter の直しは `c|` を `c:` にするだけ。 -/
theorem windowsDriveBuffer_spec (u : Url) (buf : List Char) :
    (pathStepUrl.windowsDriveBuffer u buf = buf ∧
        (u.scheme = "file" → u.path = .list [] → isWindowsDrive buf = false)) ∨
      ∃ a b, buf = [a, b] ∧ isAsciiAlpha a = true ∧
        pathStepUrl.windowsDriveBuffer u buf = [a, ':'] ∧ u.scheme = "file" ∧ u.path = .list [] := by
  unfold pathStepUrl.windowsDriveBuffer
  cases hw : isWindowsDrive buf with
  | false => left; simp
  | true =>
    cases hp : u.path with
    | «opaque» o => left; simp
    | list segs =>
      cases segs with
      | cons s r => left; simp
      | nil =>
        by_cases hf : u.scheme = "file"
        · right
          match buf, hw with
          | [a, b], hw =>
            simp only [isWindowsDrive, Bool.and_eq_true] at hw
            exact ⟨a, b, rfl, hw.1, by simp [hf], hf, rfl⟩
        · left; simp [hf]

/-- Windows drive letter の直しは segment の条件を保つ。 -/
theorem segOk_windowsDriveBuffer {sp : Bool} {u : Url} {buf : List Char}
    (he : encodedWith pathSet (String.ofList buf) = true)
    (hb : sp = true → ∀ c ∈ buf, c ≠ '\\')
    (hs : isSingleDot buf = false) (hd : isDoubleDot buf = false) :
    segOk sp (String.ofList (pathStepUrl.windowsDriveBuffer u buf)) = true := by
  rcases windowsDriveBuffer_spec u buf with ⟨hw, -⟩ | ⟨a, b, rfl, -, hw, -, -⟩
  · rw [hw]; exact segOk_of_buffer he hb hs hd
  · rw [hw]
    refine segOk_of_buffer ?_ ?_ (isSingleDot_drive a) (isDoubleDot_drive a)
    · rw [encodedWith_ofList] at he ⊢
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at he ⊢
      exact ⟨he.1, by decide⟩
    · intro hsp c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hb hsp c (by simp)
      · decide

theorem pathCanon_shortenPath {sp : Bool} {u : Url} (h : pathCanon sp u.path = true) :
    pathCanon sp (shortenPath u).path = true := by
  rcases shortenPath_spec u with hs | ⟨segs, hp, hs⟩
  · rw [hs]; exact h
  · rw [hs]
    rw [hp] at h
    simp only [pathCanon, List.all_eq_true] at h ⊢
    exact fun x hx => h x (List.dropLast_subset _ hx)

theorem pathCanon_appendSegment {sp : Bool} {u : Url} {s : String} (h : pathCanon sp u.path = true)
    (hs : segOk sp s = true) : pathCanon sp (appendSegment u s).path = true := by
  rcases appendSegment_spec u s with ha | ⟨segs, hp, ha⟩
  · rw [ha]; exact h
  · rw [ha]
    rw [hp] at h
    simp only [pathCanon, List.all_eq_true, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at h ⊢
    rintro x (hx | rfl)
    · exact h x hx
    · exact hs

theorem pathCanon_pathStepUrl {sp : Bool} {u : Url} {slash : Bool} {buf : List Char}
    (h : pathCanon sp u.path = true)
    (he : encodedWith pathSet (String.ofList buf) = true)
    (hb : sp = true → ∀ c ∈ buf, c ≠ '\\') :
    pathCanon sp (pathStepUrl u slash buf).path = true := by
  unfold pathStepUrl
  split
  · split
    · exact pathCanon_shortenPath h
    · exact pathCanon_appendSegment (pathCanon_shortenPath h) (by simp)
  · next hd =>
    split
    · split
      · exact h
      · exact pathCanon_appendSegment h (by simp)
    · next hs =>
      exact pathCanon_appendSegment h
        (segOk_windowsDriveBuffer he hb (by simpa using hs) (by simpa using hd))

theorem pathCanon_fileBasePath {sp : Bool} {u : Url} {input : List Char}
    (h : pathCanon sp u.path = true) :
    pathCanon sp (fileBasePath u input).path = true := by
  unfold fileBasePath
  split
  · rfl
  · exact pathCanon_shortenPath h

theorem pathCanon_fileSlashDrive {sp : Bool} {u : Url} {bp : Path} {input : List Char}
    (h : pathCanon sp u.path = true) (hbp : pathCanon sp bp = true) :
    pathCanon sp (fileSlashDrive u bp input).path = true := by
  unfold fileSlashDrive
  split
  · next s rest =>
    split
    · simp only [pathCanon, List.all_cons, Bool.and_eq_true] at hbp
      exact pathCanon_appendSegment h hbp.1
    · exact h
  · exact h

/-- segment を一つ足せば path は空でない。 -/
theorem appendSegment_ne_nil (u : Url) (s : String) : (appendSegment u s).path ≠ .list [] := by
  unfold appendSegment
  split
  · next o hp => rw [hp]; simp
  · simp

/-- path state が `/` 以外で segment を確定させると、path は空でない。 -/
theorem pathStepUrl_ne_nil (u : Url) (buf : List Char) :
    (pathStepUrl u false buf).path ≠ .list [] := by
  unfold pathStepUrl
  split
  · exact appendSegment_ne_nil _ _
  · split
    · exact appendSegment_ne_nil _ _
    · exact appendSegment_ne_nil _ _

/-! ## Windows drive letter -/

theorem driveOk_shortenPath {s : String} {u : Url} (h : driveOk s u.path = true) :
    driveOk s (shortenPath u).path = true := by
  rcases shortenPath_spec u with hs | ⟨segs, hp, hs⟩
  · rw [hs]; exact h
  · rw [hs]
    rw [hp] at h
    show driveOk s (.list segs.dropLast) = true
    match segs, h with
    | [], _ => rfl
    | [_], _ => rfl
    | s :: t :: rest, h =>
      rw [List.dropLast_cons_of_ne_nil (by simp)]
      exact h

theorem driveOk_appendSegment {sc : String} {u : Url} {s : String} (h : driveOk sc u.path = true)
    (hs : u.path = .list [] →
      (sc != "file" || !isWindowsDrive s.toList || isNormalizedWindowsDrive s.toList) = true) :
    driveOk sc (appendSegment u s).path = true := by
  rcases appendSegment_spec u s with ha | ⟨segs, hp, ha⟩
  · rw [ha]; exact h
  · rw [ha]
    show driveOk sc (.list (segs ++ [s])) = true
    cases segs with
    | nil => exact hs hp
    | cons x rest => rw [hp] at h; exact h

theorem driveOk_pathStepUrl {u : Url} {slash : Bool} {buf : List Char}
    (h : driveOk u.scheme u.path = true) :
    driveOk u.scheme (pathStepUrl u slash buf).path = true := by
  unfold pathStepUrl
  split
  · split
    · exact driveOk_shortenPath h
    · exact driveOk_appendSegment (driveOk_shortenPath h) (fun _ => by simp [isWindowsDrive])
  · split
    · split
      · exact h
      · exact driveOk_appendSegment h (fun _ => by simp [isWindowsDrive])
    · refine driveOk_appendSegment h fun hp => ?_
      rw [String.toList_ofList]
      rcases windowsDriveBuffer_spec u buf with ⟨hw, hnd⟩ | ⟨a, b, rfl, ha, hw, -, -⟩
      · rw [hw]
        by_cases hf : u.scheme = "file"
        · simp [hnd hf hp]
        · simp [hf]
      · rw [hw]; simp [isNormalizedWindowsDrive, ha]

theorem driveOk_fileBasePath {s : String} {u : Url} {input : List Char}
    (h : driveOk s u.path = true) : driveOk s (fileBasePath u input).path = true := by
  unfold fileBasePath
  split
  · rfl
  · exact driveOk_shortenPath h

theorem driveOk_fileSlashDrive {s : String} {u : Url} {bp : Path} {input : List Char}
    (h : driveOk s u.path = true) :
    driveOk s (fileSlashDrive u bp input).path = true := by
  unfold fileSlashDrive
  split
  · split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      exact driveOk_appendSegment h (fun _ => by simp [hc.2])
    · exact h
  · exact h

/-! ## userinfo、query、port、scheme -/

/-- authority state の振り分けは、encode 済みの username / password に encode した文字を足すだけ。 -/
theorem userinfoFold_enc (buf : List Char) (p : Url × Bool)
    (hu : encodedWith userinfoSet p.1.username = true)
    (hp : encodedWith userinfoSet p.1.password = true) :
    encodedWith userinfoSet (buf.foldl userinfoStep p).1.username = true ∧
      encodedWith userinfoSet (buf.foldl userinfoStep p).1.password = true := by
  induction buf generalizing p with
  | nil => exact ⟨hu, hp⟩
  | cons c rest ih =>
    apply ih
    · unfold userinfoStep; split
      · exact hu
      · split <;> simp [hu]
    · unfold userinfoStep; split
      · exact hp
      · split <;> simp [hp]

theorem pctSafe_ite {b : Bool} {s t : Char → Bool} (hs : PctSafe s) (ht : PctSafe t) :
    PctSafe (if b then s else t) := by
  cases b <;> simpa

/-- query state が書く query は encode 済み。 -/
theorem queryOf_enc {ctx : PCtx}
    (h : ∀ q, ctx.url.query = some q →
      encodedWith (if ctx.url.isSpecial then specialQuerySet else querySet) q = true) :
    encodedWith (if ctx.url.isSpecial then specialQuerySet else querySet) (queryOf ctx) = true := by
  unfold queryOf
  rw [encodedWith_append]
  refine Bool.and_eq_true_iff.mpr ⟨?_, encodedWith_utf8PercentEncode
    (pctSafe_ite pctSafe_specialQuery pctSafe_query) _⟩
  cases hq : ctx.url.query with
  | none => rfl
  | some q => exact h q hq

/-- port state が書く port は既定 port でない。 -/
theorem portDone_portOk {ctx ctx2 : PCtx} (h : portDone ctx = some ctx2)
    (hin : ∀ p, ctx.url.port = some p → defaultPort ctx.url.scheme ≠ some p) :
    ∀ p, ctx2.url.port = some p → defaultPort ctx2.url.scheme ≠ some p := by
  rw [portDone_scheme h]
  unfold portDone at h
  split at h
  · rw [← Option.some.inj h]; exact hin
  · split at h
    · simp at h
    · rw [← Option.some.inj h]
      intro p hp
      simp only [portSet, portOf] at hp
      split at hp
      · simp at hp
      · next hne =>
        rw [← Option.some.inj hp]
        intro he; rw [he] at hne; simp at hne

/-- 一文字を小文字にしたもの。 -/
@[simp] theorem asciiLowercase_singleton (c : Char) :
    (asciiLowercase (String.ofList [c])).toList = [asciiLowerChar c] := by
  simp [asciiLowercase]

theorem lowerChar_isLower {c : Char} (h : isAsciiAlpha c = true) :
    isAsciiLowerAlpha (asciiLowerChar c) = true := by
  unfold asciiLowerChar
  by_cases hu : isAsciiUpperAlpha c = true
  · rw [if_pos hu]
    simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at hu
    simp only [isAsciiLowerAlpha, Bool.and_eq_true, decide_eq_true_eq]
    rw [toNat_ofNat_ascii (by omega)]
    omega
  · rw [if_neg hu]
    simp only [isAsciiAlpha, isAsciiUpperAlpha, isAsciiLowerAlpha, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h hu ⊢
    omega

/-- scheme の文字を小文字にすると canonical な scheme の残りの文字になる。 -/
theorem lowerChar_schemeRest {c : Char}
    (h : (isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.') = true) :
    (isAsciiDigit (asciiLowerChar c) || isAsciiLowerAlpha (asciiLowerChar c) ||
      asciiLowerChar c == '+' || asciiLowerChar c == '-' || asciiLowerChar c == '.') = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · simp only [isAsciiAlphanumeric, Bool.or_eq_true] at h
    rcases h with h | h
    · have hn : asciiLowerChar c = c := by
        unfold asciiLowerChar
        rw [if_neg]
        simp only [isAsciiDigit, isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        omega
      rw [hn]; simp [h]
    · simp [lowerChar_isLower h]
  all_goals (subst h; decide)

/-- 一文字を小文字にした文字列。`String.ofList [c]` は simp で `String.singleton c` になる。 -/
@[simp] theorem asciiLowercase_singleton' (c : Char) :
    asciiLowercase (String.singleton c) = String.ofList [asciiLowerChar c] := by
  simp [asciiLowercase]

/-- scheme start state が積む一文字目は canonical な scheme である。 -/
theorem canonicalScheme_start {c : Char} (h : isAsciiAlpha c = true) :
    canonicalScheme (String.ofList [asciiLowerChar c]) = true := by
  simp [canonicalScheme, lowerChar_isLower h]

/-- scheme state が一文字足しても canonical な scheme のまま。 -/
theorem canonicalScheme_push {buf : List Char} {c : Char}
    (hb : canonicalScheme (String.ofList buf) = true)
    (h : (isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.') = true) :
    canonicalScheme (String.ofList (buf ++ [asciiLowerChar c])) = true := by
  unfold canonicalScheme at hb ⊢
  simp only [String.toList_ofList] at hb ⊢
  match buf, hb with
  | a :: rest, hb =>
    simp only [List.cons_append, Bool.and_eq_true, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true] at hb ⊢
    exact ⟨hb.1, hb.2, lowerChar_schemeRest h⟩

/-! ## 入力 -/

/-- 後ろを取っても、空でなければ末尾は変わらない。 -/
theorem getLast?_cons_ne {c : Char} {rest : List Char} {d : Char}
    (h : (c :: rest).getLast? ≠ some d) : rest.getLast? ≠ some d := by
  cases rest with
  | nil => simp
  | cons x t => simpa [List.getLast?_cons_cons] using h

/-! ## `canonicalUrl` を成分に分ける

base から成分を写す遷移では、base の `canonicalUrl` を `CInv` の field の形で使う。
-/

/-- `canonicalUrl` の成分。`canonicalUrl_of` の仮定と同じ形である。 -/
structure CanonParts (u : Url) : Prop where
  scheme : canonicalScheme u.scheme = true
  port : ∀ p, u.port = some p → defaultPort u.scheme ≠ some p
  username : encodedWith userinfoSet u.username = true
  password : encodedWith userinfoSet u.password = true
  query : ∀ q, u.query = some q →
    encodedWith (if u.isSpecial then specialQuerySet else querySet) q = true
  fragment : ∀ f, u.fragment = some f → encodedWith fragmentSet f = true
  path : pathCanon u.isSpecial u.path = true
  trailing : ∀ o, u.path = .opaque o → o.toList.getLast? ≠ some ' '
  hostPath : u.host = none → u.path ≠ .list []
  specialPath : u.isSpecial = true → u.path ≠ .list []
  hostIdem : ∀ h, u.host = some h → h ≠ Host.empty →
    hostParser asciiDomainToASCII (hostSerializer h).toList (!u.isSpecial) = some h
  notLocal : u.scheme = "file" → ∀ h, u.host = some h → hostSerializer h ≠ "localhost"
  drive : driveOk u.scheme u.path = true
  specialHost : u.isSpecial = true → u.host.isSome = true
  emptyNoCred : u.host = some Host.empty → u.includesCredentials = false

theorem canonical_parts {u : Url} (hc : canonicalUrl u = true) : CanonParts u := by
  simp only [canonicalUrl, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩ := hc
  refine ⟨c1, ?_, c3, c4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hp] at c2; simpa using c2
  · intro q hq; rw [hq] at c5; exact c5
  · intro f hf; rw [hf] at c6; exact c6
  · cases hpa : u.path with
    | «opaque» o =>
      rw [hpa] at c7
      simp only [Bool.and_eq_true] at c7
      simp only [pathCanon, Bool.and_eq_true]
      exact ⟨⟨c7.1.1.1, c7.1.2⟩, c7.2⟩
    | list segs => rw [hpa] at c7; exact c7
  · intro o hpa
    rw [hpa] at c7
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at c7
    exact c7.1.1.2
  · intro hh hpa; rw [hh, hpa] at c8; exact absurd c8 (by simp)
  · intro hs hpa; rw [hs, hpa] at c9; exact absurd c9 (by simp)
  · intro h hh hne
    rw [hh] at c10
    cases h with
    | empty => exact absurd rfl hne
    | _ => simpa using c10
  · intro hf h hh
    rw [hh] at c11
    simpa [hf] using c11
  · cases hpa : u.path with
    | «opaque» _ => rfl
    | list segs =>
      cases segs with
      | nil => rfl
      | cons s r => rw [hpa] at c12; exact c12
  · intro hs; rw [hs] at c13; simpa using c13
  · intro hh; rw [hh] at c14; simpa using c14

/-! ## simp の補題 -/

@[simp] theorem pathCanon_nil (sp : Bool) : pathCanon sp (.list []) = true := rfl
@[simp] theorem pathCanon_opaque_empty (sp : Bool) : pathCanon sp (.opaque "") = true := by
  simp [pathCanon]
@[simp] theorem driveOk_nil (s : String) : driveOk s (.list []) = true := rfl
@[simp] theorem driveOk_opaque (s o : String) : driveOk s (.opaque o) = true := rfl

@[simp] theorem canonicalScheme_singleton {c : Char} (h : isAsciiAlpha c = true) :
    canonicalScheme (String.singleton (asciiLowerChar c)) = true := by
  have := canonicalScheme_start h
  simpa using this

@[simp] theorem canonicalScheme_push' {buf : List Char} {c : Char}
    (hb : canonicalScheme (String.ofList buf) = true)
    (h : (isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.') = true) :
    canonicalScheme ((String.ofList buf).push (asciiLowerChar c)) = true := by
  have := canonicalScheme_push hb h
  rw [String.ofList_append] at this
  simpa using this

@[simp] theorem userinfoFold_query (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.query = p.1.query := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

@[simp] theorem userinfoFold_fragment (buf : List Char) (p : Url × Bool) :
    (buf.foldl userinfoStep p).1.fragment = p.1.fragment := by
  obtain ⟨_, _, h⟩ := userinfoFold_spec buf p; rw [h]

/-- `step` が受け取る入力。`c` を先頭に戻したもの。 -/
def cpList : Cp → List Char → List Char
  | some ch, rest => ch :: rest
  | none, _ => []

/-! ## authority state から host state へ -/

/--
authority state が host state へ渡す入力の先頭は terminator でない。

credentials があれば `@` を見ていて、guard により buffer は空でない。
host state が読み直すのは buffer の先頭からで、buffer に terminator は無い。
-/
theorem authority_hostCred {sp creds seen : Bool} {buf inp : List Char}
    (haa : creds = true → seen = true) (hab : ∀ c ∈ buf, isTerminator sp (some c) = false)
    (hg : ¬(seen && buf.isEmpty) = true) (hc : creds = true) :
    ∃ ch t, buf ++ inp = ch :: t ∧ isTerminator sp (some ch) = false := by
  have ha := haa hc
  cases buf with
  | nil => simp [ha] at hg
  | cons b rest => exact ⟨b, rest ++ inp, rfl, hab b (by simp)⟩

/-! ## host state -/

/--
host state が terminator で empty host を書くなら credentials は無い。

empty host を返すのは buffer が空のときだけで（`hostParser_empty`）、
そのとき credentials があれば次の文字は terminator でないはずだった（`CInv.hostCred`）。
-/
theorem host_emptyNoCred {sp creds : Bool} {f : List Char → Option String} {buf : List Char}
    {c : Cp} {rest input : List Char} {h : Host}
    (hhc : buf = [] → creds = true → ∃ ch t, input = ch :: t ∧ isTerminator sp (some ch) = false)
    (hin : input = cpList c rest)
    (ht : isTerminator sp c = true) (hp : hostParser f buf (!sp) = some h) :
    some h = some Host.empty → creds = false := by
  intro he
  cases he
  have hb := hostParser_empty hp
  cases hc : creds with
  | false => rfl
  | true =>
    obtain ⟨ch, t, hi, hn⟩ := hhc hb hc
    cases c with
    | none => simp [cpList] at hin; rw [hin] at hi; simp at hi
    | some x =>
      simp only [cpList] at hin
      rw [hin] at hi
      simp only [List.cons.injEq] at hi
      rw [hi.1] at ht
      rw [ht] at hn
      exact absurd hn (by simp)

@[simp] theorem canonicalScheme_file : canonicalScheme "file" = true := by decide
@[simp] theorem hostSerializer_empty : hostSerializer Host.empty = "" := rfl

section
variable (u : Url) (s : String) (input : List Char) (bp : Path)
@[simp] theorem shortenPath_query : (shortenPath u).query = u.query := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]
@[simp] theorem shortenPath_fragment : (shortenPath u).fragment = u.fragment := by
  rcases shortenPath_spec u with h | ⟨_, _, h⟩ <;> rw [h]
@[simp] theorem appendSegment_query : (appendSegment u s).query = u.query := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]
@[simp] theorem appendSegment_fragment : (appendSegment u s).fragment = u.fragment := by
  rcases appendSegment_spec u s with h | ⟨_, _, h⟩ <;> rw [h]
@[simp] theorem fileBasePath_query : (fileBasePath u input).query = u.query := by
  unfold fileBasePath; split <;> simp
@[simp] theorem fileBasePath_fragment : (fileBasePath u input).fragment = u.fragment := by
  unfold fileBasePath; split <;> simp
@[simp] theorem fileSlashDrive_query : (fileSlashDrive u bp input).query = u.query := by
  unfold fileSlashDrive; split <;> (try split) <;> simp
@[simp] theorem fileSlashDrive_fragment : (fileSlashDrive u bp input).fragment = u.fragment := by
  unfold fileSlashDrive; split <;> (try split) <;> simp
@[simp] theorem pathStepUrl_fragment (slash : Bool) (buf : List Char) :
    (pathStepUrl u slash buf).fragment = u.fragment := by
  obtain ⟨_, h⟩ := pathStepUrl_spec u slash buf; rw [h]
end

@[simp] theorem userinfoStep_query (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.query = p.1.query := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

@[simp] theorem userinfoStep_fragment (p : Url × Bool) (c : Char) :
    (userinfoStep p c).1.fragment = p.1.fragment := by
  unfold userinfoStep; split
  · rfl
  · split <;> rfl

/-- path が空なら、host を持つ非 special な URL である。 -/
theorem CanonParts.pathNil {u : Url} (h : CanonParts u) :
    u.path = .list [] → u.host.isSome = true ∧ u.isSpecial = false := by
  intro hp
  refine ⟨?_, ?_⟩
  · cases hh : u.host with
    | none => exact absurd hp (h.hostPath hh)
    | some _ => rfl
  · cases hs : u.isSpecial with
    | false => rfl
    | true => exact absurd hp (h.specialPath hs)

/-- host state が書く host は、serialize して読み直すと戻る。 -/
theorem host_idem {f : List Char → Option String} {buf : List Char} {b : Bool} {h : Host}
    (hf : f = asciiDomainToASCII) (hp : hostParser f buf b = some h) :
    ∀ h', some h = some h' → h' ≠ Host.empty → hostParser f (hostSerializer h').toList b = some h' := by
  intro h' hh hne
  cases hh
  subst hf
  exact hostParser_idem hp hne

/-- 空でない buffer から host parser が empty host を返すことは無い。 -/
theorem host_some_ne_empty {f : List Char → Option String} {buf : List Char} {b : Bool} {h : Host}
    {P : Prop} (hp : hostParser f buf b = some h) (hne : ¬buf.isEmpty = true) :
    some h = some Host.empty → P := by
  intro he
  cases he
  exact absurd (by rw [hostParser_empty hp]; rfl) hne

/-- file host state が書く host（`localhost` は empty host に直す）も同じ。 -/
theorem fileHost_idem {f : List Char → Option String} {buf : List Char} {b : Bool} {h : Host}
    (hf : f = asciiDomainToASCII) (hp : hostParser f buf b = some h) :
    ∀ h', some (if hostSerializer h == "localhost" then Host.empty else h) = some h' →
      h' ≠ Host.empty → hostParser f (hostSerializer h').toList b = some h' := by
  intro h' hh hne
  split at hh
  · cases hh; exact absurd rfl hne
  · exact host_idem hf hp h' hh hne

/-- file host state が書く host は `localhost` でない。 -/
theorem fileHost_notLocal {P : Prop} {h : Host} :
    P → ∀ h', some (if hostSerializer h == "localhost" then Host.empty else h) = some h' →
      hostSerializer h' ≠ "localhost" := by
  intro _ h' hh
  split at hh
  · cases hh; simp
  · next hn => cases hh; simpa using hn

/-- Windows drive letter の buffer は encode 済みで、`\\` を含まない。 -/
theorem pathBuf_of_drive {buf : List Char} (h : isWindowsDrive buf = true) :
    encodedWith pathSet (String.ofList buf) = true ∧ ∀ c ∈ buf, c ≠ '\\' := by
  match buf, h with
  | [a, b], h =>
    simp only [isWindowsDrive, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hb⟩ := h
    have hpa : pathSet a = false := pctSafe_path.alnum a (by simp [isAsciiAlphanumeric, ha])
    have hna : a ≠ '\\' := by
      intro he; rw [he] at ha; revert ha; decide
    rw [encodedWith_ofList]
    rcases hb with rfl | rfl
    · simp [hpa, hna]; decide
    · simp [hpa, hna]; decide

/-! ## opaque path のまま変わらないこと -/

section
variable (u : Url) (s : String) (input : List Char) (bp : Path) (o : String)
@[simp] theorem shortenPath_path_opaque : (shortenPath u).path = .opaque o ↔ u.path = .opaque o := by
  rcases shortenPath_spec u with h | ⟨segs, hp, h⟩
  · rw [h]
  · rw [h, hp]; simp
@[simp] theorem appendSegment_path_opaque :
    (appendSegment u s).path = .opaque o ↔ u.path = .opaque o := by
  rcases appendSegment_spec u s with h | ⟨segs, hp, h⟩
  · rw [h]
  · rw [h, hp]; simp
@[simp] theorem fileBasePath_path_opaque :
    (fileBasePath u input).path = .opaque o ↔ u.path = .opaque o ∧ startsWithWindowsDrive input = false := by
  unfold fileBasePath; split <;> simp_all
@[simp] theorem fileSlashDrive_path_opaque :
    (fileSlashDrive u bp input).path = .opaque o ↔ u.path = .opaque o := by
  unfold fileSlashDrive; split <;> (try split) <;> simp
@[simp] theorem pathStepUrl_path_opaque (slash : Bool) (buf : List Char) :
    (pathStepUrl u slash buf).path = .opaque o ↔ u.path = .opaque o := by
  unfold pathStepUrl
  split
  · split <;> simp
  · split
    · split <;> simp
    · simp
@[simp] theorem appendOpaque_query : (appendOpaque u s).query = u.query := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]
@[simp] theorem appendOpaque_fragment : (appendOpaque u s).fragment = u.fragment := by
  rcases appendOpaque_spec u s with h | ⟨_, _, h⟩ <;> rw [h]
end


theorem encodedWith_getD {set : Char → Bool} {o : Option String}
    (h : ∀ f, o = some f → encodedWith set f = true) : encodedWith set (o.getD "") = true := by
  cases o with
  | none => rfl
  | some f => exact h f rfl

/-! ## opaque path state -/

/--
**opaque path state が一文字ぶん積んでも `CInv` は保たれる。**

積む文字列 `add` について、encode 済みで `?` も `#` も含まず、空でなく、
`/` で始まるなら元の文字が `/` で、space で終わるなら次の文字が来ることを要求する。
`appendOpaque` は path 以外を変えないので、残りの field はそのまま運べる。
-/
theorem CInv.opaqueAppend {base : Option Url} {input rest : List Char} {ch : Char} {ctx : PCtx}
    {add : String} (h : CInv base .opaquePath input ctx) (hin : input = ch :: rest)
    (henc : encodedWith c0ControlSet add = true)
    (hqh : ∀ c ∈ add.toList, c ≠ '?' ∧ c ≠ '#')
    (hne : add.toList ≠ [])
    (hhead : add.toList.head? = some '/' → ch = '/')
    (hlast : add.toList.getLast? = some ' ' → ∃ c t, rest = c :: t ∧ c ≠ '?' ∧ c ≠ '#') :
    CInv base .opaquePath rest { ctx with url := appendOpaque ctx.url add } := by
  subst hin
  have hie := h.inputEnd rfl
  rcases appendOpaque_spec ctx.url add with hu | ⟨o, hp, hu⟩
  · -- path が opaque でなければ何も変わらない
    have hlist : ∀ o, ctx.url.path ≠ .opaque o := by
      intro o hp
      unfold appendOpaque at hu
      rw [hp] at hu
      have h1 := congrArg Url.path hu
      rw [hp] at h1
      simp only [Path.opaque.injEq] at h1
      have h2 := congrArg String.toList h1
      simp only [String.toList_append, List.append_right_eq_self] at h2
      exact hne h2
    obtain ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo,
      huo, hpwo, hqo, hfo, hpao, htr, hoh, hie', hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc',
      haa, hab, hhc, hnf, hpoa, hfsc⟩ := h
    simp only [hu]
    exact ⟨hov, hta, hbv, hbc, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => hso rfl, fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      hpo, huo, hpwo, hqo, hfo, hpao, fun o hp => absurd hp (hlist o),
      fun _ hp => absurd hp (hlist ""), fun _ => getLast?_cons_ne hie,
      fun _ => hbe rfl, fun h => absurd h (by decide), hdo, htne, fun h => absurd h (by decide),
      hsh, hhi, hnl, henc', fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
  · obtain ⟨hov, hta, hbv, hbc, hbnf, hbse, hse, hso, hsb, hhn, hpn, hcn, hpnil, hqn, hfn, hpo,
      huo, hpwo, hqo, hfo, hpao, htr, hoh, hie', hbe, hpb, hdo, htne, hhs, hsh, hhi, hnl, henc',
      haa, hab, hhc, hnf, hpoa, hfsc⟩ := h
    have hsp : ({ ctx.url with path := Path.opaque (o ++ add) } : Url).isSpecial
        = ctx.url.isSpecial := rfl
    simp only [hu]
    refine ⟨hov, hta, hbv, hbc, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => hso rfl, fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      hpo, huo, hpwo, hqo, hfo, ?_, ?_, ?_, fun _ => getLast?_cons_ne hie,
      fun _ => hbe rfl, fun h => absurd h (by decide), rfl, fun _ hp => by simp at hp,
      fun h => absurd h (by decide), hsh, hhi, hnl, henc', fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    · -- path の条件
      rw [hsp]
      rw [hp] at hpao
      simp only [pathCanon, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        encodedWith_append, String.toList_append, List.all_append, List.all_eq_true,
        bne_iff_ne] at hpao ⊢
      refine ⟨⟨⟨hpao.1.1, henc⟩, hpao.1.2, fun c hc => hqh c hc⟩, ?_⟩
      cases ho : o.toList with
      | cons x t => rw [ho] at hpao; simpa using hpao.2
      | nil =>
        simp only [List.nil_append]
        intro hh
        have hc := hhead hh
        subst hc
        have hoe : o = "" := by simpa using ho
        exact hoh rfl (by rw [hp, hoe]) rfl
    · -- 末尾の space
      intro o' hp' hl
      simp only [Path.opaque.injEq] at hp'
      subst hp'
      refine ⟨rfl, ?_⟩
      simp only [String.toList_append] at hl
      rw [List.getLast?_append] at hl
      cases hA : add.toList.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hA) hne
      | some x =>
        rw [hA] at hl
        simp only [Option.some_or, Option.some.injEq] at hl
        subst hl
        exact hlast hA
    · intro _ hp'
      simp only [Path.opaque.injEq] at hp'
      have := congrArg String.toList hp'
      simp only [String.toList_append] at this
      exact absurd (List.append_eq_nil_iff.mp this).2 hne

theorem utf8EncodeChar_ne_nil (c : Char) : utf8EncodeChar c ≠ [] := by
  unfold utf8EncodeChar
  simp only
  repeat' split
  all_goals simp

/-- 一文字を encode した結果は空でない。 -/
theorem encChar_ne_nil (set : Char → Bool) (c : Char) : (encChar set c).toList ≠ [] := by
  unfold encChar utf8PercentEncode
  simp only [String.toList_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  split
  · cases h : utf8EncodeChar c with
    | nil => exact absurd h (utf8EncodeChar_ne_nil c)
    | cons b rest => simp [percentEncodeByte]
  · simp

/-- opaque path state が `?` でも `#` でも space でもない文字を encode して積む。 -/
theorem CInv.opaqueEnc {base : Option Url} {input rest : List Char} {ch : Char} {ctx : PCtx}
    (h : CInv base .opaquePath input ctx) (hin : input = ch :: rest)
    (hs : ¬ch = ' ') (hq : ¬ch = '?') (hh : ¬ch = '#') :
    CInv base .opaquePath rest { ctx with url := appendOpaque ctx.url (encChar c0ControlSet ch) } := by
  refine h.opaqueAppend hin (encodedWith_encChar_c0 ch) ?_ (encChar_ne_nil _ ch) ?_ ?_
  · intro c hc
    exact ⟨encChar_avoid (by decide) (by decide) hq c hc, encChar_avoid (by decide) (by decide) hh c hc⟩
  · intro hd
    apply Classical.byContradiction
    intro hne
    have hm := List.mem_of_mem_head? hd
    exact encChar_avoid (by decide) (by decide) hne '/' hm rfl
  · intro hl
    have hm := List.mem_of_getLast? hl
    exact absurd rfl (encChar_avoid (by decide) (by decide) hs ' ' hm)

/-- opaque path state が space を `%20` にして積む（次が `?` か `#` のとき）。 -/
theorem CInv.opaquePct {base : Option Url} {input rest : List Char} {ctx : PCtx}
    (h : CInv base .opaquePath input ctx) (hin : input = ' ' :: rest) :
    CInv base .opaquePath rest { ctx with url := appendOpaque ctx.url "%20" } :=
  h.opaqueAppend hin (by decide) (by decide) (by decide) (by decide)
    (fun hl => absurd hl (by decide))

/-- opaque path state が space をそのまま積む（次が `?` でも `#` でもないとき）。 -/
theorem CInv.opaqueSpace {base : Option Url} {input rest : List Char} {ctx : PCtx}
    (h : CInv base .opaquePath input ctx) (hin : input = ' ' :: rest)
    (hq : ¬rest.head? = some '?') (hh : ¬rest.head? = some '#') :
    CInv base .opaquePath rest { ctx with url := appendOpaque ctx.url " " } := by
  refine h.opaqueAppend hin (by decide) (by decide) (by decide) (by decide) ?_
  intro _
  have hie := h.inputEnd rfl
  rw [hin] at hie
  cases rest with
  | nil => simp at hie
  | cons c t =>
    refine ⟨c, t, rfl, ?_, ?_⟩
    · intro he; subst he; exact hq rfl
    · intro he; subst he; exact hh rfl

end Url
