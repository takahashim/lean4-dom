import Url.RoundtripPort

/-!
# authority の往復
-/

namespace Url

open Infra

/-! ## authority

`//` で始まる URL の経路。authority state が buffer を host state へ戻し、
host state が host parser を呼ぶ。credentials と port はまだ扱っていない。
-/

/-- path or authority state：`/` なら authority state へ。 -/
theorem run_pathOrAuthority_authority (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .pathOrAuthority ('/' :: rest) ctx = run base .authority rest ctx := by
  rw [run, step]
  simp

set_option linter.unnecessarySimpa false in
/--
authority state が `@` も区切りも無い文字列を読み切って host state へ渡す。

buffer は host state の入力の先頭に戻る。
-/
theorem run_authority_host (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → (ctx.atSignSeen = true → ctx.buffer ++ l ≠ []) →
    (∀ c ∈ l, ¬c = '@' ∧ isTerminator sp (some c) = false) →
    (∀ c ∈ tail.head?, isTerminator sp (some c) = true) →
    run base .authority (l ++ tail) ctx
      = run base .host (ctx.buffer ++ l ++ tail) { ctx with buffer := [] } := by
  intro l
  induction l with
  | nil =>
    intro tail ctx hsp has _ ht
    simp only [List.nil_append, List.append_nil]
    cases tail with
    | nil =>
      rw [run, step]
      rw [if_neg (by simpa using has)]
    | cons t ts =>
      have htt := ht t rfl
      have hat : ¬t = '@' := by
        intro he; rw [he] at htt; simp [isTerminator] at htt
      rw [run, step]
      simp only [hsp]
      rw [if_neg (by simpa using hat), if_pos (by simpa using htt),
        if_neg (by simpa using has)]
  | cons c l' ih =>
    intro tail ctx hsp has h ht
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    simp only [hsp]
    rw [if_neg (by simpa using hc.1), if_neg (by simpa using hc.2)]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (by simpa using has)
      (fun x hx => h x (by simp [hx])) ht]
    simp

/-- host state が区切りでも `:` でも bracket でもない文字を読み切る。override が無い側。 -/
theorem run_host_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.over = none → ctx.url.isSpecial = sp → ctx.insideBrackets = false →
    (∀ c ∈ l, ¬c = ':' ∧ isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') →
    run base .host (l ++ tail) ctx = run base .host tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _ _; simp
  | cons c l' ih =>
    intro tail ctx hov hsp hib h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp [hc.1])]
    rw [if_neg (by simpa [hsp] using hc.2.1)]
    have hib2 : (if (c == '[') = true then true else if (c == ']') = true then false
        else ctx.insideBrackets) = false := by simp [hc.2.2.1, hc.2.2.2, hib]
    simp +zetaDelta only [hib2]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c], insideBrackets := false } hov hsp rfl
      (fun x hx => h x (by simp [hx]))]
    simp [← hib]

/-- host state の区切り。buffer を host parser に渡して path start state へ移る。 -/
theorem run_host_pathStart (base : Option Url) (sp : Bool) (tail : List Char) (ctx : PCtx)
    (hst : Host) (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hne : sp = true → ctx.buffer ≠ [])
    (ht : ∀ c ∈ tail.head?, isTerminator sp (some c) = true ∧ ¬c = ':')
    (hp : hostParser ctx.toAscii ctx.buffer (!sp) = some hst) :
    run base .host tail ctx
      = run base .pathStart tail
          { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
  cases tail with
  | nil =>
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp)]
    rw [if_pos (by simp [isTerminator])]
    rw [if_neg (by simp [hsp]; intro h; exact hne h)]
    rw [if_neg (by simp [hov])]
    simp only [hsp, hp]
    rw [if_neg (by simp [hov])]
  | cons t ts =>
    have htt := ht t rfl
    rw [run, step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp [htt.2])]
    rw [if_pos (by simpa [hsp] using htt.1)]
    rw [if_neg (by simp [hsp]; intro h; exact hne h)]
    rw [if_neg (by simp [hov])]
    simp only [hsp, hp]
    rw [if_neg (by simp [hov])]

/-- path start state：非 special で override が無いとき、`/` を一つ落として path state へ。 -/
theorem run_pathStart_slash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp [hov])]
  simp

/-- path start state の終わり。override が無ければ path は空のまま。 -/
theorem run_pathStart_eof (base : Option Url) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart [] ctx = .ok ctx.url := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp [hov])]
  simp [hov]

/-- opaque host parser を通ったなら、入力に forbidden host code point は無い。 -/
theorem hostParser_opaque_no_forbidden {f : List Char → Option String} {input : List Char}
    {h : Host} (hb : ∀ c ∈ input.head?, ¬c = '[') (hp : hostParser f input true = some h) :
    input.any isForbiddenHost = false := by
  unfold hostParser at hp
  split at hp
  · exact absurd (hb '[' rfl) (by simp)
  · rw [if_pos rfl] at hp
    exact opaqueHostParser_no_forbidden hp

/-- forbidden host code point でなければ、host state も authority state も読み進む。 -/
theorem not_forbidden_host {c : Char} (h : isForbiddenHost c = false) :
    ¬c = '@' ∧ ¬c = ':' ∧ ¬c = '[' ∧ ¬c = ']' ∧ ∀ sp, isTerminator sp (some c) = false := by
  refine ⟨?_, ?_, ?_, ?_, fun sp => isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
    (intro he; rw [he] at h; revert h; decide)

/-- `/` を一つ落として path state へ。special かどうかに依らない。 -/
theorem run_pathStart_slash_any (base : Option Url) (sp : Bool) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none) :
    run base .pathStart ('/' :: rest) ctx = run base .path rest ctx := by
  cases sp with
  | true => exact run_pathStart_slash_special base rest ctx (by simpa using hsp)
  | false => exact run_pathStart_slash base rest ctx (by simpa using hsp) hov

/-- path start state の `?`：special でなければ query state へ移る。 -/
theorem run_pathStart_question (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('?' :: rest) ctx
      = run base .query rest { ctx with url := { ctx.url with query := some "" } } := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_pos (by simp [hov])]

/-- path start state の `#`：special でなければ fragment state へ移る。 -/
theorem run_pathStart_hash (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) :
    run base .pathStart ('#' :: rest) ctx
      = run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } } := by
  rw [run, step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp [hov])]
  rw [if_pos (by simp [hov])]

/-- path start state から、path が空のまま query と fragment を読み切る。 -/
theorem run_pathStart_qf (base : Option Url) (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) (hb : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .pathStart (qfList q f) ctx
      = .ok { ctx.url with query := q, fragment := f } := by
  cases q with
  | none =>
    cases f with
    | none =>
      simp only [qfList, List.append_nil]
      rw [run_pathStart_eof base ctx hsp hov, url_qf_eta hq0 hf0]
    | some fs =>
      simp only [qfList, List.nil_append]
      rw [run_pathStart_hash base fs.toList ctx hsp hov]
      rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
      rw [← hq0]
  | some qs =>
    simp only [qfList, List.cons_append]
    rw [run_pathStart_question base _ ctx hsp hov]
    rw [run_query_full base qs f _ _ ?g0 ?g1 ?g2 ?g3 ?g4 ?g5 ?g6]
    case g0 => rfl
    case g1 => simp [hov]
    case g2 => simp [hb]
    case g3 => rfl
    case g4 => simpa using hf0
    case g5 => exact hqc qs rfl
    case g6 => exact hfc

/-- path start state の終わり：special なら空の segment が一つ残る。 -/
theorem run_pathStart_eof_special (base : Option Url) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) :
    run base .pathStart [] ctx = run base .path [] ctx := by
  rw [run, step]
  rw [if_pos (by simp [hsp])]
  simp

/-- userinfo set に入らない文字は `@` でも `:` でも区切りでもない。 -/
theorem not_userinfoSet {c : Char} (h : userinfoSet c = false) :
    ¬c = '@' ∧ ¬c = ':' ∧ ∀ sp, isTerminator sp (some c) = false := by
  refine ⟨?_, ?_, fun sp => isTerminator_false ?_ ?_ ?_ (fun _ => ?_)⟩ <;>
    (intro he; rw [he] at h; revert h; decide)

/-- userinfo の畳み込みは、`:` の前を username に積む。 -/
theorem userinfoFold_user : ∀ (l : List Char) (u : Url),
    (∀ c ∈ l, userinfoSet c = false) →
    l.foldl userinfoStep (u, false)
      = ({ u with username := u.username ++ String.ofList l }, false)
  | [], u, _ => by simp
  | c :: rest, u, h => by
    have hc := h c (by simp)
    have henc : encChar userinfoSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc)]
    show (rest.foldl userinfoStep (userinfoStep (u, false) c)) = _
    have hstep : userinfoStep (u, false) c
        = ({ u with username := u.username ++ String.ofList [c] }, false) := by
      unfold userinfoStep
      rw [if_neg (by simp [(not_userinfoSet hc).2.1])]
      simp [henc]
    rw [hstep, userinfoFold_user rest _ (fun x hx => h x (by simp [hx]))]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- `:` の後ろは password に積む。 -/
theorem userinfoFold_pass : ∀ (l : List Char) (u : Url),
    (∀ c ∈ l, userinfoSet c = false) →
    l.foldl userinfoStep (u, true)
      = ({ u with password := u.password ++ String.ofList l }, true)
  | [], u, _ => by simp
  | c :: rest, u, h => by
    have hc := h c (by simp)
    have henc : encChar userinfoSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc)]
    show (rest.foldl userinfoStep (userinfoStep (u, true) c)) = _
    have hstep : userinfoStep (u, true) c
        = ({ u with password := u.password ++ String.ofList [c] }, true) := by
      unfold userinfoStep
      split
      · next he => simp at he
      · simp [henc]
    rw [hstep, userinfoFold_pass rest _ (fun x hx => h x (by simp [hx]))]
    simp
    rw [String.push_eq_append, String.append_assoc]

/-- `user:pass` の形の buffer は username と password に分かれる。 -/
theorem userinfoFold_split (u : Url) (user pass : List Char)
    (hu : ∀ c ∈ user, userinfoSet c = false) (hp : ∀ c ∈ pass, userinfoSet c = false) :
    (user ++ ':' :: pass).foldl userinfoStep (u, false)
      = ({ u with
            username := u.username ++ String.ofList user
            password := u.password ++ String.ofList pass }, true) := by
  rw [List.foldl_append, userinfoFold_user user u hu]
  show pass.foldl userinfoStep (userinfoStep _ ':') = _
  have hstep : userinfoStep
      ({ u with username := u.username ++ String.ofList user }, false) ':'
      = ({ u with username := u.username ++ String.ofList user }, true) := by
    unfold userinfoStep
    rw [if_pos (by simp)]
  rw [hstep, userinfoFold_pass pass _ hp]

/-- authority state が `@` でも区切りでもない文字を buffer に積む。 -/
theorem run_authority_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp →
    (∀ c ∈ l, ¬c = '@' ∧ isTerminator sp (some c) = false) →
    run base .authority (l ++ tail) ctx
      = run base .authority tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _; simp
  | cons c l' ih =>
    intro tail ctx hsp h
    have hc := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    simp only [hsp]
    rw [if_neg (by simpa using hc.1), if_neg (by simpa using hc.2)]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (fun x hx => h x (by simp [hx]))]
    simp

/-- authority state の `@`。buffer を credentials に振り分ける。 -/
theorem run_authority_at (base : Option Url) (rest : List Char) (ctx : PCtx)
    (has : ctx.atSignSeen = false) :
    run base .authority ('@' :: rest) ctx
      = run base .authority rest
          { ctx with
            url := (ctx.buffer.foldl userinfoStep (ctx.url, ctx.passwordTokenSeen)).1
            buffer := []
            atSignSeen := true
            passwordTokenSeen :=
              (ctx.buffer.foldl userinfoStep (ctx.url, ctx.passwordTokenSeen)).2 } := by
  rw [run, step]
  rw [if_pos (by simp)]
  simp only [has, Bool.false_eq_true, if_false]

/-- serializer が credentials を並べる分。 -/
def credChars (user pass : String) : List Char :=
  if user.isEmpty && pass.isEmpty then []
  else user.toList ++ (if pass.isEmpty then [] else ':' :: pass.toList) ++ ['@']

/-- path start state から先の path と query と fragment を読み切る。 -/
theorem run_pathStart_path (base : Option Url) (sp : Bool) (segs : List String)
    (q f : Option String) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = sp) (hov : ctx.over = none)
    (hpath : ctx.url.path = .list []) (hb : ctx.buffer = [])
    (hwd : ∀ x, segs.head? = some x → pathStepUrl.windowsDriveBuffer ctx.url x.toList = x.toList)
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hsegs : sp = true → segs ≠ [])
    (hall : ∀ x ∈ segs, (∀ c ∈ x.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot x.toList = false ∧ isDoubleDot x.toList = false)
    (hqc : ∀ x, q = some x → ∀ c ∈ x.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .pathStart (pathChars segs ++ qfList q f) ctx
      = .ok { ctx.url with path := .list segs, query := q, fragment := f } := by
  cases hseg : segs with
  | nil =>
    cases hspv : sp with
    | true => exact absurd hseg (hsegs hspv)
    | false =>
      rw [show pathChars [] = [] from rfl, List.nil_append]
      rw [run_pathStart_qf base q f ctx ?e1 hov hb hq0 hf0 hqc hfc]
      · rw [← hpath]
      case e1 => rw [hspv] at hsp; exact hsp
  | cons x t =>
    rw [show pathChars (x :: t) = '/' :: intercal (x :: t) from rfl, List.cons_append]
    rw [run_pathStart_slash_any base sp (intercal (x :: t) ++ qfList q f) _ ?s1 ?s2]
    case s1 => exact hsp
    case s2 => exact hov
    exact run_path_full base sp (x :: t) q f _ hsp hov hpath hb (by rw [← hseg]; exact hwd)
      hq0 hf0 (by simp) (by rw [← hseg]; exact hall) hqc hfc

/-- serializer が port を並べる分。 -/
def portChars : Option Nat → List Char
  | none => []
  | some p => ':' :: (toString p).toList

end Url
