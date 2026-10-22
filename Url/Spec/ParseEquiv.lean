import Url.Spec.Parse

/-!
# basic URL parser と関数的な仕様の一致（§4.4、base 無し・special でない scheme）

`specParse`（`Url/Spec/Parse.lean`）は入力を成分に切り分けてから正規化する。parser は一文字ずつ
state を進める。ここで両者が全入力で一致することを示す（`basicUrlParse_eq_specParse`）。

証明は parser の state ごとに「この成分を読み切ると何を書くか」を積む。

* query と fragment の尾部は、どの state から入っても同じに読まれる（`run_qfTail`）。
* opaque path state は片を c0 control percent-encode set で encode しながら積む（`run_opaque_hier`）。
* authority state は最後の `@` までを userinfo として畳む（`run_authority_read`）。二つ目以降の `@` の前に
  足す `%40` は、`@` そのものを userinfo set で encode したものと同じである（`userinfoFold_at`）。
* host state は bracket の外の最初の `:` で止まる（`run_host_read`）。
-/

namespace Url.Spec

open Infra Url

/-! ## query と fragment の尾部 -/

/-- 参照の尾部。query があれば `?` と query、fragment があれば `#` と fragment。 -/
def qfTail (q f : Option (List Char)) : List Char :=
  (q.map ('?' :: ·)).getD [] ++ (f.map ('#' :: ·)).getD []

/-- **参照は hier-part と尾部に分かれる。** hier-part に `?` も `#` も無く、query に `#` は無い。 -/
theorem splitRef_decomp (l : List Char) :
    l = (splitRef l).1 ++ qfTail (splitRef l).2.1 (splitRef l).2.2 ∧
      '?' ∉ (splitRef l).1 ∧ '#' ∉ (splitRef l).1 ∧
      (∀ q, (splitRef l).2.1 = some q → '#' ∉ q) := by
  rcases first_occurrence '#' l with hnh | ⟨a, f, rfl, hnh⟩
  · rcases first_occurrence '?' l with hnq | ⟨h, q, rfl, hnq⟩
    · simp only [splitRef, splitFirst_of_not_mem _ _ hnh, splitFirst_of_not_mem _ _ hnq]
      simp [qfTail, hnq, hnh]
    · simp only [splitRef, splitFirst_of_not_mem _ _ hnh, splitFirst_append _ _ _ hnq]
      refine ⟨by simp [qfTail], hnq, fun hm => hnh (by simp [hm]), ?_⟩
      rintro q' ⟨⟩ hm; exact hnh (by simp [hm])
  · rcases first_occurrence '?' a with hnq | ⟨h, q, rfl, hnq⟩
    · simp only [splitRef, splitFirst_append _ _ _ hnh, splitFirst_of_not_mem _ _ hnq]
      simp [qfTail, hnq, hnh]
    · simp only [splitRef, splitFirst_append _ _ _ hnh, splitFirst_append _ _ _ hnq]
      refine ⟨by simp [qfTail], hnq, fun hm => hnh (by simp [hm]), ?_⟩
      rintro q' ⟨⟩ hm; exact hnh (by simp [hm])

/-- `?` でも `#` でもない文字を前に足しても、尾部の分け方は変わらない。 -/
theorem splitRef_cons {c : Char} (hq : c ≠ '?') (hh : c ≠ '#') (l : List Char) :
    splitRef (c :: l) = (c :: (splitRef l).1, (splitRef l).2) := by
  simp [splitRef, splitFirst, hq, hh]

/--
**query と fragment の尾部は、どの state から入っても同じに読まれる。**

state `S` が入力の終わりで url をそのまま返し、`?` で query state へ、`#` で fragment state へ
渡すなら、尾部を読み切った結果は参照の query と fragment を encode したものになる。
-/
theorem run_qfTail (base : Option Url) (S : PState) (q f : Option (List Char)) (ctx : PCtx)
    (hov : ctx.over = none) (hbuf : ctx.buffer = []) (hq0 : ctx.url.query = none)
    (hf0 : ctx.url.fragment = none) (hqh : ∀ x, q = some x → '#' ∉ x)
    (hE : run base S [] ctx = .ok ctx.url)
    (hQ : ∀ r, run base S ('?' :: r) ctx
      = run base .query r { ctx with url := { ctx.url with query := some "" } })
    (hH : ∀ r, run base S ('#' :: r) ctx
      = run base .fragment r { ctx with url := { ctx.url with fragment := some "" } }) :
    run base S (qfTail q f) ctx
      = .ok { ctx.url with query := q.map (queryText ctx.url.isSpecial),
                           fragment := f.map fragmentText } := by
  cases q with
  | none =>
    cases f with
    | none =>
      simp only [qfTail, Option.map_none, Option.getD_none, List.nil_append, hE]
      congr 1
      cases hu : ctx.url
      simp only [hu] at hq0 hf0
      simp [hq0, hf0]
    | some f =>
      simp only [qfTail, Option.map_none, Option.getD_none, List.nil_append, Option.map_some,
        Option.getD_some]
      rw [hH, Spec.run_fragment base f _ "" rfl]
      simp [hq0]
  | some q =>
    have hnq := hqh q rfl
    cases f with
    | none =>
      simp only [qfTail, Option.map_some, Option.getD_some, Option.map_none, Option.getD_none,
        List.append_nil]
      rw [hQ, Spec.run_query base q _ (fun c hc e => hnq (e ▸ hc))]
      simp [queryOf, queryText, hbuf, hf0, Url.isSpecial]
      rfl
    | some f =>
      simp only [qfTail, Option.map_some, Option.getD_some, List.cons_append]
      rw [hQ, run_query_until_hash base q f _ (by exact hov) hnq, Spec.run_fragment base f _ "" rfl]
      simp [queryOf, queryText, hbuf, Url.isSpecial]
      rfl

/-! ## opaque path -/

/-- opaque path state の space。次が `?` か `#` なら `%20`、そうでなければそのまま。 -/
theorem run_opaque_space (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .opaquePath (' ' :: rest) ctx
      = run base .opaquePath rest
          { ctx with
            url := appendOpaque ctx.url
                     (match rest.head? with | some '?' => "%20" | some '#' => "%20" | _ => " ") } := by
  rw [run, step]
  rfl

/-- opaque path state のそれ以外の文字。c0 control percent-encode set で encode して積む。 -/
theorem run_opaque_char (base : Option Url) {c : Char} (rest : List Char) (ctx : PCtx)
    (hq : c ≠ '?') (hh : c ≠ '#') (hs : c ≠ ' ') :
    run base .opaquePath (c :: rest) ctx
      = run base .opaquePath rest
          { ctx with url := appendOpaque ctx.url (encChar c0ControlSet c) } := by
  rw [run, step]
  · exact hq
  · exact hh
  · exact hs

theorem encChar_space : encChar c0ControlSet ' ' = " " := by decide

theorem opaqueText_nil (b : Bool) : opaqueText [] b = "" := by
  cases b <;> rfl

/-- 最後でない文字は、そのまま encode して前に付く。 -/
theorem opaqueText_cons (c : Char) {h : List Char} (hne : h ≠ []) (b : Bool) :
    opaqueText (c :: h) b = encChar c0ControlSet c ++ opaqueText h b := by
  have hl : (c :: h).getLast? = h.getLast? := by
    cases h with
    | nil => exact absurd rfl hne
    | cons d t => simp [List.getLast?_cons]
  have hd : (c :: h).dropLast = c :: h.dropLast := by
    cases h with
    | nil => exact absurd rfl hne
    | cons d t => rfl
  unfold opaqueText
  rw [hl, hd]
  split
  · simp [encChar, utf8PercentEncode, String.append_assoc]
  · simp [encChar, utf8PercentEncode]

/-- 一文字だけの opaque path。終わった後に query か fragment が続き、その文字が space なら `%20`。 -/
theorem opaqueText_single (c : Char) (b : Bool) :
    opaqueText [c] b = if b && c == ' ' then "%20" else encChar c0ControlSet c := by
  unfold opaqueText
  by_cases hb : (b && c == ' ') = true
  · rw [if_pos (by simpa using hb), if_pos hb]
    simp [utf8PercentEncode]
  · rw [if_neg (by simpa using hb), if_neg hb]
    rfl

/--
**opaque path state は hier-part を `opaqueText` で積む。**

`T` は hier-part の後ろで、空か `?` か `#` で始まる。
-/
theorem run_opaque_hier (base : Option Url) : ∀ (hier T : List Char) (ctx : PCtx) (o : String),
    ctx.url.path = .opaque o → '?' ∉ hier → '#' ∉ hier →
    (T = [] ∨ T.head? = some '?' ∨ T.head? = some '#') →
    run base .opaquePath (hier ++ T) ctx
      = run base .opaquePath T
          { ctx with url := { ctx.url with path := .opaque (o ++ opaqueText hier !T.isEmpty) } } := by
  intro hier
  induction hier with
  | nil =>
    intro T ctx o hp _ _ _
    simp only [List.nil_append, opaqueText_nil, String.append_empty, ← hp]
  | cons c h ih =>
    intro T ctx o hp hq hh hT
    have hcq : c ≠ '?' := fun e => hq (by simp [e])
    have hch : c ≠ '#' := fun e => hh (by simp [e])
    have hq' : '?' ∉ h := fun hm => hq (by simp [hm])
    have hh' : '#' ∉ h := fun hm => hh (by simp [hm])
    have happ : ∀ s, appendOpaque ctx.url s = { ctx.url with path := .opaque (o ++ s) } := by
      intro s; unfold appendOpaque; rw [hp]
    by_cases hs : c = ' '
    · subst hs
      rw [List.cons_append, run_opaque_space, happ]
      rw [ih T _ _ rfl hq' hh' hT]
      cases h with
      | nil =>
        rcases hT with rfl | hT | hT
        · simp [opaqueText_single, opaqueText_nil, encChar_space]
        · obtain ⟨r, rfl⟩ : ∃ r, T = '?' :: r := by
            cases T with
            | nil => simp at hT
            | cons x r => simp at hT; exact ⟨r, by rw [hT]⟩
          simp [opaqueText_single, opaqueText_nil]
        · obtain ⟨r, rfl⟩ : ∃ r, T = '#' :: r := by
            cases T with
            | nil => simp at hT
            | cons x r => simp at hT; exact ⟨r, by rw [hT]⟩
          simp [opaqueText_single, opaqueText_nil]
      | cons d t =>
        have hdq : d ≠ '?' := fun e => hq' (by simp [e])
        have hdh : d ≠ '#' := fun e => hh' (by simp [e])
        rw [opaqueText_cons ' ' (List.cons_ne_nil d t), encChar_space]
        simp [hdq, hdh, String.append_assoc]
    · rw [List.cons_append, run_opaque_char base _ ctx hcq hch hs, happ]
      rw [ih T _ _ rfl hq' hh' hT]
      cases h with
      | nil =>
        simp [opaqueText_single, opaqueText_nil, hs]
      | cons d t =>
        rw [opaqueText_cons c (List.cons_ne_nil d t)]
        simp [String.append_assoc]

/-! ## 最後の `@` -/

theorem splitLast_nil (d : Char) : splitLast d [] = (none, []) := rfl

/-- 区切りでない文字を後ろに足すと、後ろの片が伸びる。 -/
theorem splitLast_snoc_ne {d c : Char} (hc : c ≠ d) (l : List Char) :
    splitLast d (l ++ [c]) = ((splitLast d l).1, (splitLast d l).2 ++ [c]) := by
  unfold splitLast
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, splitFirst, hc, if_false]
  cases splitFirst d l.reverse with
  | mk a r =>
    cases r with
    | none => simp
    | some x => simp

/-- 区切りを後ろに足すと、それが最後の区切りになる。 -/
theorem splitLast_snoc_eq (d : Char) (l : List Char) : splitLast d (l ++ [d]) = (some l, []) := by
  unfold splitLast
  simp [splitFirst]

/-- 区切りが無ければ、後ろの片は全体である。 -/
theorem splitLast_none {d : Char} {l y : List Char} (h : splitLast d l = (none, y)) : y = l := by
  unfold splitLast at h
  split at h
  · simp at h
  · simp at h; exact h.symm

/-- `splitFirst` が分けたなら、最初の区切りの前後に戻すと元に戻る。 -/
theorem splitFirst_eq_some {d : Char} {l a r : List Char} (h : splitFirst d l = (a, some r)) :
    l = a ++ d :: r ∧ d ∉ a := by
  rcases first_occurrence d l with hn | ⟨a', r', rfl, hn⟩
  · rw [splitFirst_of_not_mem d l hn] at h; simp at h
  · rw [splitFirst_append d a' r' hn] at h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hn⟩

/-- 最後の区切りの前後に戻すと元に戻る。 -/
theorem splitLast_some {d : Char} {l x y : List Char} (h : splitLast d l = (some x, y)) :
    l = x ++ d :: y := by
  unfold splitLast at h
  split at h
  · next a r he =>
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨he2, -⟩ := splitFirst_eq_some he
    have := congrArg List.reverse he2
    simpa using this
  · simp at h

/-! ## userinfo の畳み込み -/

/-- 文字ごとの encode を並べたものは、列を一度に encode したものである。 -/
theorem encChar_fold (set : Char → Bool) : ∀ (x : List Char) (s : String),
    x.foldl (fun acc c => acc ++ encChar set c) s = s ++ String.ofList (utf8PercentEncode set x)
  | [], s => by simp [utf8PercentEncode]
  | c :: x, s => by
    rw [List.foldl_cons, encChar_fold set x]
    simp [encChar, utf8PercentEncode, String.append_assoc, ← String.ofList_append]

/-- password token を見た後は、残りはすべて password に encode して足される。 -/
theorem userinfoFold_true : ∀ (x : List Char) (u : Url),
    x.foldl userinfoStep (u, true)
      = ({ u with password := u.password ++ String.ofList (utf8PercentEncode userinfoSet x) }, true)
  | [], u => by simp [utf8PercentEncode]
  | c :: x, u => by
    rw [List.foldl_cons]
    have : userinfoStep (u, true) c
        = ({ u with password := u.password ++ encChar userinfoSet c }, true) := by
      simp [userinfoStep]
    rw [this, userinfoFold_true x]
    simp [encChar, utf8PercentEncode, String.append_assoc, ← String.ofList_append]

/--
**userinfo は最初の `:` で username と password に分かれ、どちらも userinfo set で encode される。**
-/
theorem userinfoFold_false : ∀ (x : List Char) (u : Url),
    x.foldl userinfoStep (u, false)
      = ({ u with username := u.username ++ String.ofList (utf8PercentEncode userinfoSet (splitFirst ':' x).1),
                  password := u.password ++ String.ofList (utf8PercentEncode userinfoSet ((splitFirst ':' x).2.getD [])) },
         (splitFirst ':' x).2.isSome)
  | [], u => by simp [splitFirst, utf8PercentEncode]
  | c :: x, u => by
    rw [List.foldl_cons]
    by_cases hc : c = ':'
    · subst hc
      have : userinfoStep (u, false) ':' = (u, true) := by simp [userinfoStep]
      rw [this, userinfoFold_true x]
      simp [splitFirst, utf8PercentEncode]
    · have : userinfoStep (u, false) c
          = ({ u with username := u.username ++ encChar userinfoSet c }, false) := by
        simp [userinfoStep, hc]
      rw [this, userinfoFold_false x]
      simp [splitFirst, hc, encChar, utf8PercentEncode, String.append_assoc, ← String.ofList_append]

/-- `@` を一文字読むのは、`%40` の三文字を読むのと同じである。 -/
theorem userinfoStep_at (a : Url × Bool) :
    userinfoStep a '@' = "%40".toList.foldl userinfoStep a := by
  obtain ⟨u, b⟩ := a
  cases b <;> simp [userinfoStep, encChar, utf8PercentEncode, String.append_assoc] <;> decide

/-! ## authority state -/

/--
authority state が `done` まで読んだときの状態。

最後の `@` より前は userinfo として畳まれ、後ろは buffer に残る。`@` が無ければ全部が buffer にある。
-/
def authCtx (ctx0 : PCtx) (done : List Char) : PCtx :=
  match splitLast '@' done with
  | (none, y) => { ctx0 with buffer := y }
  | (some x, y) =>
    { ctx0 with url := (x.foldl userinfoStep (ctx0.url, false)).1,
                passwordTokenSeen := (x.foldl userinfoStep (ctx0.url, false)).2,
                buffer := y, atSignSeen := true }

theorem authCtx_of_none {ctx0 : PCtx} {done y : List Char} (hs : splitLast '@' done = (none, y)) :
    authCtx ctx0 done = { ctx0 with buffer := y } := by
  unfold authCtx; rw [hs]

theorem authCtx_of_some {ctx0 : PCtx} {done x y : List Char}
    (hs : splitLast '@' done = (some x, y)) :
    authCtx ctx0 done
      = { ctx0 with url := (x.foldl userinfoStep (ctx0.url, false)).1,
                    passwordTokenSeen := (x.foldl userinfoStep (ctx0.url, false)).2,
                    buffer := y, atSignSeen := true } := by
  unfold authCtx; rw [hs]

/-- authority state の `@`。 -/
theorem run_authority_at (base : Option Url) (rest : List Char) (ctx0 : PCtx) (done : List Char)
    (ha0 : ctx0.atSignSeen = false) (hp0 : ctx0.passwordTokenSeen = false) :
    run base .authority ('@' :: rest) (authCtx ctx0 done)
      = run base .authority rest (authCtx ctx0 (done ++ ['@'])) := by
  rw [authCtx_of_some (splitLast_snoc_eq '@' done)]
  rcases hs : splitLast '@' done with ⟨_ | x, y⟩
  · have hy := splitLast_none hs
    subst hy
    rw [authCtx_of_none hs, run, step]
    simp [ha0, hp0]
  · have hd := splitLast_some hs
    rw [authCtx_of_some hs, run, step]
    simp only [beq_self_eq_true, if_true]
    have key : List.foldl userinfoStep (ctx0.url, false) (x ++ '@' :: y)
        = List.foldl userinfoStep
            (List.foldl userinfoStep (List.foldl userinfoStep (ctx0.url, false) x) "%40".toList) y := by
      rw [List.foldl_append, List.foldl_cons, userinfoStep_at]
    rw [hd, key, List.foldl_append]

/-- authority state の区切りでない文字。buffer に積む。 -/
theorem run_authority_char (base : Option Url) {c : Char} (rest : List Char) (ctx0 : PCtx)
    (done : List Char) (hc : c ≠ '@') (ht : isTerminator ctx0.url.isSpecial (some c) = false) :
    run base .authority (c :: rest) (authCtx ctx0 done)
      = run base .authority rest (authCtx ctx0 (done ++ [c])) := by
  have hsn := splitLast_snoc_ne hc done
  rcases hs : splitLast '@' done with ⟨_ | x, y⟩
  · rw [hs] at hsn
    rw [authCtx_of_none hs, authCtx_of_none hsn, run, step]
    simp only [beq_iff_eq, hc, if_false]
    rw [if_neg (by simpa using ht)]
  · rw [hs] at hsn
    rw [authCtx_of_some hs, authCtx_of_some hsn, run, step]
    simp only [beq_iff_eq, hc, if_false]
    have hsch : (x.foldl userinfoStep (ctx0.url, false)).1.isSpecial = ctx0.url.isSpecial := by
      rw [userinfoFold_false]; rfl
    rw [hsch, if_neg (by simpa using ht)]

/-- **authority state は区切りまでを読み、最後の `@` より前を userinfo として畳む。** -/
theorem run_authority_read (base : Option Url) (ctx0 : PCtx)
    (ha0 : ctx0.atSignSeen = false) (hp0 : ctx0.passwordTokenSeen = false) :
    ∀ (auth T done : List Char), (∀ c ∈ auth, isTerminator ctx0.url.isSpecial (some c) = false) →
    run base .authority (auth ++ T) (authCtx ctx0 done)
      = run base .authority T (authCtx ctx0 (done ++ auth)) := by
  intro auth
  induction auth with
  | nil => intro T done _; simp
  | cons c auth ih =>
    intro T done h
    rw [List.cons_append]
    by_cases hc : c = '@'
    · subst hc
      rw [run_authority_at base _ ctx0 done ha0 hp0, ih T _ (fun x hx => h x (by simp [hx]))]
      simp
    · rw [run_authority_char base _ ctx0 done hc (h c (by simp)), ih T _ (fun x hx => h x (by simp [hx]))]
      simp

/-- authority state の終わり。`@` の後に何も無ければ失敗し、そうでなければ buffer を host state に読み直させる。 -/
theorem run_authority_end (base : Option Url) (T : List Char) (ctx : PCtx)
    (hT : ∀ c r, T = c :: r → isTerminator ctx.url.isSpecial (some c) = true) :
    run base .authority T ctx
      = if ctx.atSignSeen && ctx.buffer.isEmpty then fail ctx
        else run base .host (ctx.buffer ++ T) { ctx with buffer := [] } := by
  cases T with
  | nil => rw [run, step]
  | cons c r =>
    have ht := hT c r rfl
    have hc : c ≠ '@' := fun e => by subst e; simp [isTerminator] at ht
    rw [run, step]
    simp only [beq_iff_eq, hc, if_false, ht, if_true]

/-! ## host state -/

/-- host state が文字を読んだ後の、bracket の中にいるかどうか。 -/
def bracketsAfter (inside : Bool) : List Char → Bool
  | [] => inside
  | c :: t => bracketsAfter (if c == '[' then true else if c == ']' then false else inside) t

/--
**host state は bracket の外の最初の `:` まで buffer に積む。** `:` は読まずに残す。
`:` が無ければ、区切りまで積む。
-/
theorem run_host_read (base : Option Url) : ∀ (hp T : List Char) (ctx : PCtx),
    ctx.over = none → (∀ c ∈ hp, isTerminator ctx.url.isSpecial (some c) = false) →
    run base .host (hp ++ T) ctx
      = match splitHostPort ctx.insideBrackets hp with
        | (h, none) => run base .host T
            { ctx with buffer := ctx.buffer ++ h, insideBrackets := bracketsAfter ctx.insideBrackets h }
        | (h, some p) => run base .host (':' :: (p ++ T))
            { ctx with buffer := ctx.buffer ++ h, insideBrackets := false } := by
  intro hp
  induction hp with
  | nil => intro T ctx _ _; simp [splitHostPort, bracketsAfter]
  | cons c hp ih =>
    intro T ctx hov h
    have ht := h c (by simp)
    by_cases hcol : (c == ':' && !ctx.insideBrackets) = true
    · have hs : splitHostPort ctx.insideBrackets (c :: hp) = ([], some hp) := by
        simp only [splitHostPort, hcol, if_true]
      rw [hs]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcol
      obtain ⟨rfl, hib⟩ := hcol
      cases ctx
      simp_all
    · have hs : splitHostPort ctx.insideBrackets (c :: hp)
          = (c :: (splitHostPort (if c == '[' then true else if c == ']' then false
                else ctx.insideBrackets) hp).1,
             (splitHostPort (if c == '[' then true else if c == ']' then false
                else ctx.insideBrackets) hp).2) := by
        simp only [splitHostPort, hcol, Bool.false_eq_true, if_false]
      rw [hs, List.cons_append, run, step]
      rw [if_neg (by simp [hov]), if_neg (by simpa using hcol), if_neg (by simp [ht])]
      refine Eq.trans (ih T _ hov (fun x hx => h x (by simp [hx]))) ?_
      cases splitHostPort (if c == '[' then true else if c == ']' then false else ctx.insideBrackets) hp with
      | mk hh pp =>
        cases pp with
        | none => simp [bracketsAfter, List.append_assoc]
        | some p => simp [List.append_assoc]

/-- host state の bracket の外の `:`。host を確定させて port state へ。 -/
theorem run_host_colon (base : Option Url) (r : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hib : ctx.insideBrackets = false) :
    run base .host (':' :: r) ctx
      = if ctx.buffer.isEmpty then .failure
        else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
          | none => .failure
          | some h => run base .port r { ctx with url := { ctx.url with host := some h }, buffer := [] } := by
  rw [run, step, if_neg (by simp [hov]), if_pos (by simp [hib])]
  by_cases hb : ctx.buffer.isEmpty = true
  · rw [if_pos hb, if_pos hb]; simp [fail, hov]
  · rw [if_neg hb, if_neg hb, if_neg (by simp [hov])]
    cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, hov]

/-- host state の区切り。host を確定させて path start state へ。 -/
theorem run_host_term (base : Option Url) (T : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hT : ∀ c r, T = c :: r → isTerminator ctx.url.isSpecial (some c) = true ∧ c ≠ ':') :
    run base .host T ctx
      = if ctx.url.isSpecial && ctx.buffer.isEmpty then .failure
        else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
          | none => .failure
          | some h => run base .pathStart T { ctx with url := { ctx.url with host := some h }, buffer := [] } := by
  cases T with
  | nil =>
    rw [run, step, if_neg (by simp [hov]), if_neg (by simp), if_pos (by rfl)]
    by_cases hb : (ctx.url.isSpecial && ctx.buffer.isEmpty) = true
    · rw [if_pos hb, if_pos hb]; simp [fail, hov]
    · rw [if_neg hb, if_neg hb, if_neg (by simp [hov])]
      cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, hov]
  | cons c r =>
    obtain ⟨hterm, hncol⟩ := hT c r rfl
    rw [run, step, if_neg (by simp [hov]), if_neg (by simp [hncol]), if_pos hterm]
    by_cases hb : (ctx.url.isSpecial && ctx.buffer.isEmpty) = true
    · rw [if_pos hb, if_pos hb]; simp [fail, hov]
    · rw [if_neg hb, if_neg hb, if_neg (by simp [hov])]
      cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, hov]

/-! ## port state -/

/-- port state は数字を積み、区切りでも数字でもない文字が来れば失敗する。 -/
theorem run_port_digits (base : Option Url) : ∀ (p T : List Char) (ctx : PCtx),
    ctx.over = none → (∀ c ∈ p, isTerminator ctx.url.isSpecial (some c) = false) →
    run base .port (p ++ T) ctx
      = if p.all isAsciiDigit then run base .port T { ctx with buffer := ctx.buffer ++ p }
        else .failure := by
  intro p
  induction p with
  | nil => intro T ctx _ _; simp
  | cons c p ih =>
    intro T ctx hov h
    rw [List.cons_append, run, step]
    by_cases hd : isAsciiDigit c = true
    · rw [if_pos hd, ih T]
      · simp [hd, List.append_assoc]
      · exact hov
      · exact fun x hx => h x (by simp [hx])
    · rw [if_neg hd, if_neg (by simp [h c (by simp), hov])]
      simp [hd, fail, hov]

/-- port state の区切り。積んだ数字を port にして path start state へ。 -/
theorem run_port_end (base : Option Url) (T : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hT : ∀ c r, T = c :: r → isTerminator ctx.url.isSpecial (some c) = true) :
    run base .port T ctx
      = match portDone ctx with
        | none => .failure
        | some ctx2 => run base .pathStart T ctx2 := by
  cases T with
  | nil =>
    rw [run, step]
    cases portDone ctx <;> simp [fail, hov]
  | cons c r =>
    have ht := hT c r rfl
    have hd : isAsciiDigit c = false := by
      cases hdc : isAsciiDigit c
      · rfl
      · exfalso
        simp only [isTerminator, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at ht
        rcases ht with ((h | h) | h) | ⟨_, h⟩ <;> subst h <;> simp [isAsciiDigit] at hdc
    rw [run, step, if_neg (by simp [hd]), if_pos (by simp [ht])]
    cases portDone ctx <;> simp [fail, hov]

/-- **port state は、数字だけなら値を port にし（既定 port なら null）、範囲外か数字でない文字があれば失敗する。** -/
theorem run_port_read (base : Option Url) (p T : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hbuf : ctx.buffer = []) (hport : ctx.url.port = none)
    (hp : ∀ c ∈ p, isTerminator ctx.url.isSpecial (some c) = false)
    (hT : ∀ c r, T = c :: r → isTerminator ctx.url.isSpecial (some c) = true) :
    run base .port (p ++ T) ctx
      = match specPort ctx.url.scheme (some p) with
        | none => .failure
        | some port => run base .pathStart T
            { ctx with url := { ctx.url with port := port }, buffer := [] } := by
  rw [run_port_digits base p T ctx hov hp]
  by_cases hd : p.all isAsciiDigit = true
  · rw [if_pos hd, run_port_end base T]
    rotate_left
    · exact hov
    · exact hT
    simp only [specPort, hd, if_true, hbuf, List.nil_append]
    by_cases he : p.isEmpty = true
    · have : p = [] := by simpa using he
      subst this
      simp only [portDone, List.isEmpty_nil, if_true, if_true]
      congr 2
      cases hu : ctx.url
      simp only [hu] at hport
      simp [hport]
    · rw [if_neg he]
      simp only [portDone, he, Bool.false_eq_true, if_false, ← decimalOf_eq_portValue]
      by_cases hv : decimalOf p < 65536
      · rw [if_neg (by omega), if_pos hv]
        simp [portSet, portOf]
      · rw [if_pos (by omega), if_neg hv]
  · rw [if_neg hd]
    simp [specPort, hd]

/-! ## path start state と path or authority state（special でない URL） -/

theorem run_pathStart_slash (base : Option Url) (r : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) :
    run base .pathStart ('/' :: r) ctx = run base .path r ctx := by
  rw [run, step]; simp [hsp]

/-- path start state から尾部を読み切る（special でない URL、path は空のまま）。 -/
theorem run_pathStart_qfTail (base : Option Url) (q f : Option (List Char)) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq0 : ctx.url.query = none) (hf0 : ctx.url.fragment = none)
    (hqh : ∀ x, q = some x → '#' ∉ x) :
    run base .pathStart (qfTail q f) ctx
      = .ok { ctx.url with query := q.map (queryText false), fragment := f.map fragmentText } := by
  rw [run_qfTail base .pathStart q f ctx hov hbuf hq0 hf0 hqh, hsp]
  · rw [run, step]; simp [hsp, hov]
  · intro r; rw [run, step]; simp [hsp, hov]
  · intro r; rw [run, step]; simp [hsp, hov]

theorem run_pathOrAuthority_slash (base : Option Url) (r : List Char) (ctx : PCtx) :
    run base .pathOrAuthority ('/' :: r) ctx = run base .authority r ctx := by
  rw [run, step]; simp

theorem run_pathOrAuthority_path (base : Option Url) (r : List Char) (ctx : PCtx)
    (h : ∀ t, r ≠ '/' :: t) :
    run base .pathOrAuthority r ctx = run base .path r ctx := by
  cases r with
  | nil => rw [run, step]; simp
  | cons c t =>
    have hc : c ≠ '/' := fun e => h t (by rw [e])
    rw [run, step]; simp [hc]

/-! ## scheme -/

theorem schemeChar_eq_isSchemeTail : schemeChar = isSchemeTail := rfl

/-- **`splitScheme` が scheme を返すなら、入力は scheme の文字の並びと `:` で始まる。** -/
theorem splitScheme_some {l rest : List Char} {s : String} (h : splitScheme l = some (s, rest)) :
    ∃ a pre, l = a :: (pre ++ ':' :: rest) ∧ isAsciiAlpha a = true ∧
      (∀ c ∈ pre, schemeChar c = true) ∧ s = String.ofList ((a :: pre).map asciiLowerChar) := by
  cases l with
  | nil => simp [splitScheme] at h
  | cons a r =>
    simp only [splitScheme] at h
    by_cases ha : isAsciiAlpha a = true
    · rw [if_pos ha] at h
      split at h
      · next r' hd =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨a, r.takeWhile isSchemeTail, ?_, ha, ?_, rfl⟩
        · conv => lhs; rw [← List.takeWhile_append_dropWhile (p := isSchemeTail) (l := r)]
          rw [hd]
        · intro c hc
          exact List.all_eq_true.mp List.all_takeWhile c hc
      · simp at h
    · rw [if_neg ha] at h; simp at h

/-- **scheme が無いことは `HasScheme` の否定である。** -/
theorem splitScheme_none_iff (l : List Char) : splitScheme l = none ↔ ¬ HasScheme l := by
  constructor
  · intro h ⟨a, pre, tail, he, ha, hpre⟩
    subst he
    have hdw : (pre ++ ':' :: tail).dropWhile isSchemeTail = ':' :: tail := by
      rw [List.dropWhile_append_of_pos (fun c hc => by simpa using List.all_eq_true.mp hpre c hc)]
      simp [show isSchemeTail ':' = false by decide]
    simp [splitScheme, ha, hdw] at h
  · intro h
    cases hs : splitScheme l with
    | none => rfl
    | some p =>
      obtain ⟨s, rest⟩ := p
      obtain ⟨a, pre, he, ha, hpre, -⟩ := splitScheme_some hs
      exact absurd ⟨a, pre, rest, he, ha, List.all_eq_true.mpr (fun c hc => hpre c hc)⟩ h

/-! ## 組み立て -/

/-- parser の結果としての仕様の結果。仕様の `none` は parser の失敗に当たる。 -/
def toResult : Option Url → PResult
  | some u => .ok u
  | none => .failure

/-- 尾部が空でないのは、query か fragment があるときである。 -/
theorem qfTail_isEmpty (q f : Option (List Char)) :
    (qfTail q f).isEmpty = !(q.isSome || f.isSome) := by
  cases q <;> cases f <;> simp [qfTail]

/-- 尾部は空か、`?` か `#` で始まる。 -/
theorem qfTail_head (q f : Option (List Char)) :
    qfTail q f = [] ∨ (qfTail q f).head? = some '?' ∨ (qfTail q f).head? = some '#' := by
  cases q <;> cases f <;> simp [qfTail]

/-- hier-part と尾部を並べたものは、その通りに分かれる。 -/
theorem splitRef_parts {h : List Char} {q f : Option (List Char)} (hq : '?' ∉ h) (hh : '#' ∉ h)
    (hqh : ∀ x, q = some x → '#' ∉ x) : splitRef (h ++ qfTail q f) = (h, q, f) := by
  cases q with
  | none =>
    cases f with
    | none => simp [qfTail, splitRef, splitFirst_of_not_mem _ _ hh, splitFirst_of_not_mem _ _ hq]
    | some f => simp [qfTail, splitRef, splitFirst_append _ _ _ hh, splitFirst_of_not_mem _ _ hq]
  | some q =>
    have hnq := hqh q rfl
    cases f with
    | none =>
      simp [qfTail, splitRef, splitFirst_of_not_mem '#' (h ++ '?' :: q) (by simp [hh, hnq]),
        splitFirst_append '?' h q hq]
    | some f =>
      have e : h ++ ('?' :: q ++ '#' :: f) = (h ++ '?' :: q) ++ '#' :: f := by simp
      simp only [qfTail, Option.map_some, Option.getD_some, splitRef, e]
      rw [splitFirst_append '#' _ _ (by simp [hh, hnq])]
      simp [splitFirst_append '?' h q hq]

/-- 区切りの文字を含まない片は、special でない URL の terminator を含まない。 -/
theorem isTerminator_ns {c : Char} (h1 : c ≠ '/') (h2 : c ≠ '?') (h3 : c ≠ '#') :
    isTerminator false (some c) = false := by
  simp [isTerminator, h1, h2, h3]

theorem isSpecial_ns {s : String} (hns : isSpecialScheme s = false) :
    ({ scheme := s } : Url).isSpecial = false := hns

theorem ne_file_of_ns {s : String} (hns : isSpecialScheme s = false) : (s == "file") = false := by
  cases h : (s == "file")
  · rfl
  · simp at h; subst h; simp [isSpecialScheme] at hns

/-- **opaque path の分岐。** -/
theorem branch_opaque (base : Option Url) (t : List Char → Option String) (s : String)
    (hns : isSpecialScheme s = false) (rest : List Char) (hr : ∀ x, rest ≠ '/' :: x) :
    run base .opaquePath rest { url := { scheme := s, path := .opaque "" }, toAscii := t }
      = toResult (specParseNonSpecial t s rest) := by
  obtain ⟨hdec, hnq, hnh, hqh⟩ := splitRef_decomp rest
  have hspec : specParseNonSpecial t s rest
      = some { scheme := s, path := .opaque (opaqueText (splitRef rest).1
                 ((splitRef rest).2.1.isSome || (splitRef rest).2.2.isSome)),
               query := (splitRef rest).2.1.map (queryText false),
               fragment := (splitRef rest).2.2.map fragmentText } := by
    dsimp only [specParseNonSpecial]
    generalize hh : (splitRef rest).1 = hier at hdec ⊢
    split
    · next ap => rw [hdec] at hr; exact absurd rfl (hr _)
    · next pp _ => rw [hdec] at hr; exact absurd rfl (hr _)
    · rfl
  rw [hspec]
  conv => lhs; rw [hdec]
  rw [run_opaque_hier base _ _ _ "" rfl hnq hnh (qfTail_head _ _)]
  rw [run_qfTail base .opaquePath _ _ _ rfl rfl rfl rfl hqh]
  · simp [toResult, qfTail_isEmpty, Url.isSpecial, hns]
  · rw [run, step]
  · intro r; rw [run, step]
  · intro r; rw [run, step]

/-- **path だけの分岐**（`sc:/a/b`）。 -/
theorem branch_path (base : Option Url) (t : List Char → Option String) (s : String)
    (hns : isSpecialScheme s = false) (r2 : List Char) (hr : ∀ x, r2 ≠ '/' :: x) :
    run base .pathOrAuthority r2 { url := { scheme := s }, toAscii := t }
      = toResult (specParseNonSpecial t s ('/' :: r2)) := by
  have hspec : specParseNonSpecial t s ('/' :: r2)
      = some { scheme := s, path := .list (pathFrom false (some (splitRef r2).1)),
               query := (splitRef r2).2.1.map (queryText false),
               fragment := (splitRef r2).2.2.map fragmentText } := by
    obtain ⟨hdec, -⟩ := splitRef_decomp r2
    dsimp only [specParseNonSpecial]
    rw [splitRef_cons (by decide) (by decide)]
    dsimp only
    generalize hh : (splitRef r2).1 = h2 at hdec ⊢
    split
    · next ap he =>
      simp only [List.cons.injEq, true_and] at he
      subst he
      exact absurd hdec (hr _)
    · next pp _ he =>
      simp only [List.cons.injEq, true_and] at he
      rw [he]
    · next _ hn2 => exact (hn2 h2 rfl).elim
  rw [hspec, run_pathOrAuthority_path base r2 _ hr]
  rw [run_path_ref base r2 _ (P := []) rfl rfl rfl rfl rfl]
  simp [toResult, pathFrom, Url.isSpecial, hns, ne_file_of_ns hns]

/-! ### authority の分岐 -/

/-- path start state から先の続きが、path・query・fragment をこう書くということ。 -/
def PathStartCont (base : Option Url) (T1 : List Char) (P : List String)
    (Q F : Option String) : Prop :=
  ∀ ctx' : PCtx, ctx'.over = none → ctx'.buffer = [] → ctx'.url.query = none →
    ctx'.url.fragment = none → ctx'.url.path = .list [] → ctx'.url.isSpecial = false →
    run base .pathStart T1 ctx' = .ok { ctx'.url with path := .list P, query := Q, fragment := F }

/-- host と port に分けたなら、`:` を挟んで並べると元に戻る。 -/
theorem splitHostPort_some : ∀ {ib : Bool} {hp h p : List Char},
    splitHostPort ib hp = (h, some p) → hp = h ++ ':' :: p
  | _, [], _, _, he => by simp [splitHostPort] at he
  | ib, c :: t, h, p, he => by
    unfold splitHostPort at he
    split at he
    · next hc =>
      simp only [Prod.mk.injEq, Option.some.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp [hc.1]
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, he2⟩ := he
      have := splitHostPort_some (Prod.ext rfl he2)
      exact congrArg (c :: ·) this

/-- 仕様の host と port の部分。 -/
def hostResult (t : List Char → Option String) (u : Url) (hp : List Char) (P : List String)
    (Q F : Option String) : Option Url :=
  if (splitHostPort false hp).1.isEmpty && (splitHostPort false hp).2.isSome then none
  else
    match hostParser t (splitHostPort false hp).1 true, specPort u.scheme (splitHostPort false hp).2 with
    | some host, some port =>
      some { u with host := some host, port, path := .list P, query := Q, fragment := F }
    | _, _ => none

/-- **host state から先**。host と port を読み、path start state の続きへ渡す。 -/
theorem host_flow (base : Option Url) (hp T1 : List Char) (ctxH : PCtx) {P : List String}
    {Q F : Option String}
    (hov : ctxH.over = none) (hbuf : ctxH.buffer = []) (hib : ctxH.insideBrackets = false)
    (hsp : ctxH.url.isSpecial = false) (hport : ctxH.url.port = none)
    (hq0 : ctxH.url.query = none) (hf0 : ctxH.url.fragment = none) (hpath : ctxH.url.path = .list [])
    (hhp : ∀ c ∈ hp, c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#')
    (hT1 : ∀ c r, T1 = c :: r → c = '/' ∨ c = '?' ∨ c = '#')
    (hcont : PathStartCont base T1 P Q F) :
    run base .host (hp ++ T1) ctxH = toResult (hostResult ctxH.toAscii ctxH.url hp P Q F) := by
  have hterm : ∀ c ∈ hp, isTerminator ctxH.url.isSpecial (some c) = false := by
    intro c hc; rw [hsp]; obtain ⟨h1, h2, h3⟩ := hhp c hc; exact isTerminator_ns h1 h2 h3
  have hT1t : ∀ sp c r, T1 = c :: r → isTerminator sp (some c) = true := by
    intro sp c r he
    rcases hT1 c r he with rfl | rfl | rfl <;> simp [isTerminator]
  rw [run_host_read base hp T1 ctxH hov hterm, hib]
  unfold hostResult
  rcases hsplit : splitHostPort false hp with ⟨h, _ | p⟩
  · -- `:` が無い：host だけ。
    simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
    rw [run_host_term base T1 _ (by exact hov) (fun c r he => ⟨hT1t _ c r he, by
      rcases hT1 c r he with rfl | rfl | rfl <;> decide⟩)]
    simp only [hsp, Bool.false_and, Bool.false_eq_true, if_false, Bool.not_false, hbuf,
      List.nil_append]
    cases hostParser ctxH.toAscii h true with
    | none => rfl
    | some host =>
      simp only [specPort]
      rw [hcont _ (by exact hov) rfl (by exact hq0) (by exact hf0) (by exact hpath) (by exact hsp)]
      simp [toResult, ← hport]
  · -- `:` がある：host と port。
    simp only [Option.isSome_some, Bool.and_true]
    rw [run_host_colon base _ _ (by exact hov) rfl]
    simp only [hbuf, List.nil_append]
    by_cases he : h.isEmpty = true
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]
      simp only [hsp, Bool.not_false]
      cases hostParser ctxH.toAscii h true with
      | none => rfl
      | some host =>
        simp only
        have hpp : ∀ c ∈ p, isTerminator false (some c) = false := by
          intro c hc
          have : c ∈ hp := by
            rw [splitHostPort_some hsplit]; simp [hc]
          obtain ⟨h1, h2, h3⟩ := hhp c this; exact isTerminator_ns h1 h2 h3
        rw [run_port_read base p T1 _ (by exact hov) rfl (by exact hport) (by rw [show ({ ctxH.url with host := some host } : Url).isSpecial = false from hsp]; exact hpp)
          (by intro c r he; exact hT1t _ c r he)]
        simp only
        cases specPort ctxH.url.scheme (some p) with
        | none => rfl
        | some port =>
          simp only
          rw [hcont _ (by exact hov) rfl (by exact hq0) (by exact hf0) (by exact hpath) (by exact hsp)]
          rfl

/-- 仕様の authority の部分。最後の `@` で userinfo と host-port に分ける。 -/
def authResult (t : List Char → Option String) (s : String) (auth : List Char) (P : List String)
    (Q F : Option String) : Option Url :=
  if (splitLast '@' auth).1.isSome && (splitLast '@' auth).2.isEmpty then none
  else hostResult t { scheme := s, username := (userinfoParts (splitLast '@' auth).1).1,
                                   password := (userinfoParts (splitLast '@' auth).1).2 }
         (splitLast '@' auth).2 P Q F

/-- 最後の `@` の後ろは authority の一部である。 -/
theorem mem_of_splitLast {auth y : List Char} {o : Option (List Char)} (hs : splitLast '@' auth = (o, y))
    {c : Char} (hc : c ∈ y) : c ∈ auth := by
  cases o with
  | none => rw [← splitLast_none hs]; exact hc
  | some x => rw [splitLast_some hs]; simp [hc]

/-- **authority state から先。** userinfo を畳み、host state に読み直させる。 -/
theorem authority_flow (base : Option Url) (t : List Char → Option String) (s : String)
    (hns : isSpecialScheme s = false) (auth T1 : List Char) {P : List String} {Q F : Option String}
    (hauth : ∀ c ∈ auth, c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#')
    (hT1 : ∀ c r, T1 = c :: r → c = '/' ∨ c = '?' ∨ c = '#')
    (hcont : PathStartCont base T1 P Q F) :
    run base .authority (auth ++ T1) { url := { scheme := s }, toAscii := t }
      = toResult (authResult t s auth P Q F) := by
  have h0 : ({ url := { scheme := s }, toAscii := t } : PCtx)
      = authCtx { url := { scheme := s }, toAscii := t } [] := by
    rw [authCtx_of_none (splitLast_nil '@')]
  have hterm : ∀ c ∈ auth, isTerminator ({ scheme := s } : Url).isSpecial (some c) = false := by
    intro c hc; rw [isSpecial_ns hns]; obtain ⟨h1, h2, h3⟩ := hauth c hc; exact isTerminator_ns h1 h2 h3
  rw [h0, run_authority_read base _ rfl rfl auth T1 [] hterm, List.nil_append]
  unfold authResult
  rcases hs : splitLast '@' auth with ⟨_ | x, y⟩
  · have hy := splitLast_none hs
    subst hy
    rw [authCtx_of_none hs, run_authority_end]
    · simp only [Bool.false_and, Bool.false_eq_true, if_false, Option.isSome_none]
      exact host_flow base y T1 _ rfl rfl rfl (isSpecial_ns hns) rfl rfl rfl rfl hauth hT1 hcont
    · intro c r he; rcases hT1 c r he with rfl | rfl | rfl <;> simp [isTerminator]
  · rw [authCtx_of_some hs, run_authority_end]
    · simp only [Bool.true_and, Option.isSome_some]
      by_cases hy : y.isEmpty = true
      · rw [if_pos hy, if_pos hy]; simp [fail, toResult]
      · rw [if_neg hy, if_neg hy]
        rw [userinfoFold_false]
        refine host_flow base y T1 _ rfl rfl rfl (isSpecial_ns hns) rfl rfl rfl rfl
          (fun c hc => hauth c (mem_of_splitLast hs hc)) hT1 hcont
    · intro c r he; rcases hT1 c r he with rfl | rfl | rfl <;> simp [isTerminator]

theorem ne_file_of_isSpecial {u : Url} (h : u.isSpecial = false) : (u.scheme == "file") = false := by
  cases hf : (u.scheme == "file")
  · rfl
  · simp at hf; simp [Url.isSpecial, hf, isSpecialScheme] at h

/-- path が無い authority の続き（`sc://h`、`sc://h?q`）。 -/
theorem pathStartCont_none (base : Option Url) (q f : Option (List Char))
    (hqh : ∀ x, q = some x → '#' ∉ x) :
    PathStartCont base (qfTail q f) [] (q.map (queryText false)) (f.map fragmentText) := by
  intro ctx' hov hbuf hq0 hf0 hpath hsp
  rw [run_pathStart_qfTail base q f ctx' hsp hov hbuf hq0 hf0 hqh, ← hpath]

/-- path がある authority の続き（`sc://h/p`）。 -/
theorem pathStartCont_some (base : Option Url) (pp : List Char) (q f : Option (List Char))
    (hq : '?' ∉ pp) (hh : '#' ∉ pp) (hqh : ∀ x, q = some x → '#' ∉ x) :
    PathStartCont base ('/' :: (pp ++ qfTail q f)) (pathFrom false (some pp))
      (q.map (queryText false)) (f.map fragmentText) := by
  intro ctx' hov hbuf hq0 hf0 hpath hsp
  rw [run_pathStart_slash base _ ctx' hsp, run_path_ref base _ ctx' hpath hov hbuf hq0 hf0,
    splitRef_parts hq hh hqh, hsp, ne_file_of_isSpecial hsp]
  rfl

/-- **authority の分岐**（`sc://u@h:p/a?q#f`）。 -/
theorem branch_authority (base : Option Url) (t : List Char → Option String) (s : String)
    (hns : isSpecialScheme s = false) (r3 : List Char) :
    run base .authority r3 { url := { scheme := s }, toAscii := t }
      = toResult (specParseNonSpecial t s ('/' :: '/' :: r3)) := by
  obtain ⟨hdec, hnq, hnh, hqh⟩ := splitRef_decomp r3
  have hspec : specParseNonSpecial t s ('/' :: '/' :: r3)
      = authResult t s (splitFirst '/' (splitRef r3).1).1
          (pathFrom false (splitFirst '/' (splitRef r3).1).2)
          ((splitRef r3).2.1.map (queryText false)) ((splitRef r3).2.2.map fragmentText) := by
    dsimp only [specParseNonSpecial]
    rw [splitRef_cons (by decide) (by decide), splitRef_cons (by decide) (by decide)]
    rfl
  rw [hspec]
  generalize (splitRef r3).1 = ap at hdec hnq hnh hspec
  generalize (splitRef r3).2.1 = q at hdec hqh hspec
  generalize (splitRef r3).2.2 = f at hdec hspec
  subst hdec
  rcases first_occurrence '/' ap with hns' | ⟨auth, pp, rfl, hna⟩
  · rw [splitFirst_of_not_mem _ _ hns']
    exact authority_flow base t s hns ap (qfTail q f)
      (fun c hc => ⟨fun e => hns' (e ▸ hc), fun e => hnq (e ▸ hc), fun e => hnh (e ▸ hc)⟩)
      (fun c r he => by
        rcases qfTail_head q f with h | h | h <;> rw [he] at h <;> simp_all)
      (pathStartCont_none base q f hqh)
  · rw [splitFirst_append _ _ _ hna, List.append_assoc, List.cons_append]
    exact authority_flow base t s hns auth _
      (fun c hc => ⟨fun e => hna (e ▸ hc), fun e => hnq (by subst e; simp [hc]),
        fun e => hnh (by subst e; simp [hc])⟩)
      (fun c r he => by simp at he; exact Or.inl he.1.symm)
      (pathStartCont_some base pp q f (fun hm => hnq (by simp [hm]))
        (fun hm => hnh (by simp [hm])) hqh)

/-! ## 入口 -/

/-- scheme state が special でない scheme を読み終えたときの行き先。 -/
theorem run_schemeStart_nonSpecial (base : Option Url) (t : List Char → Option String)
    {a : Char} {pre rest : List Char} (ha : isAsciiAlpha a = true)
    (hpre : ∀ c ∈ pre, schemeChar c = true)
    (hns : isSpecialScheme (String.ofList ((a :: pre).map asciiLowerChar)) = false) :
    run base .schemeStart (a :: (pre ++ ':' :: rest)) { url := {}, toAscii := t }
      = match rest with
        | '/' :: r2 => run base .pathOrAuthority r2
            { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar) }, toAscii := t }
        | _ => run base .opaquePath rest
            { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar), path := .opaque "" },
              toAscii := t } := by
  rw [run, step, if_pos ha, run_scheme_prefix base pre _ _ hpre]
  rw [run, step]
  have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
    decide
  have hns' : isSpecialScheme (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar)) = false := by
    simpa using hns
  have hnf : (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) == "file") = false := by
    cases hf : (String.ofList (asciiLowerChar a :: pre.map asciiLowerChar) == "file")
    · rfl
    · rw [beq_iff_eq.mp hf] at hns'; simp [isSpecialScheme] at hns'
  simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
    List.cons_append, hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
    Option.isSome_none, Url.isSpecial, hns', hnf, Bool.false_and]
  rfl

/--
**special でない scheme を持つ入力について、basic URL parser は関数的な仕様と一致する**（base 無し）。

`state` を一つずつ進める parser と、入力を成分に切り分けてから正規化する `specParseNonSpecial` が、
入力に制限を付けずに同じ結果（失敗を含む）を返す。
-/
theorem run_spec_nonSpecial (base : Option Url) (t : List Char → Option String)
    {l rest : List Char} {s : String} (hs : splitScheme l = some (s, rest))
    (hns : isSpecialScheme s = false) :
    run base .schemeStart l { url := {}, toAscii := t } = toResult (specParseNonSpecial t s rest) := by
  obtain ⟨a, pre, rfl, ha, hpre, rfl⟩ := splitScheme_some hs
  rw [run_schemeStart_nonSpecial base t ha hpre hns]
  cases rest with
  | nil => exact branch_opaque base t _ hns [] (fun x h => by cases h)
  | cons c r =>
    by_cases hc : c = '/'
    · subst hc
      by_cases hr : ∃ r3, r = '/' :: r3
      · obtain ⟨r3, rfl⟩ := hr
        simp only
        rw [run_pathOrAuthority_slash, branch_authority base t _ hns r3]
      · have hr' : ∀ x, r ≠ '/' :: x := fun x he => hr ⟨x, he⟩
        simp only
        exact branch_path base t _ hns r hr'
    · have : (match c :: r with
          | '/' :: r2 => run base .pathOrAuthority r2
              { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar) }, toAscii := t }
          | _ => run base .opaquePath (c :: r)
              { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar), path := .opaque "" },
                toAscii := t })
          = run base .opaquePath (c :: r)
              { url := { scheme := String.ofList ((a :: pre).map asciiLowerChar), path := .opaque "" },
                toAscii := t } := by
        split
        · next r2 he => simp at he; exact absurd he.1 hc
        · rfl
      rw [this]
      exact branch_opaque base t _ hns (c :: r) (fun x he => hc (List.cons.inj he).1)

/--
**basic URL parser は、base 無しの入力について関数的な仕様と一致する。**

前提は「入力に scheme があるなら special でない」だけで、scheme が無い入力（失敗する）も含む。
-/
theorem basicUrlParse_eq_specParse (t : List Char → Option String) (input : String)
    (h : ∀ s rest, splitScheme (preprocess input) = some (s, rest) → isSpecialScheme s = false) :
    basicUrlParse input none t = specParse t (preprocess input) := by
  cases hs : splitScheme (preprocess input) with
  | none =>
    rw [basicUrlParse_eq_none_of_not_hasScheme ((splitScheme_none_iff _).mp hs)]
    simp [specParse, hs]
  | some p =>
    obtain ⟨sc, rest⟩ := p
    have hns := h sc rest hs
    unfold basicUrlParse
    rw [run_spec_nonSpecial none t hs hns]
    have hnf : sc ≠ "file" := fun e => by subst e; simp [isSpecialScheme] at hns
    simp only [specParse, hs, hns, hnf, Bool.false_eq_true, if_false]
    cases specParseNonSpecial t sc rest <;> rfl

end Url.Spec
