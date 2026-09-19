import Url.Roundtrip.Canonical

/-!
# query と fragment の往復
-/

namespace Url

open Infra

/-! ## query と fragment

どちらも終端の state で、opaque path state からも path state からも来る。
-/

/-- set に入らない文字だけなら、1 文字ずつの percent-encode は何もしない。 -/
theorem encFold_id {set : Char → Bool} : ∀ (l : List Char), (∀ c ∈ l, set c = false) →
    l.flatMap (fun c => (encChar set c).toList) = l
  | [], _ => rfl
  | d :: rest, h => by
    have hc : encChar set d = String.ofList [d] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact h _ (by simp))]
    simp only [List.flatMap_cons, hc, String.toList_ofList, List.singleton_append]
    rw [encFold_id rest (fun x hx => h x (by simp [hx]))]

/-- fragment state は、素通しの文字をそのまま fragment の末尾に足す。 -/
theorem run_fragment_plain (base : Option Url) (l : List Char) (ctx : PCtx) (f : String)
    (hf : ctx.url.fragment = some f) (h : ∀ c ∈ l, fragmentSet c = false) :
    run base .fragment l ctx = .ok { ctx.url with fragment := some (f ++ String.ofList l) } := by
  obtain ⟨u, hu⟩ := run_fragment_ok base l ctx
  rw [hu]
  rw [run_fragment_spec base l ctx u (by rw [hf]; rfl) hu]
  rw [encFold_id l h, hf]
  rfl

/-- override が無い query state は、`#` までの文字を buffer に積んで `queryOf` を書く。 -/
theorem run_query_plain (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    ctx.over = none → (∀ c ∈ l, ¬c = '#') →
    run base .query l ctx = .ok { ctx.url with query := some (queryOf { ctx with buffer := ctx.buffer ++ l }) } := by
  intro l
  induction l with
  | nil => intro ctx _ _; rw [run, step]; simp
  | cons c tail ih =>
    intro ctx hov h
    have hc : ¬c = '#' := h c (by simp)
    rw [run, step]
    simp +zetaDelta only []
    rw [ih { ctx with buffer := ctx.buffer ++ [c] } hov (fun x hx => h x (by simp [hx]))]
    all_goals first
      | exact hc
      | (simp; done)

/-- query state は `#` でない文字を buffer に積む。 -/
theorem run_query_chunk (base : Option Url) : ∀ (l tail : List Char) (ctx : PCtx),
    (∀ c ∈ l, ¬c = '#') →
    run base .query (l ++ tail) ctx
      = run base .query tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _; simp
  | cons c rest ih =>
    intro tail ctx h
    have hc : ¬c = '#' := h c (by simp)
    simp only [List.cons_append]
    rw [run, step]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } (fun x hx => h x (by simp [hx]))]
    all_goals first
      | exact hc
      | (simp; done)

/-- query state の終わり。buffer を percent-encode して query に書く。 -/
theorem run_query_eof (base : Option Url) (ctx : PCtx) :
    run base .query [] ctx = .ok { ctx.url with query := some (queryOf ctx) } := by
  rw [run, step]

/-- query state の `#`。query を確定させて fragment state へ渡す。 -/
theorem run_query_hash (base : Option Url) (rest : List Char) (ctx : PCtx) (hov : ctx.over = none) :
    run base .query ('#' :: rest) ctx
      = run base .fragment rest
          { ctx with
            url := { ctx.url with query := some (queryOf ctx), fragment := some "" }
            buffer := [] } := by
  rw [run, step]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]

/-- opaque path state の `?`。query state へ渡す。 -/
theorem run_opaquePath_question (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .opaquePath ('?' :: rest) ctx
      = run base .query rest { ctx with url := { ctx.url with query := some "" } } := by
  rw [run, step]

/-- opaque path state の `#`。fragment state へ渡す。 -/
theorem run_opaquePath_hash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .opaquePath ('#' :: rest) ctx
      = run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } } := by
  rw [run, step]

/-- opaque path state の終わり。 -/
theorem run_opaquePath_eof (base : Option Url) (ctx : PCtx) :
    run base .opaquePath [] ctx = .ok ctx.url := by
  rw [run, step]

/-- serializer が query と fragment を並べる分。 -/
def qfList (q f : Option String) : List Char :=
  (match q with | none => [] | some s => '?' :: s.toList) ++
    (match f with | none => [] | some s => '#' :: s.toList)

/-- query も fragment も無い URL は、その二つを `none` と書き直しても同じものである。 -/
theorem url_qf_eta {u : Url} (hq : u.query = none) (hf : u.fragment = none) :
    ({ u with query := none, fragment := none } : Url) = u := by
  cases u
  simp_all

/-- buffer をそのまま query にできるとき、`queryOf` はその文字列を返す。 -/
theorem queryOf_encoded {ctx : PCtx} {qs : String} (hq : ctx.url.query = some "")
    (hb : ctx.buffer = qs.toList)
    (h : ∀ c ∈ qs.toList, (if ctx.url.isSpecial then specialQuerySet else querySet) c = false) :
    queryOf ctx = qs := by
  unfold queryOf
  rw [hq, hb, utf8PercentEncode_id h, String.ofList_toList]
  simp

/--
opaque path state から先、query と fragment を読み切る。

query と fragment の有無の四通りをまとめて扱う。
-/
theorem run_opaquePath_qf (base : Option Url) (ctx : PCtx) (q f : Option String)
    (hov : ctx.over = none) (hbuf : ctx.buffer = [])
    (hq : ctx.url.query = none) (hf : ctx.url.fragment = none)
    (hqc : ∀ s, q = some s → ∀ c ∈ s.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ s, f = some s → ∀ c ∈ s.toList, fragmentSet c = false) :
    run base .opaquePath (qfList q f) ctx = .ok { ctx.url with query := q, fragment := f } := by
  unfold qfList
  cases q with
  | none =>
    cases f with
    | none =>
      simp only [List.append_nil]
      have h1 : ({ ctx.url with query := none, fragment := none } : Url)
          = { ctx.url with query := ctx.url.query, fragment := ctx.url.fragment } := by
        rw [hq, hf]
      rw [run_opaquePath_eof, h1]
    | some fs =>
      simp only [List.nil_append]
      rw [run_opaquePath_hash]
      rw [run_fragment_plain base fs.toList _ "" rfl (hfc fs rfl), ← hq]
      simp
  | some qs =>
    have hqs := hqc qs rfl
    have hqe : utf8PercentEncode (if ctx.url.isSpecial then specialQuerySet else querySet)
        qs.toList = qs.toList := utf8PercentEncode_id hqs
    cases f with
    | none =>
      simp only [List.append_nil]
      rw [run_opaquePath_question]
      rw [run_query_plain base qs.toList { ctx with url := { ctx.url with query := some "" } }
        hov (fun c hc => by
          intro he
          have h2 := hqs c hc
          rw [he] at h2
          revert h2
          cases ctx.url.isSpecial <;> decide)]
      rw [← hf]
      simp
      exact queryOf_encoded rfl (by simp [hbuf]) hqs
    | some fs =>
      simp only [List.cons_append]
      rw [run_opaquePath_question]
      rw [run_query_chunk base qs.toList ('#' :: fs.toList)
        { ctx with url := { ctx.url with query := some "" } } (fun c hc => by
          intro he
          have h2 := hqs c hc
          rw [he] at h2
          revert h2
          cases ctx.url.isSpecial <;> decide)]
      rw [run_query_hash base fs.toList
        { ctx with
          url := { ctx.url with query := some "" }
          buffer := ctx.buffer ++ qs.toList } hov]
      rw [run_fragment_plain base fs.toList _ "" rfl (hfc fs rfl)]
      simp
      exact queryOf_encoded rfl (by simp [hbuf]) hqs

/-- fragment state は fragment を読み切って返す。 -/
theorem run_fragment_full (base : Option Url) (fs : String) (ctx : PCtx)
    (hf : ctx.url.fragment = some "") (h : ∀ c ∈ fs.toList, fragmentSet c = false) :
    run base .fragment fs.toList ctx = .ok { ctx.url with fragment := some fs } := by
  rw [run_fragment_plain base fs.toList ctx "" hf h]
  simp

/--
query state は query を読み切り、`#` があれば fragment へ渡す。

`tail` を仮引数にしてあるのは、`match f with` の作る matcher が
仮定 `hfc` を巻き込んでしまい、そのままでは `rw` の対象に合わないためである。
-/
theorem run_query_full (base : Option Url) (qs : String) (f : Option String)
    (tail : List Char) (ctx : PCtx)
    (htail : tail = match f with | none => [] | some fs => '#' :: fs.toList)
    (hov : ctx.over = none) (hb : ctx.buffer = []) (hq : ctx.url.query = some "")
    (hf0 : ctx.url.fragment = none)
    (hqc : ∀ c ∈ qs.toList,
      (if ctx.url.isSpecial then specialQuerySet else querySet) c = false)
    (hfc : ∀ x, f = some x → ∀ c ∈ x.toList, fragmentSet c = false) :
    run base .query (qs.toList ++ tail) ctx
      = .ok { ctx.url with query := some qs, fragment := f } := by
  subst htail
  have hnh : ∀ c ∈ qs.toList, ¬c = '#' := by
    intro c hc
    have := hqc c hc
    intro he
    rw [he] at this
    cases hsx : ctx.url.isSpecial <;> rw [hsx] at this <;> revert this <;> decide
  have hqe : utf8PercentEncode (if ctx.url.isSpecial then specialQuerySet else querySet)
      qs.toList = qs.toList := utf8PercentEncode_id hqc
  cases f with
  | none =>
    simp only [List.append_nil]
    rw [run_query_plain base qs.toList ctx hov hnh]
    simp only [queryOf, hb, List.nil_append, hq, hqe, String.ofList_toList]
    rw [← hf0]
    simp
  | some fs =>
    rw [run_query_chunk base qs.toList ('#' :: fs.toList) ctx hnh]
    rw [run_query_hash base fs.toList { ctx with buffer := ctx.buffer ++ qs.toList } hov]
    rw [run_fragment_full base fs _ rfl (hfc fs rfl)]
    simp only [queryOf, hb, List.nil_append, hq, hqe, String.ofList_toList]
    simp

end Url
