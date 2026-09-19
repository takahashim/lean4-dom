import Url.Roundtrip.Ipv6Chars

/-!
# host state の走行
-/

namespace Url

open Infra

/-- bracket の中では `:` は port の区切りにならない。 -/
theorem run_host_inside (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.over = none → ctx.url.isSpecial = sp → ctx.insideBrackets = true →
    (∀ c ∈ l, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') →
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
    rw [if_neg (by simp [hib])]
    rw [if_neg (by simpa [hsp] using hc.1)]
    have hib2 : (if (c == '[') = true then true else if (c == ']') = true then false
        else ctx.insideBrackets) = true := by simp [hc.2.1, hc.2.2, hib]
    simp +zetaDelta only [hib2]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c], insideBrackets := true } hov hsp rfl
      (fun x hx => h x (by simp [hx]))]
    simp [← hib]

/-- `[` から `]` までを buffer に積む。IPv6 host はこの形である。 -/
theorem run_host_bracket (base : Option Url) (sp : Bool) (inner tail : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp) (hib : ctx.insideBrackets = false)
    (h : ∀ c ∈ inner, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']') :
    run base .host ('[' :: (inner ++ ']' :: tail)) ctx
      = run base .host tail { ctx with buffer := ctx.buffer ++ ('[' :: (inner ++ [']'])) } := by
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp)]
  rw [if_neg (by cases sp <;> simp [hsp, isTerminator])]
  simp +zetaDelta only [show ((if ('[' == '[') = true then true
      else if ('[' == ']') = true then false else ctx.insideBrackets)) = true from by simp]
  rw [run_host_inside base sp inner (']' :: tail)
    { ctx with buffer := ctx.buffer ++ ['['], insideBrackets := true } hov hsp rfl h]
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp)]
  rw [if_neg (by cases sp <;> simp [hsp, isTerminator])]
  simp +zetaDelta only [show ((if (']' == '[') = true then true
      else if (']' == ']') = true then false else true)) = false from by simp]
  simp [← hib]


/--
host を serialize した文字列が authority state と host state を素通りできること。

domain も opaque host も forbidden host code point を含まない。IPv6 host はそれを含むが、
`[` と `]` に囲まれていて、その中では `:` が port の区切りにならない。
-/
def hostReadable (sp : Bool) (hst : Host) : Prop :=
  (∀ c ∈ (hostSerializer hst).toList, isForbiddenHost c = false) ∨
    (∃ inner, (hostSerializer hst).toList = '[' :: (inner ++ [']']) ∧
      ∀ c ∈ inner, isTerminator sp (some c) = false ∧ ¬c = '[' ∧ ¬c = ']' ∧ ¬c = '@')

/-- host を serialize した文字は `@` でも区切りでもない。authority state を素通りする。 -/
theorem hostReadable_auth {sp : Bool} {hst : Host} (h : hostReadable sp hst) :
    ∀ c ∈ (hostSerializer hst).toList, ¬c = '@' ∧ isTerminator sp (some c) = false := by
  rcases h with h | ⟨inner, he, h⟩
  · exact fun c hc => ⟨(not_forbidden_host (h c hc)).1, (not_forbidden_host (h c hc)).2.2.2.2 sp⟩
  · intro c hc
    rw [he] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨by decide, by cases sp <;> decide⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨(h c hc).2.2.2, (h c hc).1⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        exact ⟨by decide, by cases sp <;> decide⟩

/-- host state は host を serialize した文字列をそのまま buffer に積む。 -/
theorem run_host_serialized (base : Option Url) (sp : Bool) (hst : Host) (tail : List Char)
    (ctx : PCtx) (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hib : ctx.insideBrackets = false) (hok : hostReadable sp hst) :
    run base .host ((hostSerializer hst).toList ++ tail) ctx
      = run base .host tail
          { ctx with buffer := ctx.buffer ++ (hostSerializer hst).toList } := by
  rcases hok with h | ⟨inner, he, h⟩
  · exact run_host_chunk base sp _ tail ctx hov hsp hib
      (fun c hc => ⟨(not_forbidden_host (h c hc)).2.1,
        (not_forbidden_host (h c hc)).2.2.2.2 sp,
        (not_forbidden_host (h c hc)).2.2.1,
        (not_forbidden_host (h c hc)).2.2.2.1⟩)
  · rw [he]
    rw [show ('[' :: (inner ++ [']'])) ++ tail = '[' :: (inner ++ ']' :: tail) from by simp]
    exact run_host_bracket base sp inner tail ctx hov hsp hib
      (fun c hc => ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2.1⟩)

/-- IPv6 host を serialize した文字列は、`[` と `]` に囲まれた 16 進と `:` だけである。 -/
theorem hostReadable_ipv6 (sp : Bool) (a : Ipv6) : hostReadable sp (.ipv6 a) := by
  refine Or.inr ⟨(ipv6Serializer a).toList, ?_, ?_⟩
  · simp [hostSerializer, String.toList_append]
  · intro c hc
    have h := ipv6Serializer_chars a c hc
    refine ⟨isTerminator_false ?_ ?_ ?_ (fun _ => ?_), ?_, ?_, ?_⟩ <;>
      (intro he; rw [he] at h; revert h; decide)

/-- IPv6 host を serialize した文字に C0 control も space も無い。 -/
theorem ipv6_no_c0 (a : Ipv6) :
    ∀ c ∈ (hostSerializer (.ipv6 a)).toList, isC0ControlOrSpace c = false := by
  intro c hc
  simp only [hostSerializer, String.toList_append] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rw [show ("[" : String).toList = ['['] from rfl] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; decide
    · have h := ipv6Serializer_chars a c hc
      simp only [isHexOrColon, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
      rcases h with (h | h) | rfl
      · omega
      · omega
      · decide
  · rw [show ("]" : String).toList = [']'] from rfl] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; decide


end Url
