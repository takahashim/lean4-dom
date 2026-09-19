import Url.Roundtrip.Chars

/-!
# path の往復
-/

namespace Url

open Infra

/-! ## path

host を持たない非 special な URL の経路。scheme state から path or authority state へ入る。
-/

/-- 区切りでないことを、文字ごとの条件から言う。 -/
theorem isTerminator_false {sp : Bool} {c : Char} (h1 : ¬c = '/') (h2 : ¬c = '?') (h3 : ¬c = '#')
    (h4 : sp = true → ¬c = '\\') : isTerminator sp (some c) = false := by
  simp only [isTerminator, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  cases sp with
  | false => simp
  | true => simp [h4 rfl]

/-- path state が区切りでない文字を読み切る。 -/
theorem run_path_chunk (base : Option Url) (sp : Bool) :
    ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → ctx.over = none →
    (∀ c ∈ l, pathSet c = false ∧ isTerminator sp (some c) = false) →
    run base .path (l ++ tail) ctx
      = run base .path tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _ _; simp
  | cons c rest ih =>
    intro tail ctx hsp hov h
    have hc := h c (by simp)
    have ht := hc.2
    simp only [isTerminator, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at ht
    have henc : encChar pathSet c = String.ofList [c] := by
      unfold encChar
      rw [utf8PercentEncode_id (by intro x hx; simp at hx; subst hx; exact hc.1)]
    simp only [List.cons_append]
    rw [run, step]
    rw [if_neg (by simp [hsp, ht.1.1.1, ht.1.1.2, ht.1.2, ht.2, hov])]
    rw [ih tail { ctx with buffer := ctx.buffer ++ (encChar pathSet c).toList } hsp hov
      (fun x hx => h x (by simp [hx]))]
    simp [henc]

/-- path state の `/`。segment を確定させて次へ進む。 -/
theorem run_path_slash (base : Option Url) (rest : List Char) (ctx : PCtx) :
    run base .path ('/' :: rest) ctx
      = run base .path rest
          { ctx with url := pathStepUrl ctx.url true ctx.buffer, buffer := [] } := by
  rw [run, step]
  simp

/-- path state の終わり。buffer を最後の segment にする。 -/
theorem run_path_eof (base : Option Url) (ctx : PCtx) :
    run base .path [] ctx = .ok (pathStepUrl ctx.url false ctx.buffer) := by
  rw [run, step]
  simp

/-- `file` でない URL では Windows drive letter の直しは何もしない。 -/
theorem windowsDriveBuffer_of_not_file {u : Url} {buf : List Char} (h : ¬u.scheme = "file") :
    pathStepUrl.windowsDriveBuffer u buf = buf := by
  unfold pathStepUrl.windowsDriveBuffer
  rw [if_neg (by simp [h])]

/-- path が空でなければ、先頭 segment ではないので直さない。 -/
theorem windowsDriveBuffer_of_path_ne {u : Url} {pre : List String} {buf : List Char}
    (hp : u.path = .list pre) (hne : pre ≠ []) :
    pathStepUrl.windowsDriveBuffer u buf = buf := by
  unfold pathStepUrl.windowsDriveBuffer
  refine if_neg ?_
  rw [hp]
  cases pre with
  | nil => exact absurd rfl hne
  | cons x t => simp

/-- すでに正規化された Windows drive letter は、直しても同じである。 -/
theorem windowsDriveBuffer_of_normalized {u : Url} {buf : List Char}
    (h : isNormalizedWindowsDrive buf = true) :
    pathStepUrl.windowsDriveBuffer u buf = buf := by
  unfold pathStepUrl.windowsDriveBuffer
  match buf, h with
  | [a, b], h =>
    simp only [isNormalizedWindowsDrive, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.2]
    simp

/-- Windows drive letter でなければ直しは何もしない。 -/
theorem windowsDriveBuffer_of_not_drive {u : Url} {buf : List Char}
    (h : isWindowsDrive buf = false) : pathStepUrl.windowsDriveBuffer u buf = buf := by
  unfold pathStepUrl.windowsDriveBuffer
  rw [if_neg (by simp [h])]

/-- `.` でも `..` でもない segment を path の末尾に足す。 -/
theorem pathStepUrl_append {u : Url} {pre : List String} {s : String}
    (hp : u.path = .list pre)
    (hwd : pathStepUrl.windowsDriveBuffer u s.toList = s.toList)
    (h1 : isSingleDot s.toList = false) (h2 : isDoubleDot s.toList = false) (slash : Bool) :
    pathStepUrl u slash s.toList = { u with path := .list (pre ++ [s]) } := by
  unfold pathStepUrl
  rw [if_neg (by simp [h2]), if_neg (by simp [h1])]
  rw [hwd]
  unfold appendSegment
  rw [hp]
  simp

/-- serializer が segment を並べる分（先頭の `/` を除く）。 -/
def intercal : List String → List Char
  | [] => []
  | [s] => s.toList
  | s :: rest => s.toList ++ '/' :: intercal rest

/-- path state が segment の列を読み切る。最後の segment は buffer に残る。 -/
theorem run_path_segs (base : Option Url) (sp : Bool) :
    ∀ (segs : List String) (tail : List Char) (ctx : PCtx) (pre : List String),
    ctx.url.path = .list pre → ctx.buffer = [] →
    ctx.url.isSpecial = sp → ctx.over = none →
    (∀ x, segs.head? = some x →
      pathStepUrl.windowsDriveBuffer ctx.url x.toList = x.toList) →
    (∀ s ∈ segs, (∀ c ∈ s.toList, pathSet c = false ∧ isTerminator sp (some c) = false) ∧
      isSingleDot s.toList = false ∧ isDoubleDot s.toList = false) →
    run base .path (intercal segs ++ tail) ctx
      = run base .path tail
          { ctx with
            url := { ctx.url with path := .list (pre ++ segs.dropLast) }
            buffer := (segs.getLast?.getD "").toList } := by
  intro segs
  induction segs with
  | nil =>
    intro tail ctx pre hp hb _ _ _ _
    simp only [intercal, List.nil_append, List.dropLast_nil, List.append_nil,
      List.getLast?_nil, Option.getD_none]
    have h1 : ({ ctx.url with path := Path.list pre } : Url) = ctx.url := by rw [← hp]
    have h2 : ("" : String).toList = ctx.buffer := by rw [hb]; simp
    rw [h1, h2]
  | cons s rest ih =>
    intro tail ctx pre hp hb hsp hov hwd hall
    have hwds : pathStepUrl.windowsDriveBuffer ctx.url s.toList = s.toList := hwd s rfl
    have hs := hall s (by simp)
    cases rest with
    | nil =>
      show run base .path (s.toList ++ tail) ctx = _
      rw [run_path_chunk base sp s.toList tail ctx hsp hov hs.1]
      have h1 : ({ ctx.url with path := Path.list (pre ++ ([s] : List String).dropLast) } : Url)
          = ctx.url := by
        show ({ ctx.url with path := Path.list (pre ++ ([] : List String)) } : Url) = ctx.url
        rw [List.append_nil, ← hp]
      rw [h1, hb, List.nil_append]
      simp
    | cons t u =>
      show run base .path ((s.toList ++ '/' :: intercal (t :: u)) ++ tail) ctx = _
      rw [List.append_assoc]
      rw [run_path_chunk base sp s.toList ('/' :: intercal (t :: u) ++ tail) ctx hsp hov hs.1]
      rw [List.cons_append, run_path_slash]
      rw [ih tail
        { ctx with
          url := pathStepUrl ctx.url true (ctx.buffer ++ s.toList)
          buffer := [] } (pre ++ [s])
        (by rw [hb, List.nil_append, pathStepUrl_append hp hwds hs.2.1 hs.2.2]) rfl
        (by rw [hb, List.nil_append, pathStepUrl_append hp hwds hs.2.1 hs.2.2]; exact hsp)
        hov
        (fun x _ => windowsDriveBuffer_of_path_ne
          (by rw [hb, List.nil_append, pathStepUrl_append hp hwds hs.2.1 hs.2.2]) (by simp))
        (fun x hx => hall x (by simp [hx]))]
      rw [hb, List.nil_append, pathStepUrl_append hp hwds hs.2.1 hs.2.2]
      simp [List.append_assoc]

/-- path の serialize は `/` と segment を交互に並べたものである。 -/
theorem pathSerializer_intercal : ∀ (segs : List String), segs ≠ [] →
    (pathSerializer (.list segs)).toList = '/' :: intercal segs
  | [], h => absurd rfl h
  | [s], _ => by
    rw [pathSerializer_cons]
    simp [intercal]
  | s :: t :: u, _ => by
    rw [pathSerializer_cons]
    have hrec : (t :: u).foldl (fun a x => a ++ "/" ++ x) "" = pathSerializer (.list (t :: u)) := rfl
    rw [hrec]
    rw [show ("/" ++ s ++ pathSerializer (.list (t :: u))).toList
        = ("/" ++ s).toList ++ (pathSerializer (.list (t :: u))).toList from by simp]
    rw [pathSerializer_intercal (t :: u) (by simp)]
    simp [intercal]

/-- `intercal` に現れる文字は `/` か segment の文字である。 -/
theorem intercal_mem : ∀ (segs : List String) (c : Char), c ∈ intercal segs →
    c = '/' ∨ ∃ s ∈ segs, c ∈ s.toList
  | [], c, h => by simp [intercal] at h
  | [s], c, h => Or.inr ⟨s, by simp, by simpa [intercal] using h⟩
  | s :: t :: u, c, h => by
    simp only [intercal, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨s, by simp, h⟩
    · exact Or.inl h
    · rcases intercal_mem (t :: u) c h with h2 | ⟨x, hx, hc⟩
      · exact Or.inl h2
      · exact Or.inr ⟨x, by simp [hx], hc⟩

/-- path set に入らない文字は C0 control percent-encode set にも入らない。 -/
theorem c0Set_of_pathSet {c : Char} (h : pathSet c = false) : c0ControlSet c = false := by
  simp only [pathSet, querySet, Bool.or_eq_false_iff] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- path set に入らない文字は space でもない。 -/
theorem ne_space_of_pathSet {c : Char} (h : pathSet c = false) : ¬c = ' ' := by
  intro he; rw [he] at h; revert h; decide

/-- scheme state の `:`：続きが `/` なら path or authority state へ。 -/
theorem run_scheme_pathOrAuthority (base : Option Url) (rest2 : List Char) (ctx : PCtx)
    (hov : ctx.over = none)
    (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = false) :
    run base .scheme (':' :: '/' :: rest2) ctx
      = run base .pathOrAuthority rest2
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_neg (by simp [Url.isSpecial, hsp])]

/-- path or authority state：`/` でなければ path state へ、読んだ文字ごと渡す。 -/
theorem run_pathOrAuthority_path (base : Option Url) (l : List Char) (ctx : PCtx)
    (h : ∀ c ∈ l.head?, ¬c = '/') :
    run base .pathOrAuthority l ctx = run base .path l ctx := by
  cases l with
  | nil => rw [run, step]; simp
  | cons c t =>
    rw [run, step]
    rw [if_neg (by simpa using h c rfl)]

/-- segment の列の先頭の文字は、先頭 segment の文字である（先頭が空でなければ）。 -/
theorem intercal_head_ne_slash : ∀ (segs : List String) (c : Char),
    (∀ x t, segs = x :: t → t ≠ [] → ¬x = "") →
    (∀ x ∈ segs, ∀ d ∈ x.toList, ¬d = '/') →
    c ∈ (intercal segs).head? → ¬c = '/'
  | [], c, _, _, h => by simp [intercal] at h
  | [x], c, _, hall, h => by
    refine hall x (by simp) c ?_
    simpa [intercal] using List.mem_of_mem_head? h
  | x :: y :: u, c, hfirst, hall, h => by
    have hx : ¬x = "" := hfirst x (y :: u) rfl (by simp)
    have hxl : x.toList ≠ [] := by simp_all
    cases hxx : x.toList with
    | nil => exact absurd hxx hxl
    | cons d t =>
      refine hall x (by simp) c ?_
      simp only [intercal, hxx, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at h
      rw [hxx, ← h]
      simp

/-- 最後の segment を戻すと元の列になる。 -/
theorem dropLast_getLast? : ∀ (l : List String), l ≠ [] →
    l.dropLast ++ [l.getLast?.getD ""] = l
  | [], h => absurd rfl h
  | [s], _ => by simp
  | s :: t :: u, _ => by
    rw [List.dropLast_cons_cons, List.getLast?_cons_cons, List.cons_append,
      dropLast_getLast? (t :: u) (by simp)]

/-- scheme に使える文字は C0 control でも space でもない。 -/
theorem ne_c0_of_schemeChar {c : Char} (h : schemeChar c = true) :
    isC0ControlOrSpace c = false := by
  simp only [schemeChar, isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
    isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [isC0ControlOrSpace, decide_eq_false_iff_not, Nat.not_le]
  rcases h with (((h | h | h) | h) | h) | h <;> first | omega | (subst h; decide)

/-- serializer が path を並べる分（host の後ろ）。 -/
def pathChars : List String → List Char
  | [] => []
  | s :: rest => '/' :: intercal (s :: rest)

/-- path の serialize は `pathChars` である。 -/
theorem pathSerializer_pathChars : ∀ (segs : List String),
    (pathSerializer (.list segs)).toList = pathChars segs
  | [] => rfl
  | s :: rest => by rw [pathSerializer_intercal (s :: rest) (by simp)]; rfl

end Url
