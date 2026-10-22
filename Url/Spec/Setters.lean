import Url.Spec.ParseEquiv
import Url.Api
import Url.ParseImage

/-!
# setter の効果（§6.1）を入力に制限を付けずに書く

`Url/ApiValid.lean` の `setPathname_spec` は一 segment の入力、`setHost_spec` は `:` を含まない入力に
限ってある。ここではその制限を外し、setter が URL record をどう書き換えるかを入力の関数として書く。

* `pathname`：先頭の区切りを一つ落とし、残りを path state と同じ畳み込み（`resolveSegs`）で読む。
  state override があるので `?` と `#` は区切りでなく、segment の中で percent-encode される。
* `port`：先頭の ASCII digit の並びを 10 進で読む。digit が無いか 65535 を超えれば何も変えない。
* `host` / `hostname`：区切りまでを bracket の外の最初の `:` で host と port に分ける。
  host が読めなければ何も変えず、port が範囲外なら **host だけ変えて port は変えない**。
-/

namespace Url.Spec

open Infra Url

/-! ## state override 付きの path state -/

/-- override 付きの path state の区切りでない文字（`?` と `#` を含む）。percent-encode して buffer に積む。 -/
theorem run_path_plain_over (base : Option Url) {c : Char} (rest : List Char) (ctx : PCtx)
    (h : isPathSep ctx.url.isSpecial c = false) (hov : ctx.over.isSome = true) :
    run base .path (c :: rest) ctx
      = run base .path rest { ctx with buffer := ctx.buffer ++ (encChar pathSet c).toList } := by
  simp only [isPathSep, Bool.or_eq_false_iff, Bool.and_eq_false_imp, beq_eq_false_iff_ne] at h
  rw [run, step]
  rw [if_neg (by
    simp only [Bool.or_eq_true, beq_iff_eq, Option.some.injEq, reduceCtorEq, false_or,
      Bool.and_eq_true, not_or, not_and, Option.isNone_iff_eq_none]
    refine ⟨⟨h.1, fun hs => h.2 hs⟩, fun hn => by simp [hn] at hov⟩)]

/-- **override 付きの path state は、区切りまでの片を `segStep` で畳みながら読む。** -/
theorem run_path_read_over (base : Option Url) : ∀ (l : List Char) (ctx : PCtx) (P : List String),
    ctx.url.path = .list P → ctx.over.isSome = true →
    run base .path l ctx
      = .ok { ctx.url with path := .list (resolveSegs (ctx.url.scheme == "file") P
          ((pathSegments ctx.url.isSpecial l).modifyHead (ctx.buffer ++ ·))) } := by
  intro l
  induction l with
  | nil =>
    intro ctx P hp _
    rw [run_path_end, pathStepUrl_eq_segStep hp]
    simp [resolveSegs, foldSegs, pathSegments, splitSegs, splitBy, encodeSeg,
      show utf8PercentEncode pathSet [] = [] from rfl]
  | cons c t ih =>
    intro ctx P hp hov
    have hne := splitBy_ne_nil (isPathSep ctx.url.isSpecial) t
    by_cases hsep : isPathSep ctx.url.isSpecial c = true
    · rw [run_path_sep base _ ctx hsep]
      rw [pathStepUrl_eq_segStep hp true ctx.buffer, Bool.not_true]
      refine Eq.trans (ih _ (segStep (ctx.url.scheme == "file") P ctx.buffer false) rfl hov) ?_
      simp only [pathSegments, splitSegs, Url.isSpecial] at hne hsep ⊢
      rw [show splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) (c :: t)
          = [] :: splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) t by simp [splitBy, hsep]]
      revert hne
      cases splitBy (isPathSep (isSpecialScheme ctx.url.scheme)) t with
      | nil => intro h; exact absurd rfl h
      | cons x r =>
        intro _
        simp [resolveSegs, foldSegs, encodeSeg, List.dropLast_cons_of_ne_nil, List.getLast?_cons,
          show utf8PercentEncode pathSet [] = [] from rfl]
    · have hsep' : isPathSep ctx.url.isSpecial c = false := by simpa using hsep
      rw [run_path_plain_over base _ ctx hsep' hov]
      refine Eq.trans (ih _ P hp hov) ?_
      simp only [pathSegments, splitSegs]
      rw [splitBy_cons_nosep hsep' t]
      revert hne
      cases splitBy (isPathSep ctx.url.isSpecial) t with
      | nil => intro h; exact absurd rfl h
      | cons x r =>
        intro _
        simp [encodeSeg_cons, List.append_assoc]

/-! ## `pathname` setter -/

/--
`pathname` setter が書く path。

§6.1 は path を空にしてから path start state を override 付きで走らせる。path start state は
先頭の区切り（`/`、special なら `\` も）を一つだけ読み飛ばし、残りを path state に渡す。
入力が空なら、special な URL では空の segment が一つ、special でない URL では host が null のときだけ
空の segment が一つ残る（path start state 5）。
-/
def pathnameSpec (u : Url) (v : String) : List String :=
  match stripTabNewline v.toList with
  | [] => if u.isSpecial || u.host.isNone then [""] else []
  | c :: t =>
    resolveSegs (u.scheme == "file") []
      (pathSegments u.isSpecial (if isPathSep u.isSpecial c then t else c :: t))

/--
**`pathname` setter は path だけを `pathnameSpec` に書き換える。** 入力に制限は無い。

`?` と `#` は区切りにならず segment の中で percent-encode される。`.` と `..` は畳まれ、
`file` URL の先頭の `c|` は `c:` に直る。
-/
theorem setPathname_eq (u : Url) (v : String) (hop : u.hasOpaquePath = false) :
    u.setPathname v = { u with path := .list (pathnameSpec u v) } := by
  unfold Url.setPathname
  rw [if_neg (by simp [hop])]
  simp only [basicUrlParseOverride, SOverride.start]
  unfold pathnameSpec
  generalize stripTabNewline v.toList = l
  have hpath : ({ u with path := Path.list [] } : Url).path = .list [] := rfl
  cases l with
  | nil =>
    rw [run, step]
    by_cases hsp : u.isSpecial = true
    · simp only [show ({ u with path := Path.list [] } : Url).isSpecial = true from hsp, if_true]
      rw [if_neg (by simp)]
      rw [run_path_end, pathStepUrl_eq_segStep hpath]
      simp [segStep, hsp, isDoubleDot, isSingleDot, asciiLowercase, isWindowsDrive]
    · have hsp' : u.isSpecial = false := by simpa using hsp
      simp only [show ({ u with path := Path.list [] } : Url).isSpecial = false from hsp',
        Bool.false_eq_true, if_false, Option.isNone_some, Bool.false_and, Option.isSome_some,
        Bool.true_and, hsp', Bool.false_or]
      cases hh : u.host with
      | none => simp [appendSegment]
      | some h => simp
  | cons c t =>
    have hrd : ∀ l : List Char, run none .path l
        { url := { u with path := Path.list [] }, over := some SOverride.path }
        = .ok { u with path := .list (resolveSegs (u.scheme == "file") [] (pathSegments u.isSpecial l)) } := by
      intro l
      rw [run_path_read_over none l _ [] rfl rfl]
      have hid : ∀ m : List (List Char), m.modifyHead (fun x => x) = m := by
        intro m; cases m <;> rfl
      simp only [List.nil_append, hid]
      rfl
    have hgo : run none .pathStart (c :: t)
        { url := { u with path := Path.list [] }, over := some SOverride.path }
        = run none .path (if isPathSep u.isSpecial c then t else c :: t)
            { url := { u with path := Path.list [] }, over := some SOverride.path } := by
      rw [run, step]
      by_cases hsp : u.isSpecial = true
      · simp only [show ({ u with path := Path.list [] } : Url).isSpecial = true from hsp, if_true,
          isPathSep, hsp, Bool.true_and]
        by_cases hc : (c == '/' || c == '\\') = true
        · rw [if_pos (by simpa using hc), if_pos hc]
        · rw [if_neg (by simpa using hc), if_neg hc]
      · have hsp' : u.isSpecial = false := by simpa using hsp
        simp only [show ({ u with path := Path.list [] } : Url).isSpecial = false from hsp',
          Bool.false_eq_true, if_false, Option.isNone_some, Bool.false_and, isPathSep, hsp',
          Bool.or_false]
        by_cases hc : (c == '/') = true
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
    rw [hgo, hrd]
    rfl

/-! ## `port` setter -/

/--
`port` setter が書く URL。

* URL が port を持てなければ何もしない（§6.1 port setter 1）。
* 空文字列なら port を null にする（2）。tab と newline を取り除く前の値で見る。
* そうでなければ port state を override 付きで走らせる（3）。port state は先頭の ASCII digit を読み、
  digit でない文字で止まる（override 付きでは何が来ても止まる）。digit が無ければ何もしない。
  65535 を超えれば失敗して何もしない。既定 port なら null にする。
-/
def portSpec (u : Url) (v : String) : Url :=
  -- §4.2「cannot have a username/password/port」：host が null か空、または scheme が `file`。
  if u.host.isNone || u.host == some .empty || u.scheme == "file" then u
  else if v.isEmpty then { u with port := none }
  else
    let d := (stripTabNewline v.toList).takeWhile isAsciiDigit
    if d.isEmpty || decide (decimalOf d > 65535) then u
    else { u with port := if defaultPort u.scheme = some (decimalOf d) then none
                          else some (decimalOf d) }

/-- override 付きの port state は先頭の digit を読み、そこで `portDone` に渡す。 -/
theorem run_port_over (base : Option Url) : ∀ (l : List Char) (ctx : PCtx), ctx.over.isSome = true →
    run base .port l ctx
      = match portDone { ctx with buffer := ctx.buffer ++ l.takeWhile isAsciiDigit } with
        | none => .ok ctx.url
        | some ctx2 => .ok ctx2.url := by
  intro l
  induction l with
  | nil =>
    intro ctx hov
    rw [run, step]
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hov
    simp only [List.takeWhile_nil, List.append_nil]
    cases portDone ctx <;> simp [fail, ho]
  | cons c t ih =>
    intro ctx hov
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hov
    rw [run, step]
    by_cases hd : isAsciiDigit c = true
    · rw [if_pos hd, ih]
      · simp [hd, List.append_assoc]
      · exact hov
    · rw [if_neg hd, if_pos (by simp [ho])]
      simp only [List.takeWhile_cons, hd, Bool.false_eq_true, if_false, List.append_nil]
      have : ({ ctx with buffer := ctx.buffer } : PCtx) = ctx := rfl
      rw [this]
      cases portDone ctx <;> simp [fail, ho]

/-- **`port` setter は `portSpec` である。** 入力に制限は無い。 -/
theorem setPort_eq (u : Url) (v : String) : u.setPort v = portSpec u v := by
  unfold Url.setPort portSpec Url.cannotHaveCredentials
  by_cases hc : (u.host.isNone || u.host == some Host.empty || u.scheme == "file") = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    by_cases he : v.isEmpty = true
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he]
      simp only [basicUrlParseOverride, SOverride.start]
      rw [run_port_over none _ _ rfl]
      simp only [List.nil_append]
      generalize (stripTabNewline v.toList).takeWhile isAsciiDigit = d
      unfold portDone
      by_cases hd : d.isEmpty = true
      · simp [hd]
      · simp only [hd, Bool.false_eq_true, if_false, Bool.false_or, ← decimalOf_eq_portValue]
        by_cases hv : decimalOf d > 65535
        · simp [hv]
        · simp [hv, portSet, portOf]

/-! ## `host` / `hostname` setter -/

/-- override の有無によらず、file host state へ逸れない host state の読み取り。 -/
theorem run_host_read_gen (base : Option Url) : ∀ (hp T : List Char) (ctx : PCtx),
    (ctx.over.isSome && ctx.url.scheme == "file") = false →
    (∀ c ∈ hp, isTerminator ctx.url.isSpecial (some c) = false) →
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
    intro T ctx hnf h
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
      rw [if_neg (by simp [hnf]), if_neg (by simpa using hcol), if_neg (by simp [ht])]
      rw [ih T]
      · cases splitHostPort (if c == '[' then true else if c == ']' then false else ctx.insideBrackets) hp with
        | mk hh pp =>
          cases pp with
          | none => simp [bracketsAfter, List.append_assoc]
          | some p => simp [List.append_assoc]
      · exact hnf
      · exact fun x hx => h x (by simp [hx])

/-- host state の区切り（`/` `?` `#`、special なら `\` も）。 -/
def hostDelim (special : Bool) (c : Char) : Bool :=
  c == '/' || c == '?' || c == '#' || (special && c == '\\')

theorem isTerminator_eq_hostDelim (special : Bool) (c : Char) :
    isTerminator special (some c) = hostDelim special c := rfl

/-- override 付きの host state の区切り。host を確定させて返す。 -/
theorem run_host_term_over (base : Option Url) (T : List Char) (ctx : PCtx) {o : SOverride}
    (ho : ctx.over = some o) (hnf : ctx.url.scheme ≠ "file")
    (hT : ∀ c r, T = c :: r → hostDelim ctx.url.isSpecial c = true) :
    run base .host T ctx
      = .ok (if ctx.buffer.isEmpty &&
                (ctx.url.isSpecial || ctx.url.includesCredentials || ctx.url.port.isSome) then ctx.url
             else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
               | none => ctx.url
               | some h => { ctx.url with host := some h }) := by
  have hnf' : (ctx.over.isSome && ctx.url.scheme == "file") = false := by simp [hnf]
  have hcommon :
      (if (ctx.url.isSpecial && ctx.buffer.isEmpty) = true then fail ctx
       else if (ctx.over.isSome && ctx.buffer.isEmpty &&
           (ctx.url.includesCredentials || ctx.url.port.isSome)) = true then PResult.ok ctx.url
       else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
         | none => fail ctx
         | some h =>
           if ctx.over.isSome = true then PResult.ok { ctx.url with host := some h }
           else run base .pathStart T { ctx with url := { ctx.url with host := some h }, buffer := [] })
      = .ok (if ctx.buffer.isEmpty &&
                (ctx.url.isSpecial || ctx.url.includesCredentials || ctx.url.port.isSome) then ctx.url
             else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
               | none => ctx.url
               | some h => { ctx.url with host := some h }) := by
    by_cases hb : ctx.buffer.isEmpty = true
    · by_cases hs : ctx.url.isSpecial = true
      · simp [hb, hs, fail, ho]
      · have hs' : ctx.url.isSpecial = false := by simpa using hs
        by_cases hcp : (ctx.url.includesCredentials || ctx.url.port.isSome) = true
        · simp [hb, hs', ho, hcp]
        · have hcp' : (ctx.url.includesCredentials || ctx.url.port.isSome) = false := by
            simpa using hcp
          simp only [hb, hs', ho, hcp', Bool.and_false, Bool.false_eq_true, if_false,
            Option.isSome_some, Bool.false_or, Bool.and_self]
          cases hostParser ctx.toAscii ctx.buffer (!false) <;> simp [fail, ho]
    · simp only [hb, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
      cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, ho]
  cases T with
  | nil =>
    rw [run, step, if_neg (by simp [hnf']), if_neg (by simp), if_pos (by rfl)]
    exact hcommon
  | cons c r =>
    have hd := hT c r rfl
    have hc : c ≠ ':' := fun e => by subst e; simp [hostDelim] at hd
    rw [run, step, if_neg (by simp [hnf']), if_neg (by simp [hc]),
      if_pos (by rw [isTerminator_eq_hostDelim]; exact hd)]
    exact hcommon

/-- override 付きの host state の bracket の外の `:`。 -/
theorem run_host_colon_over (base : Option Url) (r : List Char) (ctx : PCtx) {o : SOverride}
    (ho : ctx.over = some o) (hnf : ctx.url.scheme ≠ "file") (hib : ctx.insideBrackets = false) :
    run base .host (':' :: r) ctx
      = if ctx.buffer.isEmpty || o == .hostname then .ok ctx.url
        else match hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
          | none => .ok ctx.url
          | some h => run base .port r { ctx with url := { ctx.url with host := some h }, buffer := [] } := by
  rw [run, step, if_neg (by simp [hnf]), if_pos (by simp [hib])]
  by_cases hb : ctx.buffer.isEmpty = true
  · rw [if_pos hb]; simp [hb, fail, ho]
  · rw [if_neg hb]
    by_cases hh : o = .hostname
    · subst hh; simp [hb, ho]
    · rw [if_neg (by simp [ho, hh])]
      simp only [hb, Bool.false_or, beq_iff_eq, hh, if_false]
      cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) <;> simp [fail, ho]

/-- file host state の区切り（`/` `\` `?` `#`）。 -/
def fileHostDelim (c : Char) : Bool := c == '/' || c == '\\' || c == '?' || c == '#'

/-- **override 付きの file host state は区切りまでを host として読む。** `localhost` は空の host になる。 -/
theorem run_fileHost_over (base : Option Url) : ∀ (l : List Char) (ctx : PCtx) (o : SOverride),
    ctx.over = some o →
    run base .fileHost l ctx
      = .ok (if (ctx.buffer ++ l.takeWhile (fun c => !fileHostDelim c)).isEmpty then
                { ctx.url with host := some .empty }
             else match hostParser ctx.toAscii (ctx.buffer ++ l.takeWhile (fun c => !fileHostDelim c))
                    (!ctx.url.isSpecial) with
               | none => ctx.url
               | some h => { ctx.url with host := some (if hostSerializer h = "localhost" then .empty
                                                       else h) }) := by
  intro l
  induction l with
  | nil =>
    intro ctx o ho
    rw [run, step, if_pos (by simp), if_neg (by simp [ho])]
    simp only [List.takeWhile_nil, List.append_nil]
    by_cases hb : ctx.buffer.isEmpty = true
    · simp [hb, ho]
    · simp only [hb, Bool.false_eq_true, if_false]
      cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
      | none => simp [fail, ho]
      | some h => simp [ho, beq_iff_eq]
  | cons c t ih =>
    intro ctx o ho
    by_cases hd : fileHostDelim c = true
    · rw [run, step, if_pos (by simp [fileHostDelim] at hd; rcases hd with ((h | h) | h) | h <;> simp [h]),
        if_neg (by simp [ho])]
      simp only [List.takeWhile_cons, hd, Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
      by_cases hb : ctx.buffer.isEmpty = true
      · simp [hb, ho]
      · simp only [hb, Bool.false_eq_true, if_false]
        cases hostParser ctx.toAscii ctx.buffer (!ctx.url.isSpecial) with
        | none => simp [fail, ho]
        | some h => simp [ho, beq_iff_eq]
    · have hd' : fileHostDelim c = false := by simpa using hd
      simp only [fileHostDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hd'
      rw [run, step, if_neg (by simp [hd'.1.1.1, hd'.1.1.2, hd'.1.2, hd'.2])]
      simp only
      rw [ih _ o]
      · simp [fileHostDelim, hd'.1.1.1, hd'.1.1.2, hd'.1.2, hd'.2, List.append_assoc]
      · exact ho

/--
`host` setter（`isHostname = false`）と `hostname` setter（`isHostname = true`）が書く URL。

* opaque path なら何もしない（§6.1 1）。
* `file` URL は file host state で読む。区切りまでを host にし、空なら空の host、`localhost` も空の host。
* それ以外は host state で読む。区切りまでを bracket の外の最初の `:` で host と port に分ける。
  * `:` が無いとき：host が空で、special か credentials か port があれば何もしない（host state 3.1-3.2）。
  * `:` があるとき：host が空か `hostname` setter なら何もしない（host state 2.1-2.2）。
    port は先頭の digit を読み、digit が無いか 65535 を超えれば **host だけを書き換える**。
  * host parser が失敗すれば何もしない。
-/
def hostSetterSpec (t : List Char → Option String) (u : Url) (v : String) (isHostname : Bool) : Url :=
  if u.hasOpaquePath then u
  else
    let l := stripTabNewline v.toList
    if u.scheme = "file" then
      let hp := l.takeWhile (fun c => !fileHostDelim c)
      if hp.isEmpty then { u with host := some .empty }
      else match hostParser t hp false with
        | none => u
        | some h => { u with host := some (if hostSerializer h = "localhost" then .empty else h) }
    else
      let hp := l.takeWhile (fun c => !hostDelim u.isSpecial c)
      match splitHostPort false hp with
      | (h, none) =>
        if h.isEmpty && (u.isSpecial || u.includesCredentials || u.port.isSome) then u
        else match hostParser t h (!u.isSpecial) with
          | none => u
          | some host => { u with host := some host }
      | (h, some p) =>
        if h.isEmpty || isHostname then u
        else match hostParser t h (!u.isSpecial) with
          | none => u
          | some host =>
            if (p.takeWhile isAsciiDigit).isEmpty || decide (decimalOf (p.takeWhile isAsciiDigit) > 65535)
            then { u with host := some host }
            else { u with host := some host,
                          port := if defaultPort u.scheme = some (decimalOf (p.takeWhile isAsciiDigit))
                                  then none else some (decimalOf (p.takeWhile isAsciiDigit)) }

/-- port の digit は区切りより前で止まる。 -/
theorem takeWhile_digit_append (p T : List Char)
    (hT : ∀ c r, T = c :: r → isAsciiDigit c = false) :
    (p ++ T).takeWhile isAsciiDigit = p.takeWhile isAsciiDigit := by
  induction p with
  | nil =>
    cases T with
    | nil => rfl
    | cons c r => simp [hT c r rfl]
  | cons c p ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    split <;> simp_all

theorem hostDelim_not_digit {sp : Bool} {c : Char} (h : hostDelim sp c = true) :
    isAsciiDigit c = false := by
  simp only [hostDelim, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨_, h⟩ <;> subst h <;> decide

/-- override 付きで `file` URL の host state に入ると、そのまま file host state で読む（host state 1）。 -/
theorem run_host_file_over (base : Option Url) (l : List Char) (ctx : PCtx) {o : SOverride}
    (ho : ctx.over = some o) (hf : ctx.url.scheme = "file") :
    run base .host l ctx = run base .fileHost l ctx := by
  cases l with
  | nil => rw [run, step, if_pos (by simp [ho, hf])]
  | cons c r => rw [run, step, if_pos (by simp [ho, hf])]

/-- **`host` / `hostname` setter は `hostSetterSpec` である。** 入力に制限は無い。 -/
theorem setHostGen_eq (u : Url) (v : String) (t : List Char → Option String) (o : SOverride)
    (ho : o = .host ∨ o = .hostname) :
    (if u.hasOpaquePath then u else (basicUrlParseOverride v u o t).getD u)
      = hostSetterSpec t u v (o == .hostname) := by
  unfold hostSetterSpec
  by_cases hop : u.hasOpaquePath = true
  · rw [if_pos hop, if_pos hop]
  · rw [if_neg hop, if_neg hop]
    have hst : o.start = .host := by rcases ho with rfl | rfl <;> rfl
    simp only [basicUrlParseOverride, hst]
    generalize stripTabNewline v.toList = l
    by_cases hf : u.scheme = "file"
    · rw [if_pos hf, run_host_file_over none l _ rfl hf, run_fileHost_over none l _ o rfl]
      simp only [List.nil_append, Option.getD_some]
      have hsp : u.isSpecial = true := by simp [Url.isSpecial, hf, isSpecialScheme]
      simp [hsp]
    · rw [if_neg hf]
      have hnf' : (({ url := u, over := some o, toAscii := t } : PCtx).over.isSome &&
          ({ url := u, over := some o, toAscii := t } : PCtx).url.scheme == "file") = false := by
        simp [hf]
      have hdec := List.takeWhile_append_dropWhile (p := fun c => !hostDelim u.isSpecial c) (l := l)
      have hT : ∀ c r, l.dropWhile (fun c => !hostDelim u.isSpecial c) = c :: r →
          hostDelim u.isSpecial c = true := by
        intro c r he
        have := List.head_dropWhile_not (fun c => !hostDelim u.isSpecial c) (l := l) (by rw [he]; simp)
        simp only [he, List.head_cons] at this
        simpa using this
      have hterm : ∀ c ∈ l.takeWhile (fun c => !hostDelim u.isSpecial c),
          isTerminator ({ url := u, over := some o, toAscii := t } : PCtx).url.isSpecial (some c) = false := by
        intro c hc
        have := List.all_eq_true.mp List.all_takeWhile c hc
        simpa [isTerminator_eq_hostDelim] using this
      conv => lhs; rw [← hdec]
      rw [run_host_read_gen none _ _ _ hnf' hterm]
      simp only [List.nil_append]
      generalize l.takeWhile (fun c => !hostDelim u.isSpecial c) = hp at hterm ⊢
      generalize l.dropWhile (fun c => !hostDelim u.isSpecial c) = T at hT ⊢
      rcases hsplit : splitHostPort false hp with ⟨h, _ | p⟩
      · simp only
        rw [run_host_term_over none T _ rfl hf hT]
        rfl
      · simp only
        rw [run_host_colon_over none _ _ rfl hf rfl]
        simp only
        by_cases hb : (h.isEmpty || o == .hostname) = true
        · rw [if_pos hb, if_pos hb]; rfl
        · rw [if_neg hb, if_neg hb]
          cases hostParser t h (!u.isSpecial) with
          | none => rfl
          | some host =>
            simp only
            rw [run_port_over none _ _ rfl]
            simp only [List.nil_append]
            rw [takeWhile_digit_append p T (fun c r he => hostDelim_not_digit (hT c r he))]
            generalize p.takeWhile isAsciiDigit = d
            unfold portDone
            by_cases hd : d.isEmpty = true
            · simp [hd]
            · simp only [hd, Bool.false_eq_true, if_false, Bool.false_or, ← decimalOf_eq_portValue]
              by_cases hv : decimalOf d > 65535
              · simp [hv]
              · simp [hv, portSet, portOf]

/-- **`host` setter。** -/
theorem setHost_eq (u : Url) (v : String) (t : List Char → Option String) :
    u.setHost v t = hostSetterSpec t u v false := by
  unfold Url.setHost
  exact setHostGen_eq u v t .host (.inl rfl)

/-- **`hostname` setter。** port を読まないこと以外は `host` setter と同じである。 -/
theorem setHostname_eq (u : Url) (v : String) (t : List Char → Option String) :
    u.setHostname v t = hostSetterSpec t u v true := by
  unfold Url.setHostname
  exact setHostGen_eq u v t .hostname (.inr rfl)

/-! ## `href` setter -/

/--
**parse の結果の `href` を `href` setter に代入しても URL は変わらない。**

`href` setter は base 無しで parse し直すだけなので、parse の像の上の往復（`parseUrl_serialize`）そのものである。
-/
theorem setHref_href {t : List Char → Option String} (htok : ToAsciiOk t) {input : String}
    {base : Option String} {u : Url} (h : parseUrl input base t = some u) :
    Url.setHref u.href t = some u := by
  have := parseUrl_serialize htok h
  simpa [Url.setHref, Url.href, parseUrl] using this

/-! ## `protocol` setter -/

/--
`protocol` setter が書く URL。

§6.1 は値の後ろに `:` を足して scheme start state から override 付きで読む。scheme の文字の並びが `:` に至れば
それが新しい scheme で、scheme state 2.1 の四つの門のどれかに当たれば何もしない。至らなければ何もしない。
既定 port と同じ port は null にする（scheme state 2.5）。
-/
def protocolSpec (u : Url) (v : String) : Url :=
  match splitScheme (stripTabNewline (v.toList ++ [':'])) with
  | none => u
  | some (s, _) =>
    if u.isSpecial ≠ isSpecialScheme s then u
    else if (u.includesCredentials || u.port.isSome) && s = "file" then u
    else if u.scheme = "file" && u.host = some .empty then u
    else { u with scheme := s, port := if defaultPort s = u.port then none else u.port }

/-- override 付きの scheme state は、`:` に至らなければ url を変えずに止まる。 -/
theorem run_scheme_over_fail (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    ctx.over.isSome = true →
    (∀ pre tail, l = pre ++ ':' :: tail → pre.all isSchemeTail = false) →
    run base .scheme l ctx = .ok ctx.url := by
  intro l
  induction l with
  | nil =>
    intro ctx hov _
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hov
    rw [run, step]; simp [ho, fail]
  | cons c l' ih =>
    intro ctx hov h
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hov
    rw [run, step]
    by_cases hs : isSchemeTail c = true
    · rw [if_pos (by simpa [isSchemeTail] using hs)]
      exact ih _ hov (fun pre tail he => by
        have := h (c :: pre) tail (by rw [he]; simp)
        simpa [List.all_cons, hs] using this)
    · have hcol : ¬ c = ':' := by
        intro he
        have := h [] l' (by rw [he]; simp)
        simp at this
      rw [if_neg (by simp only [isSchemeTail, Bool.or_eq_true, beq_iff_eq] at hs; simpa using hs)]
      rw [if_neg (by simpa using hcol)]
      simp [ho, fail]

/-- **`protocol` setter は `protocolSpec` である。** 入力に制限は無い。 -/
theorem setProtocol_eq (u : Url) (v : String) : u.setProtocol v = protocolSpec u v := by
  unfold Url.setProtocol protocolSpec
  simp only [basicUrlParseOverride, SOverride.start, String.toList_append]
  rw [show (":" : String).toList = [':'] from rfl]
  generalize stripTabNewline (v.toList ++ [':']) = l
  cases hs : splitScheme l with
  | none =>
    have hns := (splitScheme_none_iff l).mp hs
    cases l with
    | nil => rw [run, step]; simp [fail]
    | cons a r =>
      rw [run, step]
      by_cases ha : isAsciiAlpha a = true
      · rw [if_pos ha, run_scheme_over_fail none _ _ rfl (fun pre tail he => by
          cases hp : pre.all isSchemeTail
          · rfl
          · exact absurd ⟨a, pre, tail, by rw [he], ha, hp⟩ hns)]
        rfl
      · rw [if_neg ha]; simp [fail]
  | some p =>
    obtain ⟨sc, rest⟩ := p
    obtain ⟨a, pre, rfl, ha, hpre, rfl⟩ := splitScheme_some hs
    simp only
    rw [run, step, if_pos ha, run_scheme_prefix none pre _ _ hpre, run, step]
    have hcol : (isAsciiAlphanumeric ':' || ':' == '+' || ':' == '-' || ':' == '.') = false := by
      decide
    simp only [asciiLowercase, List.nil_append, String.toList_ofList, List.map_cons, List.map_nil,
      List.cons_append, hcol, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
      Option.isSome_some]
    unfold schemeOverride
    dsimp only
    have hS : String.ofList (List.map asciiLowerChar (a :: pre))
        = String.ofList (asciiLowerChar a :: List.map asciiLowerChar pre) := by simp
    simp only [List.map_cons] at *
    generalize String.ofList (asciiLowerChar a :: List.map asciiLowerChar pre) = S
    by_cases g1 : (u.isSpecial && !isSpecialScheme S) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at g1
      simp only [g1, Bool.true_and, Bool.not_false, if_true, Option.getD_some]
      rw [if_pos (by decide)]
    by_cases g2 : (!u.isSpecial && isSpecialScheme S) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at g2
      simp only [g2, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false,
        if_true, Option.getD_some]
      rw [if_pos (by decide)]
    have hsame : u.isSpecial = isSpecialScheme S := by
      cases h1 : u.isSpecial <;> cases h2 : isSpecialScheme S <;> simp_all
    rw [if_neg g1, if_neg g2, if_neg (show ¬(u.isSpecial ≠ isSpecialScheme S) from fun h => h hsame)]
    by_cases g3 : ((u.includesCredentials || u.port.isSome) && S == "file") = true
    · rw [if_pos g3, if_pos (show ((u.includesCredentials || u.port.isSome) && decide (S = "file")) = true
        by simpa using g3)]
      rfl
    rw [if_neg g3, if_neg (show ¬((u.includesCredentials || u.port.isSome) && decide (S = "file")) = true
      by simpa using g3)]
    by_cases g4 : (u.scheme == "file" && u.host == some Host.empty) = true
    · rw [if_pos g4, if_pos (show (decide (u.scheme = "file") && decide (u.host = some Host.empty)) = true
        by simpa using g4)]
      rfl
    rw [if_neg g4, if_neg (show ¬(decide (u.scheme = "file") && decide (u.host = some Host.empty)) = true
      by simpa using g4)]
    simp only [Option.getD_some]
    by_cases g5 : defaultPort S = u.port
    · rw [if_pos (show (defaultPort S == u.port) = true by simp [g5]), if_pos g5]
    · rw [if_neg (show ¬(defaultPort S == u.port) = true by simpa using g5), if_neg g5]

end Url.Spec
