import Url.Api

/-!
# 失敗条件の関係仕様

`basicUrlParse` が `none` を返す条件を、state machine とは独立に**入力の形**として書く。

`Url/Invariant.lean` から `Url/Roundtrip.lean` までの定理は「parse が成功したとき
結果がどうなるか」を述べる。そこには「そもそも成功してはいけない入力」が入らないので、
仕様の "return failure" を読み違えて guard を緩めても気づけない。ここはその穴を埋める。

書き方は `Dom/Spec/` と同じである。

* 関係（`HasScheme`、`decimalOf`）は parser の関数を呼ばずに、入力の形だけで定義する。
* そのうえで実行可能な parser との対応を定理にする。

読む向きは二つある。`basicUrlParse_eq_none_of_*` は「この形の入力は失敗する」、
`*_of_basicUrlParse` はその対偶で「parse が成功したなら入力はこの形ではない」。
-/

namespace Url.Spec

open Infra Url

/-! ## scheme があること -/

/--
scheme state が buffer に積める文字。URL Standard §4.4 scheme state の
"ASCII alphanumeric, U+002B (+), U+002D (-), U+002E (.)"。
-/
def isSchemeTail (c : Char) : Bool :=
  isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.'

/--
入力が scheme で始まること。

仕様の scheme start state と scheme state を、state machine ではなく
「先頭が ASCII alpha で、そこから `:` までが scheme 文字の並び」という
入力の形として書いたもの。
-/
def HasScheme (l : List Char) : Prop :=
  ∃ a pre tail, l = a :: (pre ++ ':' :: tail) ∧ isAsciiAlpha a = true ∧
    pre.all isSchemeTail = true

/-- `:` の手前に scheme でない文字があれば scheme state は "start over" する。 -/
theorem run_scheme_startOver (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    ctx.over = none →
    (∀ pre tail, l = pre ++ ':' :: tail → pre.all isSchemeTail = false) →
    run base .scheme l ctx = .startOver := by
  intro l
  induction l with
  | nil => intro ctx hov _; rw [run, step]; simp [hov]
  | cons c l' ih =>
    intro ctx hov h
    rw [run, step]
    by_cases hs : isSchemeTail c = true
    · rw [if_pos (by simpa [isSchemeTail] using hs)]
      refine ih _ hov ?_
      intro pre tail he
      have := h (c :: pre) tail (by rw [he]; simp)
      simpa [List.all_cons, hs] using this
    · have hcol : ¬ c = ':' := by
        intro he
        have := h [] l' (by rw [he]; simp)
        simp at this
      rw [if_neg (by
        simp only [isSchemeTail, Bool.or_eq_true, beq_iff_eq] at hs
        simpa using hs)]
      rw [if_neg (by simpa using hcol)]
      simp [hov]

/-- base が無ければ no scheme state はその場で失敗する（§4.4 no scheme state step 1）。 -/
theorem run_noScheme_none (l : List Char) (ctx : PCtx) (hov : ctx.over = none) :
    run (none : Option Url) .noScheme l ctx = .failure := by
  cases l with
  | nil => rw [run, step]; simp [fail, hov]
  | cons c t => rw [run, step]; simp [fail, hov]

/--
base が opaque path を持つなら、`#` で始まらない相対参照は失敗する
（§4.4 no scheme state step 2）。
-/
theorem run_noScheme_opaque (b : Url) (l : List Char) (ctx : PCtx) (hov : ctx.over = none)
    (hop : b.hasOpaquePath = true) (hne : ∀ c t, l = c :: t → ¬ c = '#') :
    run (some b) .noScheme l ctx = .failure := by
  cases l with
  | nil => rw [run, step]; simp [fail, hov, hop]
  | cons c t =>
    rw [run, step]
    rw [if_pos (by simpa [hop] using hne c t rfl)]
    simp [fail, hov]

/--
scheme を読み切れない入力に対する scheme start state の行き先は二つしかない。

先頭が ASCII alpha でなければその場で no scheme state へ落ち、alpha でも `:` に
届かなければ "start over" して no scheme state から読み直す。どちらでも
「no scheme state がこの入力をどう扱うか」だけが結果を決める。
-/
theorem run_schemeStart_cases (base : Option Url) (l : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (h : ¬ HasScheme l) :
    run base .schemeStart l ctx = .startOver ∨
      run base .schemeStart l ctx = run base .noScheme l ctx := by
  cases hl : l with
  | nil => right; rw [run, step]; simp [hov]
  | cons a l' =>
    rw [run, step]
    by_cases ha : isAsciiAlpha a = true
    · left
      rw [if_pos ha]
      refine run_scheme_startOver _ l' _ hov ?_
      intro pre tail he
      cases hp : pre.all isSchemeTail with
      | false => rfl
      | true => exact absurd ⟨a, pre, tail, by rw [hl, he], ha, hp⟩ h
    · right
      rw [if_neg ha]
      simp [hov]

/--
**scheme が無く base も無い入力は失敗する。**

scheme start state の行き先は "start over" か no scheme state で、
base が無ければどちらも同じところで失敗する。
-/
theorem basicUrlParse_eq_none_of_not_hasScheme {input : String}
    {toAscii : List Char → Option String} (h : ¬ HasScheme (preprocess input)) :
    basicUrlParse input none toAscii = none := by
  unfold basicUrlParse
  rcases run_schemeStart_cases none (preprocess input) { url := {}, toAscii } rfl h with hf | hf
  · rw [hf, run_noScheme_none _ _ rfl]
  · rw [hf, run_noScheme_none _ _ rfl]

/-- 対偶。**base 無しで parse が成功したなら、入力には scheme がある。** -/
theorem hasScheme_of_basicUrlParse {input : String} {u : Url}
    {toAscii : List Char → Option String} (h : basicUrlParse input none toAscii = some u) :
    HasScheme (preprocess input) := by
  rcases Classical.em (HasScheme (preprocess input)) with ht | hf
  · exact ht
  · exact absurd h (by rw [basicUrlParse_eq_none_of_not_hasScheme hf]; simp)

/--
**base が opaque path を持つなら、scheme の無い入力は `#` で始まるものしか解決できない。**

`data:x` を base にした `"/a"` や `"?q"` は失敗する。opaque path は
segment に分かれていないので、相対 path も query も継ぎ足す先が無い。
-/
theorem basicUrlParse_eq_none_of_opaque_base {input : String} {b : Url}
    {toAscii : List Char → Option String} (hop : b.hasOpaquePath = true)
    (h : ¬ HasScheme (preprocess input))
    (hne : ∀ c t, preprocess input = c :: t → ¬ c = '#') :
    basicUrlParse input (some b) toAscii = none := by
  unfold basicUrlParse
  rcases run_schemeStart_cases (some b) (preprocess input) { url := {}, toAscii } rfl h with hf | hf
  · rw [hf, run_noScheme_opaque b _ _ rfl hop hne]
  · rw [hf, run_noScheme_opaque b _ _ rfl hop hne]

/-! ## port が 16 bit に収まること -/

/--
10 進表記の値。§4.4 port state step 3.1 の "interpreted as decimal number"。

parser は左から畳み込んで積み上げるが、こちらは桁の重みで書く。
定義が違うので、両者が一致することは定理になる（`decimalOf_eq_portValue`）。
-/
def decimalOf : List Char → Nat
  | [] => 0
  | c :: rest => (digitValue c).getD 0 * 10 ^ rest.length + decimalOf rest

/-- 左畳み込みは、前に積んだぶんを桁の重みだけずらして残す。 -/
private theorem portFold_acc : ∀ (l : List Char) (acc : Nat),
    l.foldl (fun a c => a * 10 + (digitValue c).getD 0) acc
      = acc * 10 ^ l.length + l.foldl (fun a c => a * 10 + (digitValue c).getD 0) 0 := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons c rest ih =>
    intro acc
    show rest.foldl _ (acc * 10 + (digitValue c).getD 0) = _
    rw [ih (acc * 10 + (digitValue c).getD 0)]
    show _ = acc * 10 ^ (rest.length + 1) + rest.foldl _ (0 * 10 + (digitValue c).getD 0)
    rw [ih (0 * 10 + (digitValue c).getD 0), Nat.pow_succ]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc]

/-- **桁の重みで読んでも、parser の畳み込みと同じ値になる。** -/
theorem decimalOf_eq_portValue (l : List Char) : decimalOf l = portValue l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    show (digitValue c).getD 0 * 10 ^ rest.length + decimalOf rest = _
    show _ = rest.foldl (fun a x => a * 10 + (digitValue x).getD 0) (0 * 10 + (digitValue c).getD 0)
    rw [portFold_acc rest (0 * 10 + (digitValue c).getD 0), ih]
    simp [portValue]

/--
**16 bit に収まらない port は読み飛ばされず、そこで止まる。**

port state は digit を積むだけなので、止まるのは入力が尽きたときである。
そこで `portDone` が範囲を見て失敗する。`fail` は state override の有無で
「全体の失敗」と「何も書き換えない」に分かれる。
-/
theorem run_port_overflow (base : Option Url) : ∀ (l : List Char) (ctx : PCtx),
    (∀ c ∈ l, isAsciiDigit c = true) → decimalOf (ctx.buffer ++ l) > 65535 →
    run base .port l ctx = fail ctx := by
  intro l
  induction l with
  | nil =>
    intro ctx _ hbig
    simp only [List.append_nil] at hbig
    have hne : ctx.buffer ≠ [] := by
      intro he; rw [he] at hbig; simp [decimalOf] at hbig
    have hpd : portDone ctx = none := by
      unfold portDone
      rw [if_neg (by simpa using hne), if_pos (by rw [← decimalOf_eq_portValue]; exact hbig)]
    rw [run, step]
    simp only [hpd]
  | cons c l' ih =>
    intro ctx hd hbig
    rw [run, step]
    rw [if_pos (hd c (by simp))]
    rw [ih { ctx with buffer := ctx.buffer ++ [c] } (fun x hx => hd x (by simp [hx]))
      (by simpa using hbig)]
    simp [fail]

/-- base 無しの普通の parse では、範囲外の port は全体の失敗になる。 -/
theorem run_port_overflow_failure (base : Option Url) (l : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hd : ∀ c ∈ l, isAsciiDigit c = true)
    (hbig : decimalOf (ctx.buffer ++ l) > 65535) : run base .port l ctx = .failure := by
  rw [run_port_overflow base l ctx hd hbig]; simp [fail, hov]

/-!
### setter から見た失敗

state override 付きの呼び出しでは `fail` は「そこで止まる」＝「何も書き換えない」である
（`Url/Parser.lean` の `fail` の説明を参照）。`port` setter はその入口なので、
範囲外の port が黙って無視されることを入口の形で言える。
-/

/-- **範囲外の port は `port` setter で無視される。** `u.port = 80` に "99999" を代入しても変わらない。 -/
theorem setPort_of_overflow (u : Url) (v : String)
    (hd : ∀ c ∈ v.toList, isAsciiDigit c = true) (hbig : decimalOf v.toList > 65535) :
    u.setPort v = u := by
  unfold Url.setPort
  by_cases hc : u.cannotHaveCredentials = true
  · rw [if_pos hc]
  · rw [if_neg hc]
    have hnil : v.toList ≠ [] := by
      intro he; rw [he] at hbig; simp [decimalOf] at hbig
    rw [if_neg (by simpa [String.isEmpty] using hnil)]
    unfold basicUrlParseOverride
    rw [show stripTabNewline v.toList = v.toList from by
      refine List.filter_eq_self.mpr (fun c hc => ?_)
      have := hd c hc
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq] at this
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Bool.or_eq_false_iff]
      omega]
    simp only [SOverride.start]
    rw [run_port_overflow none v.toList { url := u, over := some .port } hd (by simpa using hbig)]
    simp [fail]

/-! ## 証人

定理が空虚でないこと、つまり前提を満たす入力が実際にあることを例で固定する。
-/

/-- `:` を含まない入力に scheme は無い。 -/
theorem not_hasScheme_of_no_colon {l : List Char} (h : ∀ c ∈ l, ¬ c = ':') : ¬ HasScheme l := by
  rintro ⟨a, pre, tail, he, -, -⟩
  refine h ':' ?_ rfl
  rw [he]; simp

/-- base 無しで `"/a/b"` は解決できない。 -/
example : basicUrlParse "/a/b" none = none :=
  basicUrlParse_eq_none_of_not_hasScheme (not_hasScheme_of_no_colon (by decide))

/-- opaque path を持つ base に対しても、`#` で始まらない相対参照は解決できない。 -/
example : basicUrlParse "/a" (some { scheme := "data", path := .opaque "x" }) = none :=
  basicUrlParse_eq_none_of_opaque_base rfl
    (not_hasScheme_of_no_colon (by decide)) (by rintro c t he; cases he; decide)

/-- `port` setter は 65536 を無視する。 -/
example : (({ scheme := "http", host := some (.domain "a"), port := some 8080 } : Url).setPort
    "65536") = { scheme := "http", host := some (.domain "a"), port := some 8080 } :=
  setPort_of_overflow _ _ (by decide) (by decide)

end Url.Spec
