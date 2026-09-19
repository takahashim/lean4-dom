import Url.ApiValid

/-!
# canonical form と正規形の道具
-/

namespace Url

open Infra

set_option maxHeartbeats 1000000

/-! ## canonical form

parser が返す record の形。これを満たさない record には `parse ∘ serialize` は成り立たない
（上の表の三つがその例である）。`checkValidUrl` と同じく、まず boolean として書いて
WPT の全 case で実行時に確かめる。証明はこれを仮定として進める。
-/

/-- scheme が parser の書く形か。先頭は ASCII 小文字 alpha、残りは alphanumeric か `+` `-` `.`。 -/
def canonicalScheme (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    isAsciiLowerAlpha c &&
      rest.all fun x =>
        (isAsciiDigit x || isAsciiLowerAlpha x) || x == '+' || x == '-' || x == '.'

/--
その set の文字を含まないこと。

percent-encode の出力がこれを満たす。`%` も 16 進の数字もどの set にも入らないので、
encode した結果をもう一度 encode しても変わらない（`utf8PercentEncode_id`）。
-/
def encodedWith (set : Char → Bool) (s : String) : Bool :=
  s.toList.all fun c => !set c

/--
**parser が返す record の形。**

`ValidUrl` は §4.1 の条件で、こちらは「parse し直しても同じ record になる」ための条件である。
重なりは無く、どちらも他方を含まない。
-/
def canonicalUrl (u : Url) (toAscii : List Char → Option String := asciiDomainToASCII) : Bool :=
  canonicalScheme u.scheme &&
  -- 既定 port は書かない（`portOf` が null にする）
  (match u.port with | none => true | some p => defaultPort u.scheme != some p) &&
  encodedWith userinfoSet u.username &&
  encodedWith userinfoSet u.password &&
  (match u.query with
   | none => true
   | some q => encodedWith (if u.isSpecial then specialQuerySet else querySet) q) &&
  (match u.fragment with | none => true | some f => encodedWith fragmentSet f) &&
  (match u.path with
   | .opaque o =>
     -- `?` と `#` は opaque path state の出口なので、中には入らない。
     -- 末尾の space は前処理が落とすので、parser は `%20` にしている。
     encodedWith c0ControlSet o && !(o.toList.getLast? == some ' ') &&
       o.toList.all (fun c => c != '?' && c != '#') &&
       -- 先頭の `/` は path or authority state へ行ってしまう。
       !(o.toList.head? == some '/')
   | .list segs =>
     segs.all fun seg =>
       encodedWith pathSet seg && !isSingleDot seg.toList && !isDoubleDot seg.toList &&
         -- special な URL では `\\` も区切りである（`pathSet` は encode しない）。
         (!u.isSpecial || seg.toList.all (fun c => c != '\\'))) &&
  -- path が空だと serialize しても跡が残らない（host が null のとき）。
  -- special な URL も同じで、`http://h` を読み直すと segment が一つ（空）できる。
  -- parser はこの二つの場合に必ず segment を一つ以上書く。
  (match u.host, u.path with | none, .list [] => false | _, _ => true) &&
  (!u.isSpecial || (match u.path with | .list [] => false | _ => true)) &&
  -- host は serialize してから読み直すと同じもの
  (match u.host with
   | none => true
   -- empty host は host parser の出力ではない（parser が直に書く）。
   | some .empty => true
   | some h => hostParser toAscii (hostSerializer h).toList (!u.isSpecial) == some h) &&
  -- file URL の `localhost` は parser が empty host に直す。
  (match u.host with
   | some h => u.scheme != "file" || hostSerializer h != "localhost"
   | none => true) &&
  -- file URL の先頭 segment の `c|` は parser が `c:` に直す。
  (match u.path with
   | .list (seg :: _) =>
     u.scheme != "file" || !isWindowsDrive seg.toList || isNormalizedWindowsDrive seg.toList
   | _ => true) &&
  -- special な URL の host は null でない（authority state が必ず host を書く）。
  (!u.isSpecial || u.host.isSome) &&
  -- host が空なら credentials は持てない（authority state が `@` の後で失敗する）。
  (u.host != some Host.empty || !u.includesCredentials)

/-- 先頭が落ちない文字なら `dropWhile` は何もしない。 -/
theorem dropWhile_of_head : ∀ (l : List Char) (p : Char → Bool), (∀ c ∈ l.head?, p c = false) →
    List.dropWhile p l = l
  | [], _, _ => rfl
  | c :: rest, p, h => by
    rw [List.dropWhile_cons, if_neg (by rw [h c rfl]; simp)]

/--
前後が C0 control でも space でもなく、tab も newline も無ければ、前処理は何もしない。

前後だけで済むのは `dropWhile` が最初の一つで止まるからである。
-/
theorem preprocess_eq_self {str : String}
    (hh : ∀ c ∈ str.toList.head?, isC0ControlOrSpace c = false)
    (hl : ∀ c ∈ str.toList.reverse.head?, isC0ControlOrSpace c = false)
    (hnt : ∀ c ∈ str.toList, c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D) :
    preprocess str = str.toList := by
  unfold preprocess
  simp only [dropWhile_of_head str.toList isC0ControlOrSpace hh]
  rw [dropWhile_of_head str.toList.reverse isC0ControlOrSpace hl, List.reverse_reverse]
  exact stripTabNewline_eq_self hnt

/-- scheme に使える文字。§4.4 scheme state の step 1 である。 -/
def schemeChar (c : Char) : Bool :=
  isAsciiAlphanumeric c || c == '+' || c == '-' || c == '.'

/-- scheme state は scheme の文字を小文字にして buffer に積む。 -/
theorem run_scheme_prefix (base : Option Url) : ∀ (pre rest : List Char) (ctx : PCtx),
    (∀ c ∈ pre, schemeChar c = true) →
    run base .scheme (pre ++ rest) ctx
      = run base .scheme rest { ctx with buffer := ctx.buffer ++ pre.map asciiLowerChar } := by
  intro pre
  induction pre with
  | nil => intro rest ctx _; simp
  | cons c tail ih =>
    intro rest ctx hd
    simp only [List.cons_append]
    rw [run, step, if_pos (by have := hd c (by simp); simpa [schemeChar] using this)]
    rw [ih rest { ctx with buffer := ctx.buffer ++ (asciiLowercase (String.ofList [c])).toList }
        (fun x hx => hd x (by simp [hx]))]
    simp [asciiLowercase]

/--
scheme state の `:`：special でない scheme で、続きが `/` で始まらなければ opaque path へ。

仕様 §4.4 scheme state の step 2.6 である。
-/
theorem run_scheme_opaque (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none)
    (hf : ¬(String.ofList ctx.buffer = "file"))
    (hsp : isSpecialScheme (String.ofList ctx.buffer) = false)
    (hr : ∀ r ∈ rest.head?, ¬r = '/') :
    run base .scheme (':' :: rest) ctx
      = run base .opaquePath rest
          { ctx with
            url := { ctx.url with scheme := String.ofList ctx.buffer, path := .opaque "" }
            buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide), if_pos (by decide)]
  simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hf), if_neg (by simp [Url.isSpecial, hsp]),
    if_neg (by simp [Url.isSpecial, hsp])]
  cases rest with
  | nil => rfl
  | cons r t =>
    have hne : ¬r = '/' := hr r (by simp)
    split
    · next rest2 he => simp only [List.cons.injEq] at he; exact absurd he.1 hne
    · rfl

/-- scheme に使える文字は tab でも newline でもない。 -/
theorem schemeChar_ne_tab {c : Char} (h : schemeChar c = true) :
    c.toNat ≠ 0x09 ∧ c.toNat ≠ 0x0A ∧ c.toNat ≠ 0x0D := by
  simp only [schemeChar, isAsciiAlphanumeric, isAsciiDigit, isAsciiAlpha, isAsciiUpperAlpha,
    isAsciiLowerAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (((h | h | h) | h) | h) | h <;> first | omega | (subst h; decide)

/-- 末尾の一文字。`preprocess` が見るのは後ろの `dropWhile` の最初の一つだけである。 -/
theorem reverse_head_mid (l1 : List Char) (c : Char) (l2 : List Char) :
    (l1 ++ c :: l2).reverse.head? = if l2.isEmpty then some c else l2.reverse.head? := by
  cases hx : l2 with
  | nil => simp
  | cons d t => simp [List.reverse_append]

end Url
