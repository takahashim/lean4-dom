import Url.Parser

/-!
# state 遷移の優先順

仕様の各 state は条件を**並べた順に**見る。同じ文字に当てはまる条件が複数あるとき、
どれが先かで結果が変わる。ここではその順序を、当てはまる入力を両方持つ場面について
名前の付いた定理にしておく。

DOM 側の `Dom/Properties/PreInsertValidity.lean` の
`ensurePreInsertionValidity_step1` / `_step2` / `_step3` と同じ役割である。
順序は仕様を読み違えても差分テストで見つかりにくい（片方の条件が先に当たるだけで、
どちらも「もっともらしい」結果を返す）ので、条件ごとに固定しておく価値がある。
-/

namespace Url.Spec

open Infra Url

/--
**scheme state は `file` を special より先に見る。**

`file` は special scheme でもあるので、順序が逆だと `file:` が
special authority slashes state へ行ってしまい、`file://` を要求するようになる。
-/
theorem scheme_file_before_special (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hbuf : ctx.buffer = "file".toList) :
    run base .scheme (':' :: rest) ctx
      = run base .file rest { ctx with url := { ctx.url with scheme := "file" }, buffer := [] } := by
  rw [run, step]
  rw [if_neg (by decide)]
  rw [if_pos (by decide)]
  rw [if_neg (by simp [hov])]
  rw [if_pos (by simp [hbuf])]
  simp [hbuf]

/--
**host state は bracket の中の `:` を port の区切りにしない。**

IPv6 address は `:` を含むので、`insideBrackets` の判定が先でないと
`[::1]` が host と port に割れてしまう。
-/
theorem host_colon_inside_brackets (base : Option Url) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hib : ctx.insideBrackets = true) :
    run base .host (':' :: rest) ctx
      = run base .host rest
          { ctx with buffer := ctx.buffer ++ [':'], insideBrackets := true } := by
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_neg (by simp [hib])]
  rw [if_neg (by cases h : ctx.url.isSpecial <;> simp [isTerminator])]
  simp [hib]

/--
**special な URL の空の host は、host parser を通る前に失敗する。**

順序が逆だと空文字列が domain parser に渡り、そこが空を通してしまえば
`https://` が host 無しで通ってしまう。
-/
theorem host_empty_special_fails (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hov : ctx.over = none) (hsp : ctx.url.isSpecial = true)
    (hbuf : ctx.buffer = []) (hcol : ¬ c = some ':') (ht : isTerminator true c = true) :
    step base .host c rest input ctx = .failure := by
  cases c with
  | none =>
    rw [step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by simp)]
    rw [if_pos (by simpa [hsp] using ht)]
    rw [if_pos (by simp [hsp, hbuf])]
    simp [fail, hov]
  | some ch =>
    rw [step]
    rw [if_neg (by simp [hov])]
    rw [if_neg (by
      have hb : (some ch == some ':') = false := by simpa using hcol
      simp [hb])]
    rw [if_pos (by simpa [hsp] using ht)]
    rw [if_pos (by simp [hsp, hbuf])]
    simp [fail, hov]

/--
**port state は digit でも terminator でもない文字を読み飛ばさない。**

`http://h:8o80/` は port を `8` で打ち切らずに失敗する。
-/
theorem port_rejects_other (base : Option Url) (c : Char) (rest : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hd : isAsciiDigit c = false)
    (ht : isTerminator ctx.url.isSpecial (some c) = false) :
    run base .port (c :: rest) ctx = .failure := by
  rw [run, step]
  rw [if_neg (by simp [hd])]
  rw [if_neg (by simp [ht, hov])]
  simp [fail, hov]

/--
**path state は state override があるとき `?` と `#` を segment の文字にする。**

`pathname` setter に `"a?b"` を渡しても query は動かない。
-/
theorem path_override_keeps_query_char (base : Option Url) (ch : Char) (rest input : List Char)
    (ctx : PCtx) (hov : ctx.over.isSome = true) (hq : ch = '?' ∨ ch = '#') :
    step base .path (some ch) rest input ctx
      = run base .path rest { ctx with buffer := ctx.buffer ++ (encChar pathSet ch).toList } := by
  rw [step]
  rw [if_neg (by
    rcases hq with rfl | rfl <;>
      simp [show ctx.over.isNone = false from by
        cases h : ctx.over <;> simp_all])]

/--
**file host state は Windows drive letter を host として読む前に path へ回す。**

`file:///c:/path` の `c:` は host ではない。順序が逆だと `c` が host になる。
-/
theorem fileHost_drive_before_host (base : Option Url) (c : Cp) (rest input : List Char)
    (ctx : PCtx) (hov : ctx.over = none) (hd : isWindowsDrive ctx.buffer = true)
    (ht : c = none ∨ c = some '/' ∨ c = some '\\' ∨ c = some '?' ∨ c = some '#') :
    step base .fileHost c rest input ctx = run base .path input ctx := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    (rw [step]; rw [if_pos (by simp)]; rw [if_pos (by simp [hov, hd])])

/--
**path start state が `\` を `/` と同じに扱うのは special な URL だけである。**

special でなければ `\` は segment の文字として読み直される。
-/
theorem pathStart_backslash_special (base : Option Url) (rest input : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = true) :
    step base .pathStart (some '\\') rest input ctx = run base .path rest ctx := by
  rw [step]
  rw [if_pos hsp]
  rw [if_pos (by simp)]

/-- special でない URL では `\` は segment の文字である（`pathStart_backslash_special` の対）。 -/
theorem pathStart_backslash_not_special (base : Option Url) (rest input : List Char) (ctx : PCtx)
    (hsp : ctx.url.isSpecial = false) : step base .pathStart (some '\\') rest input ctx
      = run base .path input ctx := by
  rw [step]
  rw [if_neg (by simp [hsp])]
  rw [if_neg (by simp)]
  rw [if_neg (by simp)]
  simp

end Url.Spec
