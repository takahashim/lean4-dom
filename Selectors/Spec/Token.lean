import Infra.Ascii
import Selectors.Token

/-!
# CSS tokenizer の関係仕様（CSS Syntax Level 3 §3.3・§4）

`Selectors/Token.lean` の tokenizer を、**実行関数を呼ばずに**関係として書く。
版は `docs/selectors-spec-version.md` に固定した Editor's Draft で、§ 番号もその版のものである。

規則は本文のアルゴリズムの分岐に一対一で対応させる。差分テストで tokenizer に起因する
不一致が出たとき、どの § のどの分岐で割れたかを名指しできるようにするためである。

使ってよいのは code point の数値範囲と list の添字だけで、`Selectors/Token.lean` の
関数（`isIdentStart`・`startsValidEscape` など）は呼ばない。`Selectors/Token.lean` から使うのは
token の型 `Token` / `Num` だけである。code point の分類も
`Infra.Ascii` ではなく CSS Syntax §4.2 の定義から書き写す。

`Selectors/Spec/TokenSound.lean` で実行関数がこれを満たすことを、
`Selectors/Spec/TokenDeterministic.lean` で関係が結果を一意に決めることを示す。

## 本文との差（`Selectors/Token.lean` 冒頭と同じ）

* surrogate を U+FFFD にする前処理は無い。Lean の `Char` は surrogate を持てない。
* `<url-token>` を作らない（§4.3.4 の `url(` の分岐が無い）。
* number は整数のときだけ本文どおりの値を持つ（§4.3.13）。
* percentage token が type flag を持つ（§4.3.3）。
-/

namespace Selectors.Spec

/-! ## code point の分類（§4.2） -/

/-- digit：U+0030..U+0039。 -/
def Digit (c : Char) : Prop := 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39

/-- hex digit：digit、U+0041..U+0046、U+0061..U+0066。 -/
def HexDigit (c : Char) : Prop :=
  Digit c ∨ (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46) ∨ (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x66)

/-- letter：uppercase letter（U+0041..U+005A）か lowercase letter（U+0061..U+007A）。 -/
def Letter (c : Char) : Prop :=
  (0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A) ∨ (0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A)

/-- non-ASCII ident code point。本文の 15 項目をそのまま並べる（範囲はすべて両端を含む）。 -/
def NonAsciiIdentCp (c : Char) : Prop :=
  let n := c.toNat
  n = 0xB7 ∨ (0xC0 ≤ n ∧ n ≤ 0xD6) ∨ (0xD8 ≤ n ∧ n ≤ 0xF6) ∨ (0xF8 ≤ n ∧ n ≤ 0x37D) ∨
    (0x37F ≤ n ∧ n ≤ 0x1FFF) ∨ n = 0x200C ∨ n = 0x200D ∨ n = 0x203F ∨ n = 0x2040 ∨
    (0x2070 ≤ n ∧ n ≤ 0x218F) ∨ (0x2C00 ≤ n ∧ n ≤ 0x2FEF) ∨ (0x3001 ≤ n ∧ n ≤ 0xD7FF) ∨
    (0xF900 ≤ n ∧ n ≤ 0xFDCF) ∨ (0xFDF0 ≤ n ∧ n ≤ 0xFFFD) ∨ 0x10000 ≤ n

/-- ident-start code point：letter、non-ASCII ident code point、U+005F LOW LINE。 -/
def IdentStartCp (c : Char) : Prop := Letter c ∨ NonAsciiIdentCp c ∨ c = '_'

/-- ident code point：ident-start code point、digit、U+002D HYPHEN-MINUS。 -/
def IdentCp (c : Char) : Prop := IdentStartCp c ∨ Digit c ∨ c = '-'

/-- newline：U+000A LINE FEED。CR と FF は前処理で LF になっている。 -/
def Newline (c : Char) : Prop := c = '\n'

/-- whitespace：newline、U+0009 CHARACTER TABULATION、U+0020 SPACE。 -/
def Whitespace (c : Char) : Prop := Newline c ∨ c = '\t' ∨ c = ' '

/-! ## 前処理（§3.3 "filter code points"） -/

/--
`Preprocessed input out`：`input` を filter した結果が `out`。

CR・FF・CRLF の組を LF 一つに、NULL を U+FFFD にする。
-/
inductive Preprocessed : List Char → List Char → Prop where
  | nil : Preprocessed [] []
  /-- CR に LF が続く組は LF 一つ。 -/
  | crlf {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\r' :: '\n' :: rest) ('\n' :: out)
  /-- LF が続かない CR は LF。 -/
  | cr {rest out : List Char} (hn : ∀ r, rest ≠ '\n' :: r) (h : Preprocessed rest out) :
      Preprocessed ('\r' :: rest) ('\n' :: out)
  /-- FF は LF。 -/
  | ff {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\x0c' :: rest) ('\n' :: out)
  /-- NULL は U+FFFD。 -/
  | null {rest out : List Char} (h : Preprocessed rest out) :
      Preprocessed ('\x00' :: rest) ('\uFFFD' :: out)
  /-- それ以外はそのまま。 -/
  | other {c : Char} {rest out : List Char} (hc : c ≠ '\r' ∧ c ≠ '\x0c' ∧ c ≠ '\x00')
      (h : Preprocessed rest out) :
      Preprocessed (c :: rest) (c :: out)

/-! ## 先読みの判定（§4.3.8–§4.3.10）

本文は「二つ（三つ）の code point」について判定する。入力が尽きた先は EOF code point で、
ここでは `none` で表す。入力の流れに対して呼ぶときは、先頭からの添字で取り出す。
-/

/-- `o` が digit である。EOF は digit でない。 -/
def DigitAt (o : Option Char) : Prop := ∃ d, o = some d ∧ Digit d

/-- §4.3.8 "check if two code points are a valid escape"。 -/
def ValidEscape (a b : Option Char) : Prop :=
  a = some '\\' ∧ ∀ d, b = some d → ¬ Newline d

/--
§4.3.9 "check if three code points would start an ident sequence"。

本文は先頭の code point で場合分けする。`-` と `\` は ident-start code point ではないので、
三つの場合を `∨` で並べても排他である。
-/
def WouldStartIdent (a b c : Option Char) : Prop :=
  (a = some '-' ∧ ((∃ d, b = some d ∧ (IdentStartCp d ∨ d = '-')) ∨ ValidEscape b c)) ∨
  (∃ d, a = some d ∧ IdentStartCp d) ∨
  (a = some '\\' ∧ ValidEscape a b)

/-- §4.3.10 "check if three code points would start a number"。 -/
def WouldStartNumber (a b c : Option Char) : Prop :=
  ((a = some '+' ∨ a = some '-') ∧ (DigitAt b ∨ (b = some '.' ∧ DigitAt c))) ∨
  (a = some '.' ∧ DigitAt b) ∨
  DigitAt a

/-- 入力の流れの先頭が valid escape で始まる。 -/
def StartsValidEscape (l : List Char) : Prop := ValidEscape l[0]? l[1]?

/-- 入力の流れの先頭が ident sequence を始める。 -/
def StartsIdent (l : List Char) : Prop := WouldStartIdent l[0]? l[1]? l[2]?

/-- 入力の流れの先頭が number を始める。 -/
def StartsNumber (l : List Char) : Prop := WouldStartNumber l[0]? l[1]? l[2]?

/-! ## escape（§4.3.7 "consume an escaped code point"） -/

/-- hex digit が表す値。 -/
def HexDigitValue (c : Char) : Nat :=
  if 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 then c.toNat - 0x30
  else if 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46 then c.toNat - 0x41 + 10
  else c.toNat - 0x61 + 10

/-- `HexNumber ds v`：hex digit の並び `ds` を 16 進として読んだ値が `v`（上の桁から読む）。 -/
inductive HexNumber : List Char → Nat → Prop where
  | nil : HexNumber [] 0
  | snoc {ds : List Char} {v : Nat} (d : Char) (h : HexNumber ds v) :
      HexNumber (ds ++ [d]) (v * 16 + HexDigitValue d)

/--
`EscapedValue v c`：escape の 16 進の値 `v` が表す code point が `c`。
0・surrogate・最大値 U+10FFFF を超える値は U+FFFD。
-/
inductive EscapedValue : Nat → Char → Prop where
  | replacement {v : Nat} (h : v = 0 ∨ (0xD800 ≤ v ∧ v ≤ 0xDFFF) ∨ 0x10FFFF < v) :
      EscapedValue v '\uFFFD'
  | scalar {v : Nat} {c : Char} (h : ¬ (v = 0 ∨ (0xD800 ≤ v ∧ v ≤ 0xDFFF) ∨ 0x10FFFF < v))
      (hc : c.toNat = v) :
      EscapedValue v c

/--
`Escape input c rest`：逆斜線の後ろの `input` から escape を一つ読むと `c` になり、残りが `rest`。

hex digit は 1〜6 個を最長一致で読み、直後の whitespace を一つだけ一緒に読む。
-/
inductive Escape : List Char → Char → List Char → Prop where
  /-- hex digit の並び。後ろに whitespace があれば一つ読む。 -/
  | hex {input ds rest rest' : List Char} {v : Nat} {c : Char}
      (hsplit : input = ds ++ rest) (hne : ds ≠ []) (hlen : ds.length ≤ 6) (hall : ∀ d ∈ ds, HexDigit d)
      (hmax : ds.length = 6 ∨ ∀ d, rest[0]? = some d → ¬ HexDigit d)
      (hws : (∃ w, rest = w :: rest' ∧ Whitespace w) ∨
        ((∀ w, rest[0]? = some w → ¬ Whitespace w) ∧ rest' = rest))
      (hv : HexNumber ds v) (hc : EscapedValue v c) :
      Escape input c rest'
  /-- 入力が尽きた。U+FFFD。 -/
  | eof : Escape [] '\uFFFD' []
  /-- hex digit でない code point はそれ自身。 -/
  | other {c : Char} {rest : List Char} (h : ¬ HexDigit c) : Escape (c :: rest) c rest

/-! ## ident sequence（§4.3.12 "consume an ident sequence"） -/

/--
`IdentSeq input result rest`：`input` から ident sequence を最長に読むと `result`、残りが `rest`。

先頭の検査（§4.3.9）はしない。本文と同じく、呼び出す側の責任である。
-/
inductive IdentSeq : List Char → List Char → List Char → Prop where
  /-- ident code point を足す。 -/
  | cp {c : Char} {rest r out : List Char} (h : IdentCp c) (ih : IdentSeq rest r out) :
      IdentSeq (c :: rest) (c :: r) out
  /-- valid escape なら escape を読んで足す。逆斜線は ident code point ではない。 -/
  | escape {rest rest' r out : List Char} {e : Char}
      (hv : StartsValidEscape ('\\' :: rest)) (he : Escape rest e rest')
      (ih : IdentSeq rest' r out) :
      IdentSeq ('\\' :: rest) (e :: r) out
  /-- どちらでもなければ止まる。入力が尽きた場合も含む。 -/
  | stop {l : List Char} (hc : ∀ c, l[0]? = some c → ¬ IdentCp c)
      (he : ¬ StartsValidEscape l) :
      IdentSeq l [] l

/-! ## string token（§4.3.5 "consume a string token"） -/

/--
`StringRun e input value bad rest`：開き引用符の後ろの `input` を、終わりの code point `e` まで読む。
`value` は値、`bad` は `<bad-string-token>` になったか、`rest` は残り。

本文の分岐の順序どおり、終わりの code point の判定が先に来る。他の規則はすべて `c ≠ e` を持つ。
-/
inductive StringRun (e : Char) : List Char → List Char → Bool → List Char → Prop where
  /-- 終わりの code point。 -/
  | close {rest : List Char} : StringRun e (e :: rest) [] false rest
  /-- 入力が尽きた（parse error）。それまでの値で string token になる。 -/
  | eof : StringRun e [] [] false []
  /-- 改行（parse error）。改行は読み直しに残し、bad-string token になる。 -/
  | newline {rest : List Char} (he : '\n' ≠ e) :
      StringRun e ('\n' :: rest) [] true ('\n' :: rest)
  /-- 逆斜線で入力が尽きた。何もしない。 -/
  | backslashEof (he : '\\' ≠ e) : StringRun e ['\\'] [] false []
  /-- 逆斜線と改行は読み飛ばす（行の継続）。 -/
  | backslashNewline {rest v : List Char} {b : Bool} {out : List Char} (he : '\\' ≠ e)
      (ih : StringRun e rest v b out) :
      StringRun e ('\\' :: '\n' :: rest) v b out
  /-- 逆斜線のあとが改行でなければ escape。 -/
  | backslashEscape {d : Char} {rest rest' v : List Char} {x : Char} {b : Bool} {out : List Char}
      (he : '\\' ≠ e) (hd : d ≠ '\n') (hx : Escape (d :: rest) x rest')
      (ih : StringRun e rest' v b out) :
      StringRun e ('\\' :: d :: rest) (x :: v) b out
  /-- それ以外は値に足す。 -/
  | other {c : Char} {rest v : List Char} {b : Bool} {out : List Char}
      (he : c ≠ e) (hn : c ≠ '\n') (hb : c ≠ '\\') (ih : StringRun e rest v b out) :
      StringRun e (c :: rest) (c :: v) b out

/-- `StringTok e input t rest`：string token を読むと `t`、残りが `rest`。 -/
def StringTok (e : Char) (input : List Char) (t : Token) (rest : List Char) : Prop :=
  ∃ v b, StringRun e input v b rest ∧
    t = if b then Token.badString else Token.string (String.ofList v)

/-! ## comment（§4.3.2 "consume comments"） -/

/-- `s` の中に `*/` が現れない。 -/
def NoCommentEnd (s : List Char) : Prop := ∀ x y, s ≠ x ++ '*' :: '/' :: y

/--
`CommentBody input rest`：`/*` の後ろから、最初の `*/` まで（それも含めて）読むと残りが `rest`。
`*/` が無ければ入力の終わりまで読む（parse error）。
-/
def CommentBody (input rest : List Char) : Prop :=
  (∃ pre, input = pre ++ '*' :: '/' :: rest ∧ NoCommentEnd pre) ∨
  (NoCommentEnd input ∧ rest = [])

/-- `Comments input rest`：先頭の comment をすべて読み飛ばすと残りが `rest`。 -/
inductive Comments : List Char → List Char → Prop where
  /-- `/*` で始まらなければ何もしない。 -/
  | done {l : List Char} (h : ∀ r, l ≠ '/' :: '*' :: r) : Comments l l
  /-- comment を一つ読み、本文の "Return to the start of this step" に戻る。 -/
  | comment {rest rest' out : List Char} (hb : CommentBody rest rest') (ih : Comments rest' out) :
      Comments ('/' :: '*' :: rest) out

/-! ## number（§4.3.13 "consume a number"）

本文は number part と exponent part を組み立てて十進の値を作る。model は
**整数のときだけ値を持つ**（`Selectors/Token.lean` 冒頭の差）。ここでも `value` は
符号と整数部の digit から作る。type flag が "integer" なら本文の値と一致し、
"number" なら本文の値とは違うが、`<an+b>` は整数しか受け付けないので使われない。
-/

/-- `DecimalNumber ds v`：digit の並び `ds` を十進として読んだ値が `v`。 -/
inductive DecimalNumber : List Char → Nat → Prop where
  | nil : DecimalNumber [] 0
  | snoc {ds : List Char} {v : Nat} (d : Char) (h : DecimalNumber ds v) :
      DecimalNumber (ds ++ [d]) (v * 10 + (d.toNat - 0x30))

/-- `DigitRun input ds rest`：`input` の先頭から digit を続く限り読むと `ds`、残りが `rest`。 -/
def DigitRun (input ds rest : List Char) : Prop :=
  input = ds ++ rest ∧ (∀ d ∈ ds, Digit d) ∧ ¬ DigitAt rest[0]?

/-- 符号。`+` か `-` なら読んで sign character にする。 -/
def SignPart (input : List Char) (sign : Option Char) (rest : List Char) : Prop :=
  (∃ c, input = c :: rest ∧ (c = '+' ∨ c = '-') ∧ sign = some c) ∨
  (input[0]? ≠ some '+' ∧ input[0]? ≠ some '-' ∧ sign = none ∧ rest = input)

/-- 小数部が始まる：`.` に digit が続く。 -/
def FractionStart (l : List Char) : Prop := l[0]? = some '.' ∧ DigitAt l[1]?

/-- 小数部。始まるなら `.` と digit の並びを読み、type を "number" にする。 -/
def FractionPart (input : List Char) (frac : Bool) (rest : List Char) : Prop :=
  (∃ r ds, FractionStart input ∧ input = '.' :: r ∧ DigitRun r ds rest ∧ frac = true) ∨
  (¬ FractionStart input ∧ frac = false ∧ rest = input)

/-- 指数部が始まる：`E`/`e` に、（`+`/`-` を挟んで）digit が続く。 -/
def ExponentStart (l : List Char) : Prop :=
  (l[0]? = some 'E' ∨ l[0]? = some 'e') ∧
    (DigitAt l[1]? ∨ ((l[1]? = some '+' ∨ l[1]? = some '-') ∧ DigitAt l[2]?))

/-- 指数部。始まるなら `E`/`e`、符号、digit の並びを読み、type を "number" にする。 -/
def ExponentPart (input : List Char) (expo : Bool) (rest : List Char) : Prop :=
  (∃ e r r' ds, ExponentStart input ∧ input = e :: r ∧
    (((r[0]? = some '+' ∨ r[0]? = some '-') ∧ r' = r.tail) ∨
      (r[0]? ≠ some '+' ∧ r[0]? ≠ some '-' ∧ r' = r)) ∧
    DigitRun r' ds rest ∧ expo = true) ∨
  (¬ ExponentStart input ∧ expo = false ∧ rest = input)

/-- `Number input n rest`：§4.3.13 の手順を順に踏むと `n`、残りが `rest`。 -/
def Number (input : List Char) (n : Num) (rest : List Char) : Prop :=
  ∃ sign s1 ds s2 frac s3 expo v,
    SignPart input sign s1 ∧ DigitRun s1 ds s2 ∧ FractionPart s2 frac s3 ∧
    ExponentPart s3 expo rest ∧ DecimalNumber ds v ∧
    n = { isInteger := !frac && !expo,
          value := if sign = some '-' then -(v : Int) else (v : Int),
          sign := sign }

/-! ## numeric token・ident-like token（§4.3.3・§4.3.4） -/

/--
§4.3.3 "consume a numeric token"。

本文との差：本文の percentage token は type flag を持たないが、model は number の
`Num` をそのまま持たせる。selector で percentage token が意味を持つ場所は無い。
-/
def NumericTok (input : List Char) (t : Token) (rest : List Char) : Prop :=
  ∃ n r, Number input n r ∧
    ((StartsIdent r ∧ ∃ u, IdentSeq r u rest ∧ t = Token.dimension n (String.ofList u)) ∨
     (¬ StartsIdent r ∧ r = '%' :: rest ∧ t = Token.percentage n) ∨
     (¬ StartsIdent r ∧ r[0]? ≠ some '%' ∧ t = Token.number n ∧ rest = r))

/--
§4.3.4 "consume an ident-like token"。

本文との差：`url(` を特別扱いしない（`<url-token>` を作らない）。`url(` は function token になる。
-/
def IdentLikeTok (input : List Char) (t : Token) (rest : List Char) : Prop :=
  ∃ s r, IdentSeq input s r ∧
    ((r = '(' :: rest ∧ t = Token.function (String.ofList s)) ∨
     (r[0]? ≠ some '(' ∧ t = Token.ident (String.ofList s) ∧ rest = r))

/-! ## token を一つ読む（§4.3.1 "consume a token"）

`TokenAt c rest t out`：comment を読み飛ばしたあと一文字 `c` を読み、後ろが `rest` のとき、
token `t` を作って残りが `out`。規則は本文の switch の分岐に一対一で対応する。

本文との差：`unicode ranges allowed` は常に false なので、`U`/`u` は ident-start code point の
分岐に入る。入力が尽きたとき（EOF token）は `Tokenizes` の側で扱う。
-/

/-- 一文字がそのまま token になる code point。 -/
inductive Punct : Char → Token → Prop where
  | lparen : Punct '(' Token.lparen
  | rparen : Punct ')' Token.rparen
  | comma : Punct ',' Token.comma
  | colon : Punct ':' Token.colon
  | semicolon : Punct ';' Token.semicolon
  | lbracket : Punct '[' Token.lbracket
  | rbracket : Punct ']' Token.rbracket
  | lbrace : Punct '{' Token.lbrace
  | rbrace : Punct '}' Token.rbrace

/-- `rest` の先頭の whitespace を続く限り読むと残りが `out`。 -/
def WhitespaceRun (rest out : List Char) : Prop :=
  ∃ ws, rest = ws ++ out ∧ (∀ w ∈ ws, Whitespace w) ∧ ∀ x, out[0]? = some x → ¬ Whitespace x

/-- switch のどの名前付きの分岐にも当たらない code point（本文の "anything else"）。 -/
def OtherCp (c : Char) : Prop :=
  ¬ Whitespace c ∧ ¬ Digit c ∧ ¬ IdentStartCp c ∧
    c ∉ ['"', '#', '\'', '(', ')', '+', ',', '-', '.', ':', ';', '<', '@', '[', '\\', ']', '{', '}']

inductive TokenAt : Char → List Char → Token → List Char → Prop where
  /-- whitespace：続く whitespace をすべて読む。 -/
  | whitespace {c : Char} {rest out : List Char} (hc : Whitespace c) (hw : WhitespaceRun rest out) :
      TokenAt c rest Token.whitespace out
  /-- `"` と `'`：string token。 -/
  | string {c : Char} {rest out : List Char} {t : Token} (hc : c = '"' ∨ c = '\'')
      (hs : StringTok c rest t out) :
      TokenAt c rest t out
  /-- `#` に ident code point か valid escape が続く：hash token。type flag は §4.3.9 で決める。 -/
  | hash {rest s out : List Char} {isId : Bool}
      (h : (∃ x, rest[0]? = some x ∧ IdentCp x) ∨ StartsValidEscape rest)
      (hid : isId = true ↔ StartsIdent rest) (hs : IdentSeq rest s out) :
      TokenAt '#' rest (Token.hash (String.ofList s) isId) out
  /-- `#` のそれ以外：delim。 -/
  | hashDelim {rest : List Char}
      (h : ¬ ((∃ x, rest[0]? = some x ∧ IdentCp x) ∨ StartsValidEscape rest)) :
      TokenAt '#' rest (Token.delim '#') rest
  /-- 一文字の token。 -/
  | punct {c : Char} {rest : List Char} {t : Token} (h : Punct c t) : TokenAt c rest t rest
  /-- `+`・`-`・`.` が number を始める：numeric token。 -/
  | numericSign {c : Char} {rest out : List Char} {t : Token} (hc : c = '+' ∨ c = '-' ∨ c = '.')
      (hn : StartsNumber (c :: rest)) (ht : NumericTok (c :: rest) t out) :
      TokenAt c rest t out
  /-- `+` と `.` のそれ以外：delim。 -/
  | signDelim {c : Char} {rest : List Char} (hc : c = '+' ∨ c = '.')
      (hn : ¬ StartsNumber (c :: rest)) :
      TokenAt c rest (Token.delim c) rest
  /-- `-` に `->` が続く：CDC token。 -/
  | cdc {out : List Char} (hn : ¬ StartsNumber ('-' :: '-' :: '>' :: out)) :
      TokenAt '-' ('-' :: '>' :: out) Token.cdc out
  /-- `-` が ident sequence を始める：ident-like token。 -/
  | hyphenIdent {rest out : List Char} {t : Token} (hn : ¬ StartsNumber ('-' :: rest))
      (hc : ¬ ∃ r, rest = '-' :: '>' :: r) (hi : StartsIdent ('-' :: rest))
      (ht : IdentLikeTok ('-' :: rest) t out) :
      TokenAt '-' rest t out
  /-- `-` のそれ以外：delim。 -/
  | hyphenDelim {rest : List Char} (hn : ¬ StartsNumber ('-' :: rest))
      (hc : ¬ ∃ r, rest = '-' :: '>' :: r) (hi : ¬ StartsIdent ('-' :: rest)) :
      TokenAt '-' rest (Token.delim '-') rest
  /-- `<` に `!--` が続く：CDO token。 -/
  | cdo {out : List Char} : TokenAt '<' ('!' :: '-' :: '-' :: out) Token.cdo out
  /-- `<` のそれ以外：delim。 -/
  | ltDelim {rest : List Char} (h : ¬ ∃ r, rest = '!' :: '-' :: '-' :: r) :
      TokenAt '<' rest (Token.delim '<') rest
  /-- `@` が ident sequence を始める：at-keyword token。 -/
  | atKeyword {rest s out : List Char} (hi : StartsIdent rest) (hs : IdentSeq rest s out) :
      TokenAt '@' rest (Token.atKeyword (String.ofList s)) out
  /-- `@` のそれ以外：delim。 -/
  | atDelim {rest : List Char} (hi : ¬ StartsIdent rest) :
      TokenAt '@' rest (Token.delim '@') rest
  /-- `\` が valid escape：ident-like token。 -/
  | backslashIdent {rest out : List Char} {t : Token} (hv : StartsValidEscape ('\\' :: rest))
      (ht : IdentLikeTok ('\\' :: rest) t out) :
      TokenAt '\\' rest t out
  /-- `\` のそれ以外（parse error）：delim。 -/
  | backslashDelim {rest : List Char} (hv : ¬ StartsValidEscape ('\\' :: rest)) :
      TokenAt '\\' rest (Token.delim '\\') rest
  /-- digit：numeric token。 -/
  | digit {c : Char} {rest out : List Char} {t : Token} (hc : Digit c)
      (ht : NumericTok (c :: rest) t out) :
      TokenAt c rest t out
  /-- ident-start code point：ident-like token。 -/
  | identStart {c : Char} {rest out : List Char} {t : Token} (hc : IdentStartCp c)
      (ht : IdentLikeTok (c :: rest) t out) :
      TokenAt c rest t out
  /-- anything else：delim。 -/
  | other {c : Char} {rest : List Char} (hc : OtherCp c) : TokenAt c rest (Token.delim c) rest

/-! ## token 列（§4） -/

/-- `Tokenizes l ts`：前処理済みの `l` を、comment を挟みながら token に切ると `ts`。 -/
inductive Tokenizes : List Char → List Token → Prop where
  /-- comment を読み飛ばすと入力が尽きる。 -/
  | eof {l : List Char} (h : Comments l []) : Tokenizes l []
  /-- comment を読み飛ばし、一文字読んで token を一つ作る。 -/
  | step {l rest out : List Char} {c : Char} {t : Token} {ts : List Token}
      (hc : Comments l (c :: rest)) (ht : TokenAt c rest t out) (ih : Tokenizes out ts) :
      Tokenizes l (t :: ts)

/-- 文字列 `input` を tokenize すると `ts`。前処理（§3.3）から始める。 -/
def TokenizesInput (input : String) (ts : List Token) : Prop :=
  ∃ l, Preprocessed input.toList l ∧ Tokenizes l ts

end Selectors.Spec
