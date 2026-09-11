import Url.Record

/-!
# basic URL parser

WHATWG URL Standard §4.4 の "basic URL parser"。

## pointer をどう表すか

仕様は入力上の pointer を進める state machine で、いくつかの state が
pointer を戻す。戻り方は二通りしかない。

* **1 つ戻す**（`decrease pointer by 1`）。「この文字を次の state で読み直す」という意味なので、
  次の state へ `c :: rest` を渡せばよい。
* **buffer のぶん戻す**（authority state と host state）。buffer に溜めた文字は
  まだ確定していない入力そのものなので、`buffer ++ (c :: rest)` を渡せばよい。

例外は scheme state の "start over"（先頭からやり直す）だけで、これは高々一度しか起きない
（やり直した先は no scheme state で、そこから scheme start state へ戻る道は無い）。
top level で一度だけ再実行する形にしてある。

## state override

`state override` は `Location` と `URL` の setter が使う引数で、
「この state から始めて、成分が一つ決まったら返す」という意味である。
`PCtx.over` に持ち、入口は `basicUrlParseOverride`。setter 側は `Url/Api.lean`。

override が与えられているときは前処理も変わる。仕様 step 1 の
「前後の C0 control or space を落とす」は url が与えられていないときだけで、
tab と newline を落とす step 3 は常に走る。

## 停止性

`stateRank` の順に並べたとおり、どの遷移も state の順位を下げるか、
順位を変えずに入力を 1 つ消費する。測度は `(順位, 残りの文字数, 位相)` の辞書式で、
詳しくは `run` と `step` の手前の節を参照。
-/

namespace Url

open Infra

/-- URL Standard §4.4 の state。 -/
inductive PState where
  | schemeStart | scheme | noScheme | specialRelativeOrAuthority | pathOrAuthority
  | relative | relativeSlash | specialAuthoritySlashes | specialAuthorityIgnoreSlashes
  | authority | host | port | file | fileSlash | fileHost | pathStart | path | opaquePath
  | query | fragment
deriving DecidableEq, Repr, Inhabited

/--
state machine の結果。

`startOver` は scheme state が `:` を見つけられなかったときの
「先頭から no scheme state でやり直す」（step 2.1 の最後）である。
これだけは入力が先頭へ戻るので、再帰の外で一度だけ扱う。
-/
inductive PResult where
  | ok (u : Url)
  | failure
  | startOver
deriving Repr

/--
URL Standard §4.4 の state override。setter が指定しうる state だけを挙げる。

`host` と `hostname` は同じ state から始まり、`:` を見たときの振る舞いだけが違う
（hostname は port を読まずにそこで返す）。仕様では別々の state だが、
本体を分ける必要がないので override の側で区別する。
-/
inductive SOverride where
  | scheme | host | hostname | port | path | query | fragment
deriving DecidableEq, Repr, Inhabited

/-- override が指定する開始 state。 -/
def SOverride.start : SOverride → PState
  | .scheme => .schemeStart
  | .host | .hostname => .host
  | .port => .port
  | .path => .pathStart
  | .query => .query
  | .fragment => .fragment

/-- parser が持ち回る状態。 -/
structure PCtx where
  url : Url
  buffer : List Char := []
  atSignSeen : Bool := false
  insideBrackets : Bool := false
  passwordTokenSeen : Bool := false
  /-- state override。setter から呼ばれたときだけ `some`。 -/
  over : Option SOverride := none

/--
state の順位。停止性の測度の第一成分。

どの遷移も順位を下げるか、同じ順位のまま入力を 1 つ消費する。
唯一の例外が `startOver` で、それは再帰の外に出してある。
-/
def stateRank : PState → Nat
  | .schemeStart => 19
  | .scheme => 18
  | .noScheme => 17
  | .specialRelativeOrAuthority => 16
  | .relative => 15
  | .relativeSlash => 14
  | .specialAuthoritySlashes => 13
  | .specialAuthorityIgnoreSlashes => 12
  | .pathOrAuthority => 11
  | .authority => 10
  | .host => 9
  | .port => 8
  | .file => 7
  | .fileSlash => 6
  | .fileHost => 5
  | .pathStart => 4
  | .path => 3
  | .opaquePath => 2
  | .query => 1
  | .fragment => 0

/-! ## 補助 -/

/-- URL Standard §4.4 single-dot URL path segment。 -/
def isSingleDot (s : List Char) : Bool :=
  let l := asciiLowercase (String.ofList s)
  l == "." || l == "%2e"

/-- URL Standard §4.4 double-dot URL path segment。 -/
def isDoubleDot (s : List Char) : Bool :=
  let l := asciiLowercase (String.ofList s)
  l == ".." || l == ".%2e" || l == "%2e." || l == "%2e%2e"

/-- URL Standard §4.4 Windows drive letter。 -/
def isWindowsDrive (s : List Char) : Bool :=
  match s with
  | [a, b] => isAsciiAlpha a && (b == ':' || b == '|')
  | _ => false

/-- URL Standard §4.4 normalized Windows drive letter。 -/
def isNormalizedWindowsDrive (s : List Char) : Bool :=
  match s with
  | [a, b] => isAsciiAlpha a && b == ':'
  | _ => false

/-- URL Standard §4.4「starts with a Windows drive letter」。 -/
def startsWithWindowsDrive (s : List Char) : Bool :=
  match s with
  | a :: b :: rest =>
    isAsciiAlpha a && (b == ':' || b == '|') &&
      (rest.isEmpty ||
        match rest with
        | c :: _ => c == '/' || c == '\\' || c == '?' || c == '#'
        | [] => true)
  | _ => false

/-- URL Standard §4.4 "shorten a URL's path"。 -/
def shortenPath (u : Url) : Url :=
  match u.path with
  | .opaque _ => u
  | .list segs =>
    if u.scheme == "file" && segs.length == 1 &&
        isNormalizedWindowsDrive ((segs.getD 0 "").toList) then u
    else { u with path := .list segs.dropLast }

/-- path の末尾に segment を足す。 -/
def appendSegment (u : Url) (seg : String) : Url :=
  match u.path with
  | .opaque _ => u
  | .list segs => { u with path := .list (segs ++ [seg]) }

/-- opaque path の末尾に文字列を足す。 -/
def appendOpaque (u : Url) (s : String) : Url :=
  match u.path with
  | .opaque o => { u with path := .opaque (o ++ s) }
  | .list _ => u

/-- EOF を含めた「次の文字」。 -/
abbrev Cp := Option Char

/-- 終端条件（EOF / `/` / `?` / `#`、special なら `\` も）。authority と host が使う。 -/
def isTerminator (special : Bool) : Cp → Bool
  | none => true
  | some c => c == '/' || c == '?' || c == '#' || (special && c == '\\')

/--
path state が segment を確定させるときの url。

`..` なら一つ短くし、`.` なら何も足さず、それ以外は buffer を segment として足す。
どの枝でも path 以外の成分は変わらない。
-/
def pathStepUrl (u : Url) (slash : Bool) (buffer : List Char) : Url :=
  if isDoubleDot buffer then
    if slash then shortenPath u else appendSegment (shortenPath u) ""
  else if isSingleDot buffer then
    if slash then u else appendSegment u ""
  else appendSegment u (String.ofList (windowsDriveBuffer u buffer))
where
  /-- file URL の先頭 segment に来た `c|` は `c:` に直す。 -/
  windowsDriveBuffer (u : Url) (buffer : List Char) : List Char :=
    if u.scheme == "file" && (match u.path with | .list [] => true | _ => false) &&
        isWindowsDrive buffer then
      (match buffer with | [a, _] => [a, ':'] | b => b)
    else buffer

/--
file state が base の path を引き継ぐときの url。

入力が Windows drive letter で始まるなら base の path は捨てる
（`file:///c:/` の `c:` が base の path の後ろに付かないようにする）。
-/
def fileBasePath (u : Url) (input : List Char) : Url :=
  if startsWithWindowsDrive input then { u with path := .list [] } else shortenPath u

/--
file slash state が base の Windows drive letter を引き継ぐときの url。

base の path の先頭が正規化された Windows drive letter で、
入力がそうでないときだけ、その drive letter を path の先頭に足す。
-/
def fileSlashDrive (u : Url) (basePath : Path) (input : List Char) : Url :=
  match basePath with
  | .list (s :: _) =>
    if !startsWithWindowsDrive input && isNormalizedWindowsDrive s.toList then
      appendSegment u s
    else u
  | _ => u

/-- 1 文字を percent-encode して文字列にする。 -/
def encChar (set : Char → Bool) (c : Char) : String :=
  String.ofList (utf8PercentEncode set [c])

/-! ## state machine -/

/-- port state が積んだ 10 進の数字列の値。 -/
def portValue (buf : List Char) : Nat :=
  buf.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) 0

/-- 既定の port と同じなら null にする（§4.4 port state step 3.2）。 -/
def portOf (scheme : String) (p : Nat) : Option Nat :=
  if defaultPort scheme == some p then none else some p

/-- port を書き込み、buffer を空にする。 -/
def portSet (ctx : PCtx) (p : Option Nat) : PCtx :=
  { ctx with url := { ctx.url with port := p }, buffer := [] }

/-- port state の終わり方。buffer を 10 進として読み、既定 port なら null にする。 -/
def portDone (ctx : PCtx) : Option PCtx :=
  if ctx.buffer.isEmpty then some { ctx with buffer := [] }
  else if portValue ctx.buffer > 65535 then none
  else some (portSet ctx (portOf ctx.url.scheme (portValue ctx.buffer)))

/--
authority state が `@` の手前を username と password に振り分ける 1 文字ぶん。

`acc.2` は password token（`:`）を見たかどうか。最初の `:` だけが区切りで、
それ以降の `:` は password の中身になる。
-/
def userinfoStep (acc : Url × Bool) (cp : Char) : Url × Bool :=
  if cp == ':' && !acc.2 then (acc.1, true)
  else
    let enc := encChar userinfoSet cp
    if acc.2 then ({ acc.1 with password := acc.1.password ++ enc }, acc.2)
    else ({ acc.1 with username := acc.1.username ++ enc }, acc.2)

/-- query state が積んだ buffer を percent-encode したもの。 -/
def queryOf (ctx : PCtx) : String :=
  (ctx.url.query.getD "") ++
    String.ofList (utf8PercentEncode
      (if ctx.url.isSpecial then specialQuerySet else querySet) ctx.buffer)

/--
scheme state が `:` を見たときの、state override がある側（protocol setter）。

仕様が並べる四つの拒否条件は、どれも「書き換えると URL record の形が壊れる」もの。
special と非 special の間は行き来できず（path の形が違う）、
credentials や port を持つ URL は `file` になれず（`file` は持てない）、
host が空の `file` は他の scheme になれない（host を要求されうる）。
-/
def schemeOverride (ctx : PCtx) : PResult :=
  let buf := String.ofList ctx.buffer
  if ctx.url.isSpecial && !isSpecialScheme buf then .ok ctx.url
  else if !ctx.url.isSpecial && isSpecialScheme buf then .ok ctx.url
  else if (ctx.url.includesCredentials || ctx.url.port.isSome) && buf == "file" then .ok ctx.url
  else if ctx.url.scheme == "file" && ctx.url.host == some Host.empty then .ok ctx.url
  else
    let u := { ctx.url with scheme := buf }
    .ok (if defaultPort u.scheme == u.port then { u with port := none } else u)

/--
仕様の「return failure」。

url を与えられた（state override 付きの）呼び出しでは、仕様は URL record を
その場で書き換えていくので、途中で失敗しても**そこまでの書き換えは残る**。
setter 側は返り値を見ないので、失敗は「そこで止まる」以上の意味を持たない。
url を与えない普通の parse では、失敗は全体の失敗である。

実際に効くのは host state から port state へ渡った後の失敗で、
`u.host = "example.com:65536"` は host だけが書き換わって port は変わらない。
-/
def fail (ctx : PCtx) : PResult :=
  match ctx.over with
  | some _ => .ok ctx.url
  | none => .failure

/-!
## 停止性

`stateRank` が示すとおり、どの遷移も

* state の順位を下げるか、
* 順位を変えずに入力を 1 つ消費する

かのどちらかである。入力を消費しない遷移（`decrease pointer by 1` と
authority/host の巻き戻し）は必ず順位を下げ、順位を変えない遷移
（buffer に 1 文字積む自己ループ）は必ず入力を 1 つ消費する。

測度は `(stateRank st, 残りの文字数, 位相)` の辞書式である。
`run` は先頭の 1 文字を取り出すだけなので位相 1、`step` が本体で位相 0。
`step` の「残りの文字数」は `rest` の長さに、いま読んでいる文字があれば 1 を足したもの。
-/

mutual

/-- 入力の先頭を取り出して `step` に渡す。 -/
def run (base : Option Url) (st : PState) (input : List Char) (ctx : PCtx) : PResult :=
  match input with
  | [] => step base st none [] [] ctx
  | ch :: t => step base st (some ch) t (ch :: t) ctx
termination_by (stateRank st, input.length, 1)

/-- state machine 本体。`c` は EOF を含めた「いま読んでいる文字」、`rest` はその後ろ。 -/
def step (base : Option Url) (st : PState) (c : Cp) (rest input : List Char) (ctx : PCtx) :
    PResult :=
    -- `input` は「この文字を読み直す」ための入力。仕様の `decrease pointer by 1` に当たる。
    let special := ctx.url.isSpecial
    match st with
    | .schemeStart =>
      match c with
      | some ch =>
        if isAsciiAlpha ch then
          run base .scheme rest
            { ctx with buffer := ctx.buffer ++ (asciiLowercase (String.ofList [ch])).toList }
        -- override があるときは no scheme state へ落ちず、そこで失敗する。
        else if ctx.over.isSome then fail ctx
        else run base .noScheme input ctx
      | none => if ctx.over.isSome then fail ctx else run base .noScheme input ctx
    | .scheme =>
      match c with
      | some ch =>
        if isAsciiAlphanumeric ch || ch == '+' || ch == '-' || ch == '.' then
          run base .scheme rest
            { ctx with buffer := ctx.buffer ++ (asciiLowercase (String.ofList [ch])).toList }
        else if ch == ':' then
          if ctx.over.isSome then schemeOverride ctx
          else
          let u := { ctx.url with scheme := String.ofList ctx.buffer }
          let ctx2 : PCtx := { ctx with url := u, buffer := [] }
          if u.scheme == "file" then run base .file rest ctx2
          else if u.isSpecial &&
              (match base with | some b => b.scheme == u.scheme | none => false) then
            run base .specialRelativeOrAuthority rest ctx2
          else if u.isSpecial then run base .specialAuthoritySlashes rest ctx2
          else
            match rest with
            | '/' :: rest2 => run base .pathOrAuthority rest2 ctx2
            | _ => run base .opaquePath rest { ctx2 with url := { u with path := .opaque "" } }
        else if ctx.over.isSome then fail ctx
        else
          -- "start over"。入力が先頭へ戻る唯一の遷移なので、再帰の外へ返す。
          PResult.startOver
      -- EOF も「alphanumeric でも `:` でもない」に当たるので、同じく start over する。
      | none => if ctx.over.isSome then fail ctx else PResult.startOver
    | .noScheme =>
      match base with
      | none => fail ctx
      | some b =>
        if b.hasOpaquePath && c != some '#' then fail ctx
        else if b.hasOpaquePath then
          let u := { ctx.url with scheme := b.scheme, path := b.path, query := b.query }
          run base .fragment rest { ctx with url := { u with fragment := some "" } }
        else if b.scheme != "file" then run base .relative input ctx
        else run base .file input ctx
    | .specialRelativeOrAuthority =>
      match c, rest with
      | some '/', '/' :: rest2 => run base .specialAuthorityIgnoreSlashes rest2 ctx
      | _, _ => run base .relative input ctx
    | .pathOrAuthority =>
      if c == some '/' then run base .authority rest ctx
      else run base .path input ctx
    | .relative =>
      match base with
      | none => fail ctx
      | some b =>
        let u := { ctx.url with scheme := b.scheme }
        if c == some '/' then run base .relativeSlash rest { ctx with url := u }
        else if u.isSpecial && c == some '\\' then
          run base .relativeSlash rest { ctx with url := u }
        else
          let u1 := { u with username := b.username, password := b.password }
          let u2 := { u1 with host := b.host, port := b.port, path := b.path, query := b.query }
          match c with
          | some '?' =>
            run base .query rest { ctx with url := { u2 with query := some "" } }
          | some '#' =>
            run base .fragment rest { ctx with url := { u2 with fragment := some "" } }
          | none => .ok u2
          | some _ =>
            run base .path input { ctx with url := shortenPath { u2 with query := none } }
    | .relativeSlash =>
      if special && (c == some '/' || c == some '\\') then
        run base .specialAuthorityIgnoreSlashes rest ctx
      else if c == some '/' then run base .authority rest ctx
      else
        match base with
        | none => fail ctx
        | some b =>
          let u1 := { ctx.url with username := b.username, password := b.password }
          run base .path input { ctx with url := { u1 with host := b.host, port := b.port } }
    | .specialAuthoritySlashes =>
      match c, rest with
      | some '/', '/' :: rest2 => run base .specialAuthorityIgnoreSlashes rest2 ctx
      | _, _ => run base .specialAuthorityIgnoreSlashes input ctx
    | .specialAuthorityIgnoreSlashes =>
      match c with
      | some ch =>
        if ch == '/' || ch == '\\' then run base .specialAuthorityIgnoreSlashes rest ctx
        else run base .authority input ctx
      | none => run base .authority input ctx
    | .authority =>
      match c with
      | none =>
        -- EOF は terminator。buffer を host state へ戻す。
        if ctx.atSignSeen && ctx.buffer.isEmpty then fail ctx
        else run base .host (ctx.buffer ++ input) { ctx with buffer := [] }
      | some ch =>
        if ch == '@' then
          let buf := if ctx.atSignSeen then "%40".toList ++ ctx.buffer else ctx.buffer
          let r := buf.foldl userinfoStep (ctx.url, ctx.passwordTokenSeen)
          let ctx2 : PCtx := { ctx with url := r.1, buffer := [], atSignSeen := true }
          run base .authority rest { ctx2 with passwordTokenSeen := r.2 }
        else if isTerminator special (some ch) then
          if ctx.atSignSeen && ctx.buffer.isEmpty then fail ctx
          else run base .host (ctx.buffer ++ input) { ctx with buffer := [] }
        else run base .authority rest { ctx with buffer := ctx.buffer ++ [ch] }
    | .host =>
      -- override 付きで file URL の host を書き換えるときは file host state で読む。
      if ctx.over.isSome && ctx.url.scheme == "file" then run base .fileHost input ctx
      else if c == some ':' && !ctx.insideBrackets then
        if ctx.buffer.isEmpty then fail ctx
        -- hostname setter は port を読まない。
        else if ctx.over == some .hostname then PResult.ok ctx.url
        else
          match hostParser asciiDomainToASCII ctx.buffer (!special) with
          | none => fail ctx
          | some h =>
            let u := { ctx.url with host := some h }
            run base .port rest { ctx with url := u, buffer := [] }
      else if isTerminator special c then
        if special && ctx.buffer.isEmpty then fail ctx
        -- host を空にすると credentials や port の置き場所が無くなる場合は何もしない。
        else if ctx.over.isSome && ctx.buffer.isEmpty &&
            (ctx.url.includesCredentials || ctx.url.port.isSome) then PResult.ok ctx.url
        else
          match hostParser asciiDomainToASCII ctx.buffer (!special) with
          | none => fail ctx
          | some h =>
            let u := { ctx.url with host := some h }
            if ctx.over.isSome then PResult.ok u
            else run base .pathStart input { ctx with url := u, buffer := [] }
      else
        match c with
        | none => fail ctx
        | some ch =>
          let ib := if ch == '[' then true else if ch == ']' then false else ctx.insideBrackets
          run base .host rest { ctx with buffer := ctx.buffer ++ [ch], insideBrackets := ib }
    | .port =>
      match c with
      | some ch =>
        if isAsciiDigit ch then run base .port rest { ctx with buffer := ctx.buffer ++ [ch] }
        -- override があるときは、digit でない文字はすべてここを終わらせる。
        else if isTerminator special c || ctx.over.isSome then
          match portDone ctx with
          | none => fail ctx
          | some ctx2 =>
            if ctx.over.isSome then PResult.ok ctx2.url else run base .pathStart input ctx2
        else fail ctx
      | none =>
        match portDone ctx with
        | none => fail ctx
        | some ctx2 =>
          if ctx.over.isSome then PResult.ok ctx2.url else run base .pathStart input ctx2
    | .file =>
      let u := { ctx.url with scheme := "file", host := some Host.empty }
      if c == some '/' || c == some '\\' then
        run base .fileSlash rest { ctx with url := u }
      else
        match base with
        | some b =>
          if b.scheme == "file" then
            let u2 := { u with host := b.host, path := b.path, query := b.query }
            match c with
            | some '?' =>
              run base .query rest { ctx with url := { u2 with query := some "" } }
            | some '#' =>
              run base .fragment rest { ctx with url := { u2 with fragment := some "" } }
            | none => .ok u2
            | some _ =>
              run base .path input { ctx with url := fileBasePath { u2 with query := none } input }
          else run base .path input { ctx with url := u }
        | none => run base .path input { ctx with url := u }
    | .fileSlash =>
      if c == some '/' || c == some '\\' then run base .fileHost rest ctx
      else
        match base with
        | some b =>
          if b.scheme == "file" then
            let u := { ctx.url with host := b.host }
            run base .path input { ctx with url := fileSlashDrive u b.path input }
          else run base .path input ctx
        | none => run base .path input ctx
    | .fileHost =>
      if c == none || c == some '/' || c == some '\\' || c == some '?' || c == some '#' then
        -- Windows drive letter を host と読み違えないための分岐は override では要らない。
        if ctx.over.isNone && isWindowsDrive ctx.buffer then run base .path input ctx
        else if ctx.buffer.isEmpty then
          let u := { ctx.url with host := some Host.empty }
          if ctx.over.isSome then PResult.ok u
          else run base .pathStart input { ctx with url := u }
        else
          match hostParser asciiDomainToASCII ctx.buffer (!special) with
          | none => fail ctx
          | some h =>
            let h2 := if hostSerializer h == "localhost" then Host.empty else h
            let u := { ctx.url with host := some h2 }
            if ctx.over.isSome then PResult.ok u
            else run base .pathStart input { ctx with url := u, buffer := [] }
      else
        match c with
        | none => fail ctx
        | some ch => run base .fileHost rest { ctx with buffer := ctx.buffer ++ [ch] }
    | .pathStart =>
      if special then
        if c == some '/' || c == some '\\' then run base .path rest ctx
        else run base .path input ctx
      else if ctx.over.isNone && c == some '?' then
        run base .query rest { ctx with url := { ctx.url with query := some "" } }
      else if ctx.over.isNone && c == some '#' then
        run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } }
      else
        match c with
        -- host を持たない URL の path を空にすると serialize で scheme と path が
        -- くっついてしまうので、空の segment を一つ残す。
        | none =>
          if ctx.over.isSome && ctx.url.host.isNone then .ok (appendSegment ctx.url "")
          else .ok ctx.url
        | some ch => if ch == '/' then run base .path rest ctx
                     else run base .path input ctx
    | .path =>
      -- override があるときは `?` と `#` は segment の一部で、query / fragment へは移らない。
      if c == none || c == some '/' || (special && c == some '\\') ||
          (ctx.over.isNone && (c == some '?' || c == some '#')) then
        let slash := c == some '/' || (special && c == some '\\')
        let u := pathStepUrl ctx.url slash ctx.buffer
        let ctx2 : PCtx := { ctx with url := u, buffer := [] }
        match c with
        | some '?' => run base .query rest { ctx2 with url := { u with query := some "" } }
        | some '#' => run base .fragment rest { ctx2 with url := { u with fragment := some "" } }
        | none => .ok u
        | some _ => run base .path rest ctx2
      else
        match c with
        | none => fail ctx
        | some ch =>
          run base .path rest { ctx with buffer := ctx.buffer ++ (encChar pathSet ch).toList }
    | .opaquePath =>
      match c with
      | some '?' => run base .query rest { ctx with url := { ctx.url with query := some "" } }
      | some '#' =>
        run base .fragment rest { ctx with url := { ctx.url with fragment := some "" } }
      | some ' ' =>
        let addition := match rest.head? with
          | some '?' => "%20"
          | some '#' => "%20"
          | _ => " "
        run base .opaquePath rest { ctx with url := appendOpaque ctx.url addition }
      | some ch =>
        run base .opaquePath rest
          { ctx with url := appendOpaque ctx.url (encChar c0ControlSet ch) }
      | none => .ok ctx.url
    | .query =>
      match c with
      | none => .ok { ctx.url with query := some (queryOf ctx) }
      | some '#' =>
        if ctx.over.isSome then run base .query rest { ctx with buffer := ctx.buffer ++ ['#'] }
        else
          let u := { ctx.url with query := some (queryOf ctx), fragment := some "" }
          run base .fragment rest { ctx with url := u, buffer := [] }
      | some ch => run base .query rest { ctx with buffer := ctx.buffer ++ [ch] }
    | .fragment =>
      match c with
      | none => .ok ctx.url
      | some ch =>
        let f := (ctx.url.fragment.getD "") ++ encChar fragmentSet ch
        run base .fragment rest { ctx with url := { ctx.url with fragment := some f } }
termination_by (stateRank st, rest.length + (if c.isSome then 1 else 0), 0)
decreasing_by all_goals (simp_wf <;> simp [stateRank, Prod.lex_def] <;> omega)

end


/-! ## 入口 -/

/--
URL Standard §4.4 "basic URL parser"。

step 1 の前処理（前後の C0 control or space を落とし、tab と newline を全部落とす）を
してから state machine を回す。
-/
def stripTabNewline (l : List Char) : List Char :=
  l.filter (fun c => !(c.toNat == 0x09 || c.toNat == 0x0A || c.toNat == 0x0D))

/-- §4.4 step 1-3 の前処理。前後の C0 control or space を落とし、tab と newline を落とす。 -/
def preprocess (input : String) : List Char :=
  let l := input.toList.dropWhile isC0ControlOrSpace
  stripTabNewline (l.reverse.dropWhile isC0ControlOrSpace).reverse

def basicUrlParse (input : String) (base : Option Url := none) : Option Url :=
  -- "start over" は高々一度。no scheme state から scheme start state へ戻る道は無い。
  match run base .schemeStart (preprocess input) { url := {} } with
  | .ok u => some u
  | .failure => none
  | .startOver =>
    match run base .noScheme (preprocess input) { url := {} } with
    | .ok u => some u
    | _ => none

/--
url と state override を与えた basic URL parser。setter だけが使う。

前後の C0 control or space を落とさないのは仕様どおりで、
その step が「url が与えられていないとき」の中にあるためである。
override があると scheme state は "start over" せず失敗するので、
ここでやり直しは要らない。
-/
def basicUrlParseOverride (input : String) (u : Url) (over : SOverride) : Option Url :=
  match run none over.start (stripTabNewline input.toList) { url := u, over := some over } with
  | .ok u' => some u'
  | _ => none

/-- `URL(url, base)` に当たる入口。失敗したら `none`。 -/
def parseUrl (input : String) (base : Option String := none) : Option Url :=
  match base with
  | none => basicUrlParse input none
  | some b =>
    match basicUrlParse b none with
    | none => none
    | some bu => basicUrlParse input (some bu)

/-! ## origin -/

/--
URL Standard §4.7 の origin。

`blob` は blob URL entry を持たない前提で、path を URL として読み直す
（読み直した結果が http / https / file ならその origin、そうでなければ opaque）。
`file` は仕様が「実装依存の opaque origin」としているので opaque にする。

`blob:blob:...` のような入れ子は仕様上も一段だけ辿れば足りる
（読み直した URL の scheme が `blob` なら http/https/file ではないので opaque になる）。
-/
def origin (u : Url) : Origin :=
  if u.scheme == "ftp" || u.scheme == "http" || u.scheme == "https" ||
      u.scheme == "ws" || u.scheme == "wss" then
    match u.host with
    | some h => some (u.scheme, h, u.port)
    | none => none
  else if u.scheme == "blob" then
    match u.path with
    | .opaque p =>
      match basicUrlParse p none with
      | none => none
      | some p' =>
        if p'.scheme == "http" || p'.scheme == "https" then
          match p'.host with
          | some h => some (p'.scheme, h, p'.port)
          | none => none
        else none
    | .list _ => none
  else none

end Url
