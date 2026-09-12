import Url
import Lean.Data.Json

/-!
# `url-model`

URL Standard の oracle。

`url-model --wpt FILE` は WPT の `urltestdata.json` から作った表
（`test/url/wpt-ascii.json`）を読み、各 case を model で parse して
期待される `href`（または failure）と突き合わせる。
-/

open Lean (Json)
open Url

structure Case where
  input : String
  base : Option String
  failure : Bool
  href : Option String
  origin : Option String
  /-- model の対象外である理由。付いていたら一致を求めない。 -/
  outOfModel : Option String

def caseOfJson (j : Json) : Except String Case := do
  let input ← (← j.getObjVal? "input").getStr?
  let base ← match j.getObjVal? "base" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  let failure ← match j.getObjVal? "failure" with
    | .ok v => v.getBool?
    | .error _ => pure false
  let href ← match j.getObjVal? "href" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  let origin ← match j.getObjVal? "origin" with
    | .ok v => if v.isNull then pure none else (v.getStr?).map some
    | .error _ => pure none
  let outOfModel ← match j.getObjVal? "out_of_model" with
    | .ok v => (v.getStr?).map some
    | .error _ => pure none
  return { input, base, failure, href, origin, outOfModel }

/-! ## UTS #46 の表 -/

def idnaRangeOfJson (j : Json) : Except String IdnaRange := do
  let arr ← j.getArr?
  match arr.toList with
  | loJ :: hiJ :: stJ :: oomJ :: rest =>
    let lo ← loJ.getNat?
    let hi ← hiJ.getNat?
    let st ← stJ.getNat?
    let oom ← oomJ.getNat?
    let mapping ← match rest with
      | [m] => do let ma ← m.getArr?; ma.toList.mapM (fun x => x.getNat?)
      | _ => pure []
    let status := match st with
      | 0 => IdnaStatus.valid
      | 1 => IdnaStatus.ignored
      | 2 => IdnaStatus.mapped
      | _ => IdnaStatus.disallowed
    return { lo, hi, status, oom := oom != 0, mapping }
  | _ => throw "範囲が 4 要素以上の配列ではない"

/-- UTS #46 の表を読む。`Resolved` を実行時に確かめる。 -/
def loadIdnaTable (path : String) : IO (Option (Array IdnaRange)) := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return none
  let .ok rangesJson := json.getObjVal? "ranges"
    | do IO.eprintln s!"{path}: `ranges` がない"; return none
  let .ok arr := rangesJson.getArr? | do IO.eprintln s!"{path}: `ranges` が配列ではない"; return none
  let mut rs : Array IdnaRange := #[]
  for j in arr do
    match idnaRangeOfJson j with
    | .error e => IO.eprintln s!"範囲を読めない: {e}"; return none
    | .ok r => rs := rs.push r
  if !checkSorted rs then
    IO.eprintln s!"{path}: 区間が昇順でないか重なっている（二分探索が正しく引けない）"
    return none
  if !checkResolved rs then
    IO.eprintln s!"{path}: 写像先が valid でない項がある（IdnaTable.Resolved を満たさない）"
    return none
  IO.println s!"UTS #46 の表: {rs.size} 範囲、昇順・非重複、Resolved を満たす"
  return some rs

/-- 表があればそれを使う ToASCII、無ければ ASCII だけの既定。 -/
def toAsciiOf : Option (Array IdnaRange) → (List Char → Option String)
  | none => asciiDomainToASCII
  | some rs => toASCII (tableOfRanges rs)

def runWpt (path : String) (idna : Option (Array IdnaRange)) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return 1
  let .ok casesJson := json.getObjVal? "cases"
    | do IO.eprintln s!"{path}: `cases` がない"; return 1
  let .ok arr := casesJson.getArr? | do IO.eprintln s!"{path}: `cases` が配列ではない"; return 1
  let mut ok := 0
  let mut bad := 0
  let mut skipped := 0
  let mut stale := 0
  let mut invalid := 0
  let mut originOk := 0
  let mut originBad := 0
  let mut shown := 0
  for j in arr do
    match caseOfJson j with
    | .error e => IO.eprintln s!"case を読めない: {e}"; bad := bad + 1
    | .ok c =>
      let got := parseUrl c.input c.base (toAsciiOf idna)
      let expected : Option String := if c.failure then none else c.href
      let actual : Option String := got.map (fun u => urlSerializer u)
      -- parse が成功したなら、結果の record は `ValidUrl` を満たす（`basicUrlParse_valid`）。
      -- 証明は付いたが、実装と証明が同じ定義を見ていることの検査として走らせ続ける。
      match got with
      | some u =>
        if !checkValidUrl u then
          invalid := invalid + 1
          IO.println s!"INVALID input={repr c.input} base={repr c.base} -> {urlSerializer u}"
        -- §4.1 のうち証明に上げていない条件。交差検証として実行時に見る。
        if !checkStrictUrl u then
          invalid := invalid + 1
          IO.println s!"STRICT input={repr c.input} base={repr c.base} -> {urlSerializer u}"
      | none => pure ()
      -- §4.7 origin。WPT の表が期待値を持っている case だけ見る。
      match got, c.origin with
      | some u, some expectedOrigin =>
        if originSerializer (Url.origin u) == expectedOrigin then originOk := originOk + 1
        else
          originBad := originBad + 1
          if shown < 20 then
            shown := shown + 1
            IO.println s!"ORIGIN input={repr c.input} base={repr c.base}"
            IO.println s!"  expected={repr expectedOrigin}"
            IO.println s!"  actual  ={repr (originSerializer (Url.origin u))}"
      | _, _ => pure ()
      -- 対象外かどうかは fixture が明示する。実行結果から推測しない
      -- （推測にすると、対象外でない case の退行が対象外に吸収されてしまう）。
      -- 表を渡したときは IDNA の印を無視して一致を要求する。
      match (if idna.isSome then none else c.outOfModel) with
      | some reason =>
        if actual == expected then
          stale := stale + 1
          IO.println s!"STALE 対象外（{reason}）の印だが一致した input={repr c.input}"
        else skipped := skipped + 1
      | none =>
        if actual == expected then ok := ok + 1
        else
          bad := bad + 1
          if shown < 20 then
            shown := shown + 1
            IO.println s!"MISMATCH input={repr c.input} base={repr c.base}"
            IO.println s!"  expected={repr expected}"
            IO.println s!"  actual  ={repr actual}"
  IO.println s!"WPT: 一致 {ok} / 不一致 {bad} / 対象外 {skipped}"
  if stale != 0 then IO.println s!"対象外の印が古い: {stale}"
  IO.println s!"ValidUrl: 違反 {invalid}"
  IO.println s!"origin: 一致 {originOk} / 不一致 {originBad}"
  return if bad == 0 && stale == 0 && invalid == 0 && originBad == 0 then 0 else 1

/-! ## setter -/

structure SetterCase where
  setter : String
  href : String
  newValue : String
  expected : List (String × String)
  /-- model の対象外である理由。付いていたら一致を求めない。 -/
  outOfModel : Option String

def setterCaseOfJson (j : Json) : Except String SetterCase := do
  let setter ← (← j.getObjVal? "setter").getStr?
  let href ← (← j.getObjVal? "href").getStr?
  let newValue ← (← j.getObjVal? "new_value").getStr?
  let arr ← (← j.getObjVal? "expected").getArr?
  let expected ← arr.toList.mapM fun pair => do
    let p ← pair.getArr?
    match p.toList with
    | [k, v] => do return ((← k.getStr?), (← v.getStr?))
    | _ => throw "expected の要素が 2 要素の配列ではない"
  let outOfModel ← match j.getObjVal? "out_of_model" with
    | .ok v => (v.getStr?).map some
    | .error _ => pure none
  return { setter, href, newValue, expected, outOfModel }

/--
WPT の `setters_tests.json`（ASCII だけの 258 件）を通す。

各 case は「この URL を parse し、この setter にこの値を入れ、
各 IDL 属性がこうなる」という形。`href` が parse できることも一緒に確かめる。
-/
def runSetters (path : String) (idna : Option (Array IdnaRange)) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return 1
  let .ok casesJson := json.getObjVal? "cases"
    | do IO.eprintln s!"{path}: `cases` がない"; return 1
  let .ok arr := casesJson.getArr? | do IO.eprintln s!"{path}: `cases` が配列ではない"; return 1
  let mut ok := 0
  let mut bad := 0
  let mut skipped := 0
  let mut stale := 0
  let mut invalid := 0
  let mut shown := 0
  for j in arr do
    match setterCaseOfJson j with
    | .error e => IO.eprintln s!"case を読めない: {e}"; bad := bad + 1
    | .ok c =>
      match parseUrl c.href none (toAsciiOf idna) with
      | none =>
        bad := bad + 1
        IO.println s!"SETTER base を parse できない href={repr c.href}"
      | some u0 =>
        match u0.setAttr c.setter c.newValue (toAsciiOf idna) with
        | none =>
          bad := bad + 1
          IO.println s!"SETTER 未知の setter {repr c.setter}"
        | some u =>
          -- setter を通した後も record は `ValidUrl` を満たす（`setAttr_valid`）。
          if !checkValidUrl u then
            invalid := invalid + 1
            IO.println s!"INVALID setter={c.setter} href={repr c.href} value={repr c.newValue}"
          if !checkStrictUrl u then
            invalid := invalid + 1
            IO.println s!"STRICT setter={c.setter} href={repr c.href} value={repr c.newValue}"
          -- 対象外かどうかは fixture が明示する。`--wpt` 側と同じ扱い。
          let mut anyMismatch := false
          for (name, want) in c.expected do
            match u.getAttr name with
            | none =>
              bad := bad + 1
              IO.println s!"SETTER 未知の属性 {repr name}"
            | some got =>
              if got == want then
                ok := ok + 1
              else
                anyMismatch := true
                match (if idna.isSome then none else c.outOfModel) with
                | some _ => skipped := skipped + 1
                | none =>
                  bad := bad + 1
                  if shown < 20 then
                    shown := shown + 1
                    IO.println s!"SETTER {c.setter} href={repr c.href} value={repr c.newValue}"
                    IO.println s!"  {name}: expected={repr want} actual={repr got}"
          match (if idna.isSome then none else c.outOfModel) with
          | some reason =>
            if !anyMismatch then
              stale := stale + 1
              IO.println s!"STALE 対象外（{reason}）の印だが全部一致した setter={c.setter}"
          | none => pure ()
  IO.println s!"setters: 一致 {ok} / 不一致 {bad} / 対象外 {skipped}"
  if stale != 0 then IO.println s!"対象外の印が古い: {stale}"
  IO.println s!"ValidUrl（setter 後）: 違反 {invalid}"
  return if bad == 0 && stale == 0 && invalid == 0 then 0 else 1

/-! ## Punycode -/

structure PunyCase where
  label : String
  input : String
  punycode : String

def punyCaseOfJson (j : Json) : Except String PunyCase := do
  let label ← (← j.getObjVal? "label").getStr?
  let input ← (← j.getObjVal? "input").getStr?
  let punycode ← (← j.getObjVal? "punycode").getStr?
  return { label, input, punycode }

/--
RFC 3492 §7.1 の sample strings を通す。

符号化の比較は ASCII の大文字小文字を無視する（RFC の (I) が §5 の case annotation を
含んでいるため）。復号は RFC の綴りをそのまま食わせる。
-/
def runPunycode (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return 1
  let .ok casesJson := json.getObjVal? "cases"
    | do IO.eprintln s!"{path}: `cases` がない"; return 1
  let .ok arr := casesJson.getArr? | do IO.eprintln s!"{path}: `cases` が配列ではない"; return 1
  let mut ok := 0
  let mut bad := 0
  for j in arr do
    match punyCaseOfJson j with
    | .error e => IO.eprintln s!"case を読めない: {e}"; bad := bad + 1
    | .ok c =>
      let got := String.ofList (Url.Punycode.encode c.input.toList)
      if Infra.asciiLowercase got == Infra.asciiLowercase c.punycode then ok := ok + 1
      else
        bad := bad + 1
        IO.println s!"PUNY encode ({c.label}) expected={c.punycode} actual={got}"
      match Url.Punycode.decode c.punycode.toList with
      | none =>
        bad := bad + 1
        IO.println s!"PUNY decode ({c.label}) 失敗 {c.punycode}"
      | some d =>
        if String.ofList d == c.input then ok := ok + 1
        else
          bad := bad + 1
          IO.println s!"PUNY decode ({c.label}) expected={repr c.input} actual={repr (String.ofList d)}"
  IO.println s!"punycode: 一致 {ok} / 不一致 {bad}"
  return if bad == 0 then 0 else 1

/-! ## `URLSearchParams` -/

structure SortCase where
  input : String
  output : List (String × String)

def sortCaseOfJson (j : Json) : Except String SortCase := do
  let input ← (← j.getObjVal? "input").getStr?
  let arr ← (← j.getObjVal? "output").getArr?
  let output ← arr.toList.mapM fun pair => do
    let p ← pair.getArr?
    match p.toList with
    | [k, v] => do return ((← k.getStr?), (← v.getStr?))
    | _ => throw "output の要素が 2 要素の配列ではない"
  return { input, output }

/--
§6.2 の各操作の固定 case。仕様の記述とその例から作った。

`sort` だけは WPT が配列リテラルで期待値を配っているので、そちらは `--searchparams` で
その表を通す。
-/
def paramsCases : List (String × String × String) :=
  let base := Params.ofString "?a=b&c=d&a=e"
  [ ("get a", (Params.get base "a").getD "<none>", "b")
  , ("get z", (Params.get base "z").getD "<none>", "<none>")
  , ("getAll a", String.intercalate "," (Params.getAll base "a"), "b,e")
  , ("getAll z", String.intercalate "," (Params.getAll base "z"), "")
  , ("has c", toString (Params.has base "c"), "true")
  , ("has z", toString (Params.has base "z"), "false")
  , ("hasValue a e", toString (Params.hasValue base "a" "e"), "true")
  , ("hasValue a d", toString (Params.hasValue base "a" "d"), "false")
  , ("size", toString (Params.size base), "3")
  , ("append", Params.serialize (Params.append base "e" "f"), "a=b&c=d&a=e&e=f")
  , ("delete a", Params.serialize (Params.delete base "a"), "c=d")
  , ("deleteValue a e", Params.serialize (Params.deleteValue base "a" "e"), "a=b&c=d")
  , ("set a x", Params.serialize (Params.set base "a" "x"), "a=x&c=d")
  , ("set z x", Params.serialize (Params.set base "z" "x"), "a=b&c=d&a=e&z=x")
  , ("sort", Params.serialize (Params.sort base), "a=b&a=e&c=d")
  , ("serialize", Params.serialize base, "a=b&c=d&a=e")
  , -- 仕様 §6.2 の例。URL から読んで並べ替え、URL に書き戻す。
    ("url + sort",
     match parseUrl "https://example.org/?q=%F0%9F%8C%88&key=e1f7bc78" none with
     | none => "<parse failed>"
     | some u => Url.search (Url.withParams u (Params.sort (Url.searchParams u))),
     "?key=e1f7bc78&q=%F0%9F%8C%88")
  , -- 空になったら query は null になる。
    ("url + delete all",
     match parseUrl "https://example.org/?a=b" none with
     | none => "<parse failed>"
     | some u => Url.href (Url.withParams u (Params.delete (Url.searchParams u) "a")),
     "https://example.org/")
  ]

/--
WPT の `urlsearchparams-sort.any.js` が持つ表を通す。

`sort` は code point 順ではなく **UTF-16 code unit 順**である。
`ﬃ&🌈` の case がそれを見分ける（🌈 は code point では後ろだが、
surrogate pair なので code unit では前に来る）。
-/
def runSearchParams (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok json := Json.parse text | do IO.eprintln s!"{path}: JSON を読めない"; return 1
  let .ok casesJson := json.getObjVal? "cases"
    | do IO.eprintln s!"{path}: `cases` がない"; return 1
  let .ok arr := casesJson.getArr? | do IO.eprintln s!"{path}: `cases` が配列ではない"; return 1
  let mut ok := 0
  let mut bad := 0
  for j in arr do
    match sortCaseOfJson j with
    | .error e => IO.eprintln s!"case を読めない: {e}"; bad := bad + 1
    | .ok c =>
      let got := Params.sort (Params.ofString c.input)
      if got == c.output then ok := ok + 1
      else
        bad := bad + 1
        IO.println s!"SORT input={repr c.input}"
        IO.println s!"  expected={repr c.output}"
        IO.println s!"  actual  ={repr got}"
  for (label, got, want) in paramsCases do
    if got == want then ok := ok + 1
    else
      bad := bad + 1
      IO.println s!"PARAMS {label}: expected={repr want} actual={repr got}"
  IO.println s!"searchparams: 一致 {ok} / 不一致 {bad}"
  return if bad == 0 then 0 else 1

/--
`application/x-www-form-urlencoded` の固定 case。

WPT 側は JS のテストなので機械可読の表が無い。仕様 §5 の記述と
その例（`≡` → `%E2%89%A1`、`‽` → `%E2%80%BD`）から作った。
-/
def urlencodedCases : List (String × List (String × String)) :=
  [ ("a=b&c=d", [("a", "b"), ("c", "d")])
  , ("a=b&c=d&", [("a", "b"), ("c", "d")])
  , ("&&&a=b&&&&c=d&", [("a", "b"), ("c", "d")])
  , ("a", [("a", "")])
  , ("a=", [("a", "")])
  , ("=b", [("", "b")])
  , ("=", [("", "")])
  , ("a=b=c", [("a", "b=c")])
  , ("a+b=c+d", [("a b", "c d")])
  , ("a%20b=c%20d", [("a b", "c d")])
  , ("a=%2B", [("a", "+")])
  , ("%E2%89%A1=%E2%80%BD", [("≡", "‽")])
  , ("a=%zz", [("a", "%zz")])
  ]

def runUrlencoded : IO UInt32 := do
  let mut ok := 0
  let mut bad := 0
  for (input, expected) in urlencodedCases do
    let got := parseUrlencodedString input
    if got == expected then ok := ok + 1
    else
      bad := bad + 1
      IO.println s!"URLENCODED parse {repr input}"
      IO.println s!"  expected={repr expected}"
      IO.println s!"  actual  ={repr got}"
    -- serialize したものを読み直すと元に戻る（`urlencodedEncode_no_separator` が
    -- 区切りを作らないことを保証している）。
    let round := parseUrlencodedString (serializeUrlencoded expected)
    if round == expected then ok := ok + 1
    else
      bad := bad + 1
      IO.println s!"URLENCODED round-trip {repr expected}"
      IO.println s!"  serialized={repr (serializeUrlencoded expected)}"
      IO.println s!"  reparsed  ={repr round}"
  IO.println s!"urlencoded: 一致 {ok} / 不一致 {bad}"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--wpt", path] => do
    let a ← runWpt path none
    let b ← runUrlencoded
    return if a == 0 && b == 0 then 0 else 1
  | ["--wpt", path, tablePath] => do
    match ← loadIdnaTable tablePath with
    | none => return 1
    | some rs => runWpt path (some rs)
  | ["--setters", path] => runSetters path none
  | ["--setters", path, tablePath] => do
    match ← loadIdnaTable tablePath with
    | none => return 1
    | some rs => runSetters path (some rs)
  | ["--searchparams", path] => runSearchParams path
  | ["--punycode", path] => runPunycode path
  | ["--urlencoded"] => runUrlencoded
  | _ =>
    IO.println "usage: url-model --wpt FILE [UTS46] | --setters FILE [UTS46] | --searchparams FILE | --punycode FILE | --urlencoded"
    return 1
