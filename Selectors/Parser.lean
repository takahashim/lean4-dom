import Selectors.Ast
import Selectors.Component

/-!
# selector を読む（Selectors Level 4 §18・§19.1）

`parse a selector` は文字列を受け取り、complex selector の list か失敗を返す。
ここでは `Option SelectorList` で表す。`none` が仕様の failure である。

## 読み方

component value の列を **左から一度だけ** 走る。compound selector を組み立てながら、
combinator が来たら一つ前の compound を閉じる。`Complex` は右端の compound を
先頭に持つ向きなので、閉じた compound をそのまま `seq` の外側に積んでいける。

`:is()` のような引数付き pseudo-class は、引数が component の部分木になっているので
そこへ再帰する。停止は `csize`（component 木の大きさ）で与える。

## 仕様との差

* **namespace prefix は `*|` だけ受ける。** `ns|E` は宣言する手段が無いので失敗する。
  素の `E` は既定 namespace が無い状況と同じで、namespace を問わない（§6.1）。
* **pseudo-element は受けない。** `::before` も `:before` も失敗する。
-/

namespace Selectors

open Infra

/-! ## component 列の道具 -/

mutual

/-- component 一つの大きさ。停止性の尺度に使う。 -/
def csizeC : Component -> Nat
  | .tok _ => 1
  | .func _ a => 1 + csize a
  | .block _ a => 1 + csize a

/-- component 列の大きさ。 -/
def csize : List Component -> Nat
  | [] => 0
  | c :: t => csizeC c + csize t

end

theorem csizeC_pos (c : Component) : 0 < csizeC c := by
  cases c <;> (simp only [csizeC]; omega)

theorem csize_cons (c : Component) (l : List Component) :
    csize (c :: l) = csizeC c + csize l := by rw [csize]

/-- 先頭の whitespace を落とす。 -/
def dropWs : List Component -> List Component
  | .tok .whitespace :: rest => dropWs rest
  | l => l

def isComma : Component -> Bool
  | .tok .comma => true
  | _ => false

/-- forgiving な list で、失敗した項目を捨てて次の `,` の後ろまで進む。 -/
def dropToComma : List Component -> List Component
  | [] => []
  | c :: rest => if isComma c then rest else dropToComma rest

theorem dropToComma_size : ∀ (l : List Component), csize (dropToComma l) <= csize l
  | [] => by simp [dropToComma]
  | c :: rest => by
    rw [dropToComma, csize_cons]
    have h1 := csizeC_pos c
    have h2 := dropToComma_size rest
    split <;> omega

def isOfIdent : Component -> Bool
  | .tok (.ident s) => asciiLowercase s == "of"
  | _ => false

/-- `:nth-child(An+B of S)` を `An+B` と `S` に切る。最初の top-level の `of` で切る。 -/
def splitAtOf : List Component -> Option (List Component × List Component)
  | [] => none
  | c :: rest =>
    if isOfIdent c then some ([], rest)
    else
      match splitAtOf rest with
      | some (a, b) => some (c :: a, b)
      | none => none

theorem splitAtOf_size : ∀ (l a b : List Component),
    splitAtOf l = some (a, b) -> csize b <= csize l
  | [], _, _, h => by simp [splitAtOf] at h
  | c :: rest, a, b, h => by
    rw [splitAtOf] at h
    have hc := csizeC_pos c
    rw [csize_cons]
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      omega
    · split at h
      · next a' b' hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        have := splitAtOf_size rest a' b' hs
        omega
      · simp at h

/-! ## `<a-n-plus-b>`（CSS Syntax §9） -/

/-- `pre` に digit の列が続く形か。続くならその値。 -/
def digitsAfter (pre : String) (s : String) : Option Nat :=
  let p := pre.toList
  let l := s.toList
  if l.take p.length == p then
    let d := l.drop p.length
    if d.isEmpty || !d.all isAsciiDigit then none else some (digitsToNat d)
  else none

/-- 符号の無い整数。 -/
def signlessInt : List Component -> Option (Nat × List Component)
  | .tok (.number n) :: rest =>
    if n.isInteger && n.sign.isNone && 0 <= n.value then some (n.value.toNat, rest) else none
  | _ => none

/-- `An+B` の B 側。A は決まっている。 -/
def parseB (a : Int) (l : List Component) : Option (AnB × List Component) :=
  match dropWs l with
  | .tok (.number n) :: rest =>
    if n.isInteger && n.sign.isSome then some (⟨a, n.value⟩, rest) else some (⟨a, 0⟩, l)
  | .tok (.delim d) :: rest =>
    if d == CH_PLUS || d == CH_HYPHEN then
      match signlessInt (dropWs rest) with
      | some (v, r) => some (⟨a, if d == CH_HYPHEN then -(v : Int) else (v : Int)⟩, r)
      | none => none
    else some (⟨a, 0⟩, l)
  | _ => some (⟨a, 0⟩, l)

/-- `n` で始まる ident 形。`keywords` が false なら `odd`/`even` を受けない。 -/
def identAnB (keywords : Bool) (s : String) (rest : List Component) :
    Option (AnB × List Component) :=
  let s0 := asciiLowercase s
  if keywords && s0 == "odd" then some (⟨2, 1⟩, rest)
  else if keywords && s0 == "even" then some (⟨2, 0⟩, rest)
  else if s0 == "n" then parseB 1 rest
  else if s0 == "-n" then parseB (-1) rest
  else if s0 == "n-" then
    match signlessInt (dropWs rest) with
    | some (v, r) => some (⟨1, -(v : Int)⟩, r)
    | none => none
  else if s0 == "-n-" then
    match signlessInt (dropWs rest) with
    | some (v, r) => some (⟨-1, -(v : Int)⟩, r)
    | none => none
  else
    match digitsAfter "-n-" s0 with
    | some v => some (⟨-1, -(v : Int)⟩, rest)
    | none =>
      match digitsAfter "n-" s0 with
      | some v => some (⟨1, -(v : Int)⟩, rest)
      | none => none

/-- CSS Syntax §9.2 の `<a-n-plus-b>`。 -/
def parseAnB (l : List Component) : Option (AnB × List Component) :=
  match dropWs l with
  | .tok (.ident s) :: rest => identAnB true s rest
  | .tok (.number n) :: rest => if n.isInteger then some (⟨0, n.value⟩, rest) else none
  | .tok (.dimension n u) :: rest =>
    if !n.isInteger then none
    else
      let u0 := asciiLowercase u
      if u0 == "n" then parseB n.value rest
      else if u0 == "n-" then
        match signlessInt (dropWs rest) with
        | some (v, r) => some (⟨n.value, -(v : Int)⟩, r)
        | none => none
      else
        match digitsAfter "n-" u0 with
        | some v => some (⟨n.value, -(v : Int)⟩, rest)
        | none => none
  | .tok (.delim d) :: .tok (.ident s) :: rest =>
    -- `+` と ident の間に空白を置けない（§9.2 の †）
    if d == CH_PLUS then identAnB false s rest else none
  | _ => none

/-- `An+B` として全体を読み切る。 -/
def parseAnBFull (l : List Component) : Option AnB :=
  match parseAnB l with
  | some (ab, r) => if (dropWs r).isEmpty then some ab else none
  | none => none

/-! ## attribute selector（§6.3） -/

def attrFlag (name : String) (anyNs : Bool) (op : AttrOp) (v : String)
    (l : List Component) : Option Simple :=
  match dropWs l with
  | [] => some (.attr name anyNs (some ⟨op, v, .byDocument⟩))
  | .tok (.ident f) :: rest =>
    if !(dropWs rest).isEmpty then none
    else
      let f0 := asciiLowercase f
      if f0 == "i" then some (.attr name anyNs (some ⟨op, v, .insensitive⟩))
      else if f0 == "s" then some (.attr name anyNs (some ⟨op, v, .sensitive⟩))
      else none
  | _ => none

def attrValue (name : String) (anyNs : Bool) (op : AttrOp) (l : List Component) : Option Simple :=
  match dropWs l with
  | .tok (.string v) :: rest => attrFlag name anyNs op v rest
  | .tok (.ident v) :: rest => attrFlag name anyNs op v rest
  | _ => none

def attrTail (name : String) (anyNs : Bool) (l : List Component) : Option Simple :=
  match dropWs l with
  | [] => some (.attr name anyNs none)
  | .tok (.delim d) :: rest =>
    if d == CH_EQUALS then attrValue name anyNs .exact rest
    else
      match rest with
      | .tok (.delim e) :: rest2 =>
        if e != CH_EQUALS then none
        else if d == CH_TILDE then attrValue name anyNs .includes rest2
        else if d == CH_PIPE then attrValue name anyNs .dashMatch rest2
        else if d == CH_CARET then attrValue name anyNs .prefixMatch rest2
        else if d == CH_DOLLAR then attrValue name anyNs .suffixMatch rest2
        else if d == CH_STAR then attrValue name anyNs .substring rest2
        else none
      | _ => none
  | _ => none

/-- `[...]` の中身を読む。 -/
def parseAttrBlock (items : List Component) : Option Simple :=
  match dropWs items with
  | .tok (.delim d) :: .tok (.delim p) :: .tok (.ident name) :: rest =>
    if d == CH_STAR && p == CH_PIPE then attrTail name true rest else none
  | .tok (.ident name) :: rest => attrTail name false rest
  | _ => none

/-! ## pseudo-class -/

/-- 引数を取らない pseudo-class。名前は ASCII 大文字小文字を区別しない。 -/
def simplePseudo (n : String) : Option Simple :=
  match asciiLowercase n with
  | "root" => some .root
  | "empty" => some .empty
  | "first-child" => some .firstChild
  | "last-child" => some .lastChild
  | "only-child" => some .onlyChild
  | "first-of-type" => some .firstOfType
  | "last-of-type" => some .lastOfType
  | "only-of-type" => some .onlyOfType
  | "scope" => some .scope
  | _ => none

/-- `:nth-*()` の四種。 -/
def nthKindOf (n : String) : Option (NthKind × Bool) :=
  match asciiLowercase n with
  | "nth-child" => some (.child, true)
  | "nth-last-child" => some (.lastChild, true)
  | "nth-of-type" => some (.ofType, false)
  | "nth-last-of-type" => some (.lastOfType, false)
  | _ => none

/-! ## 走査

`ScanSt` は組み立て中の selector list を持つ。`cur` は「いま作っている compound より
左側」を表す complex で、compound を閉じるたびに外側へ伸びる。
-/

/-- 走査の設定。 -/
structure ScanCfg where
  /-- 失敗した項目を捨てる（`:is()` `:where()` の forgiving selector list）。 -/
  forgiving : Bool
  /-- relative selector。先頭に anchor を置く（`:has()` の引数）。 -/
  relative : Bool
  /--
  いま `:has()` の引数の中か。

  §14.10 は「`:has()` は入れ子にできない。`:has()` の中に `:has()` は書けない」と定める。
  `:is()` や `:not()` を挟んでも中は中なので、そこへも伝える。
  forgiving な list の中なら、その項目が落ちるだけで済む。
  -/
  inHas : Bool := false

/-- 走査の途中の状態。 -/
structure ScanSt where
  /-- 読み終えた complex selector。逆順。 -/
  done : List Complex
  /-- いま作っている compound より左側。 -/
  cur : Option Complex
  /-- いま作っている compound の前に置く combinator。 -/
  pend : Option Combinator
  /-- いま作っている compound。逆順。 -/
  parts : List Simple

def initSt (cfg : ScanCfg) (done : List Complex) : ScanSt :=
  { done := done
    cur := if cfg.relative then some (.one [.anchor]) else none
    pend := none
    parts := [] }

/-- 組み立て中の compound を閉じる。まだ何も読んでいなければ何もしない。 -/
def flush (st : ScanSt) : Option ScanSt :=
  match st.parts with
  | [] => some st
  | _ =>
    match st.cur with
    | none =>
      if st.pend.isSome then none
      else some { st with cur := some (.one st.parts.reverse), parts := [] }
    | some c =>
      let left := Complex.seq st.parts.reverse (st.pend.getD .descendant) c
      some { st with cur := some left, parts := [], pend := none }

/-- 一つの complex selector を閉じて `done` に積む。 -/
def finishComplex (cfg : ScanCfg) (st : ScanSt) : Option ScanSt :=
  match flush st with
  | none => none
  | some st' =>
    if st'.pend.isSome then none
    else
      match st'.cur with
      | none => none
      | some c => some (initSt cfg (c :: st'.done))

set_option maxHeartbeats 1000000 in
/--
component 列を selector list として読む。

`cfg.forgiving` なら、読めなかった項目を捨てて次の `,` から読み直す（§18.1）。
-/
def scan (cfg : ScanCfg) (st : ScanSt) : List Component -> Option SelectorList
  | [] =>
    match finishComplex cfg st with
    | some st' => some st'.done.reverse
    | none => if cfg.forgiving then some st.done.reverse else none
  | .tok .whitespace :: rest =>
    match flush st with
    | some st' => scan cfg st' rest
    | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .tok .comma :: rest =>
    match finishComplex cfg st with
    | some st' => scan cfg st' rest
    | none => if cfg.forgiving then scan cfg (initSt cfg st.done) rest else none
  | .tok (.delim d) :: rest =>
    if d == CH_GT || d == CH_PLUS || d == CH_TILDE then
      let k : Combinator :=
        if d == CH_GT then .child else if d == CH_PLUS then .nextSibling else .subsequentSibling
      match flush st with
      | some st' =>
        if st'.pend.isSome then
          if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
        else scan cfg { st' with pend := some k } rest
      | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
    else if d == CH_DOT then
      match rest with
      | .tok (.ident n) :: rest2 => scan cfg { st with parts := .cls n :: st.parts } rest2
      | r => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma r) else none
    else if d == CH_STAR then
      if !st.parts.isEmpty then
        if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
      else
        -- `*|E` と `*|*` だけ先読みする。それ以外の `*` は universal selector で、
        -- 後ろには subclass selector や combinator が続きうる。
        match rest with
        | .tok (.delim p) :: .tok (.ident n) :: rest2 =>
          if p == CH_PIPE then scan cfg { st with parts := [.typeSel n] } rest2
          else
            scan cfg { st with parts := [.univ] }
              (.tok (.delim p) :: .tok (.ident n) :: rest2)
        | .tok (.delim p) :: .tok (.delim q) :: rest2 =>
          if p == CH_PIPE && q == CH_STAR then scan cfg { st with parts := [.univ] } rest2
          else
            scan cfg { st with parts := [.univ] }
              (.tok (.delim p) :: .tok (.delim q) :: rest2)
        | r => scan cfg { st with parts := [.univ] } r
    else if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .tok (.ident n) :: rest =>
    if st.parts.isEmpty then scan cfg { st with parts := [.typeSel n] } rest
    else if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .tok (.hash v isId) :: rest =>
    if isId then scan cfg { st with parts := .id v :: st.parts } rest
    else if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .block b items :: rest =>
    match parseAttrBlock items with
    | some s => if b == .lbracket then scan cfg { st with parts := s :: st.parts } rest
                else if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest)
                else none
    | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .tok .colon :: .tok (.ident n) :: rest =>
    match simplePseudo n with
    | some s => scan cfg { st with parts := s :: st.parts } rest
    | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | .tok .colon :: .func name args :: rest =>
    let nm := asciiLowercase name
    if nm == "is" || nm == "where" then
      let inner : ScanCfg := { forgiving := true, relative := false, inHas := cfg.inHas }
      match scan inner (initSt inner []) args with
      | some l =>
        let s : Simple := if nm == "is" then .isSel l else .whereSel l
        scan cfg { st with parts := s :: st.parts } rest
      | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
    else if nm == "not" then
      let inner : ScanCfg := { forgiving := false, relative := false, inHas := cfg.inHas }
      match scan inner (initSt inner []) args with
      | some l => scan cfg { st with parts := .notSel l :: st.parts } rest
      | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
    else if nm == "has" then
      -- §14.10。`:has()` の中に `:has()` は書けない。
      if cfg.inHas then
        if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
      else
        let inner : ScanCfg := { forgiving := false, relative := true, inHas := true }
        match scan inner (initSt inner []) args with
        | some l => scan cfg { st with parts := .has l :: st.parts } rest
        | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
    else
      match nthKindOf nm with
      | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
      | some (kind, ofAllowed) =>
        match _hs : splitAtOf args with
        | none =>
          match parseAnBFull args with
          | some ab => scan cfg { st with parts := .nth kind ab none :: st.parts } rest
          | none => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
        | some (abPart, sPart) =>
          if !ofAllowed then
            if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
          else
            match parseAnBFull abPart with
            | none =>
              if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
            | some ab =>
              let inner : ScanCfg := { forgiving := false, relative := false, inHas := cfg.inHas }
              match scan inner (initSt inner []) sPart with
              | some l => scan cfg { st with parts := .nth kind ab (some l) :: st.parts } rest
              | none =>
                if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
  | _ :: rest => if cfg.forgiving then scan cfg (initSt cfg st.done) (dropToComma rest) else none
termination_by l => csize l
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (simp only [csize, csizeC]; omega)
      | (apply Nat.lt_of_le_of_lt (dropToComma_size _)
         simp only [csize, csizeC]; omega)
      | (apply Nat.lt_of_le_of_lt (dropToComma_size _)
         simp only [csize]
         have := csizeC_pos ‹Component›
         omega)
      | (apply Nat.lt_of_le_of_lt (splitAtOf_size _ _ _ (by assumption))
         simp only [csize, csizeC]; omega)

/-- §19.1 "parse a selector"。 -/
def parseSelector (input : String) : Option SelectorList :=
  match parseComponents input with
  | none => none
  | some cs =>
    let cfg : ScanCfg := { forgiving := false, relative := false }
    scan cfg (initSt cfg []) cs

end Selectors
