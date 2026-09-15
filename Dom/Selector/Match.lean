import Dom.Basic.Order
import Dom.Attribute.Algorithms
import Selectors.Parser

/-!
# selector を element に当てる（Selectors Level 4 §17）

`match a selector against an element` を `Bool` で表す。文脈は `MatchCtx` にまとめた。
scoping root（`:scope`）と `:has()` の anchor を持つ。

停止は **selector の大きさ** で与える。木をたどるのは combinator と `:has()` の
ときだけで、そのときは必ず selector が小さくなっているからである。

## 仕様との差

* **`[attr=value]` の既定の大文字小文字は常に区別する。** HTML が定める
  「大文字小文字を区別しない attribute」の一覧は model の対象外である。
  `i` / `s` flag は仕様どおりに効く。
* **quirks mode を持たない。** class と id は常に大文字小文字を区別する。
-/

namespace Dom

open Infra Selectors

/-! ## 文字列の道具 -/

def hasPrefixL : List Char -> List Char -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && hasPrefixL as bs

def hasInfixL (p : List Char) : List Char -> Bool
  | [] => hasPrefixL p []
  | c :: t => hasPrefixL p (c :: t) || hasInfixL p t

def hasSuffixL (p l : List Char) : Bool := hasPrefixL p.reverse l.reverse

/-- ASCII whitespace で区切る。空の欠片は落とす。 -/
def splitWsAux (acc : List Char) : List Char -> List (List Char)
  | [] => if acc.isEmpty then [] else [acc.reverse]
  | c :: rest =>
    if isAsciiWhitespace c then
      (if acc.isEmpty then [] else [acc.reverse]) ++ splitWsAux [] rest
    else splitWsAux (c :: acc) rest

/-! ## 木の道具 -/

/-- 照合の文脈。 -/
structure MatchCtx where
  tree : Tree
  /-- `:scope` が指す node。 -/
  scope : Option NodeId := none
  /-- `:has()` の anchor。 -/
  anchor : Option NodeId := none

def isElementNode (t : Tree) (n : NodeId) : Bool := kindOf t n == some NodeKind.element

def elementChildrenOf (t : Tree) (n : NodeId) : List NodeId :=
  (childrenOf t n).filter (isElementNode t)

/-- §3.1 の inclusive sibling のうち element であるもの。parent が無ければ自分だけ。 -/
def elementSiblings (t : Tree) (n : NodeId) : List NodeId :=
  match parentOf t n with
  | none => [n]
  | some p => elementChildrenOf t p

/-- 同じ type（namespace と local name）か。 -/
def sameTypeAs (t : Tree) (d : NodeData) (m : NodeId) : Bool :=
  match t.get? m with
  | none => false
  | some e => e.namespace == d.namespace && e.localName == d.localName

/--
combinator の左に来られる node の候補。

ancestor 側は element でない node も返す。scoping root が `Document` や
`DocumentFragment` のとき、仕様はそれを「root element の parent としてふるまう
featureless な node」として扱い、`:scope > .foo` が通るようにしているためである
（§4.4）。featureless なので、`matchSimple` はそこで `:scope` しか通さない。
-/
def combCandidates (t : Tree) (comb : Combinator) (n : NodeId) : List NodeId :=
  match comb with
  | .descendant => ancestors t n
  | .child =>
    match parentOf t n with
    | none => []
    | some p => [p]
  | .nextSibling =>
    match parentOf t n with
    | none => []
    | some p =>
      match ((elementChildrenOf t p).takeWhile (fun m => m != n)).getLast? with
      | none => []
      | some m => [m]
  | .subsequentSibling =>
    match parentOf t n with
    | none => []
    | some p => (elementChildrenOf t p).takeWhile (fun m => m != n)

/-- `:empty` を壊さない子か。comment と PI、それに空白だけの text は数えない。 -/
def emptyOk (t : Tree) (c : NodeId) : Bool :=
  match t.get? c with
  | none => true
  | some d =>
    match d.kind with
    | .comment => true
    | .processingInstruction => true
    | .text => d.data.toList.all isAsciiWhitespace
    | .cdataSection => d.data.toList.all isAsciiWhitespace
    | _ => false

/-- selector の中の attribute 名を、element に合わせて正規化する。 -/
def attrNameInSelector (t : Tree) (d : NodeData) (name : String) : String :=
  if d.namespace == some htmlNamespace && isHTMLDocumentOf t d then asciiLowercase name
  else name

/-- `[name]` が指す attribute。 -/
def selectorAttr (t : Tree) (d : NodeData) (anyNs : Bool) (name : String) : Option Attr :=
  let nm := attrNameInSelector t d name
  d.attributes.find? (fun a => a.localName == nm && (anyNs || a.namespace.isNone))

/-- 素の attribute 名（`class` や `id`）。namespace は持たない。 -/
def plainAttr (d : NodeData) (name : String) : Option String :=
  (d.attributes.find? (fun a => a.localName == name && a.namespace.isNone)).map Attr.value

/-- §6.3 の値の照合。 -/
def attrTestHolds (test : AttrTest) (value : String) : Bool :=
  let fold : List Char -> List Char :=
    match test.case with
    | .insensitive => fun l => l.map asciiLowerChar
    | _ => fun l => l
  let v := fold value.toList
  let w := fold test.value.toList
  match test.op with
  | .exact => v == w
  | .includes => !w.isEmpty && !(w.any isAsciiWhitespace) && (splitWsAux [] v).any (fun x => x == w)
  | .dashMatch => v == w || hasPrefixL (w ++ ['-']) v
  | .prefixMatch => !w.isEmpty && hasPrefixL w v
  | .suffixMatch => !w.isEmpty && hasSuffixL w v
  | .substring => !w.isEmpty && hasInfixL w v

/-- type selector の照合。HTML document の HTML element だけ ASCII 非依存にする。 -/
def typeHolds (t : Tree) (d : NodeData) (name : String) : Bool :=
  if d.namespace == some htmlNamespace && isHTMLDocumentOf t d then
    asciiLowercase name == d.localName
  else name == d.localName

/-- `An+B` が index `i`（1 始まり）に当たるか。 -/
def anbMatches (ab : AnB) (i : Nat) : Bool :=
  let d : Int := (i : Int) - ab.b
  if ab.a == 0 then d == 0
  else if ab.a > 0 then decide (0 <= d) && d % ab.a == 0
  else decide (d <= 0) && (-d) % (-ab.a) == 0

/-- `l` の中での `n` の位置（0 始まり）。 -/
def indexOfNode (l : List NodeId) (n : NodeId) : Option Nat := l.findIdx? (fun m => m == n)

/-! ## selector の大きさ -/

mutual

def oSize : Option (List Complex) -> Nat
  | none => 0
  | some l => lSize l

def sSize : Simple -> Nat
  | .nth _ _ o => 1 + oSize o
  | .isSel l => 1 + lSize l
  | .whereSel l => 1 + lSize l
  | .notSel l => 1 + lSize l
  | .has l => 1 + lSize l
  | _ => 1

def cpSize : List Simple -> Nat
  | [] => 1
  | s :: t => sSize s + cpSize t

def cxSize : Complex -> Nat
  | .one p => 1 + cpSize p
  | .seq p _ l => 1 + cpSize p + cxSize l

def lSize : List Complex -> Nat
  | [] => 1
  | c :: t => cxSize c + lSize t

end

theorem sSize_pos (s : Simple) : 0 < sSize s := by
  cases s <;> simp [sSize] <;> omega

theorem cxSize_pos (c : Complex) : 0 < cxSize c := by
  cases c <;> simp [cxSize] <;> omega

theorem cpSize_pos : ∀ (l : List Simple), 0 < cpSize l
  | [] => by simp [cpSize]
  | s :: t => by
    rw [cpSize]
    have := sSize_pos s
    have := cpSize_pos t
    omega

theorem lSize_pos : ∀ (l : List Complex), 0 < lSize l
  | [] => by simp [lSize]
  | c :: t => by
    rw [lSize]
    have := cxSize_pos c
    have := lSize_pos t
    omega

theorem sSize_lt_cpSize : ∀ (l : List Simple) (s : Simple), s ∈ l -> sSize s < cpSize l
  | [], _, h => absurd h (by simp)
  | x :: rest, s, h => by
    rw [cpSize]
    rcases List.mem_cons.mp h with rfl | hrest
    · have := cpSize_pos rest
      omega
    · have := sSize_lt_cpSize rest s hrest
      have := sSize_pos x
      omega

theorem cxSize_lt_lSize : ∀ (l : List Complex) (c : Complex), c ∈ l -> cxSize c < lSize l
  | [], _, h => absurd h (by simp)
  | x :: rest, c, h => by
    rw [lSize]
    rcases List.mem_cons.mp h with rfl | hrest
    · have := lSize_pos rest
      omega
    · have := cxSize_lt_lSize rest c hrest
      have := cxSize_pos x
      omega

/-! ## `:scope` を含まない selector

`matchSimple` が `ctx.scope` を読むのは `Simple.scope` の枝だけである。
だから `:scope` を含まない selector は scoping root に依らない。
`Dom/Selector/Spec.lean` の `matchSelList_scope_irrelevant` がそれを言う。
-/

/-- `:scope` そのものか。featureless な node に当たるのはこれだけである。 -/
def isScopeSelector : Simple -> Bool
  | .scope => true
  | _ => false

mutual

def scopeFreeS : Simple -> Bool
  | .scope => false
  | .nth _ _ o => scopeFreeO o
  | .isSel l => scopeFreeL l
  | .whereSel l => scopeFreeL l
  | .notSel l => scopeFreeL l
  | .has l => scopeFreeL l
  | _ => true

def scopeFreeO : Option (List Complex) -> Bool
  | none => true
  | some l => scopeFreeL l

def scopeFreeCp : List Simple -> Bool
  | [] => true
  | s :: rest => scopeFreeS s && scopeFreeCp rest

def scopeFreeCx : Complex -> Bool
  | .one p => scopeFreeCp p
  | .seq p _ l => scopeFreeCp p && scopeFreeCx l

def scopeFreeL : List Complex -> Bool
  | [] => true
  | c :: rest => scopeFreeCx c && scopeFreeL rest

end

theorem isScopeSelector_eq_false {s : Simple} (h : scopeFreeS s = true) :
    isScopeSelector s = false := by
  cases s <;> simp [isScopeSelector] <;> simp [scopeFreeS] at h

theorem scopeFreeS_of_mem : ∀ (l : List Simple) (s : Simple),
    s ∈ l -> scopeFreeCp l = true -> scopeFreeS s = true
  | [], _, h, _ => absurd h (by simp)
  | x :: rest, s, h, hf => by
    rw [scopeFreeCp, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp h with rfl | hrest
    · exact hf.1
    · exact scopeFreeS_of_mem rest s hrest hf.2

theorem scopeFreeCx_of_mem : ∀ (l : List Complex) (c : Complex),
    c ∈ l -> scopeFreeL l = true -> scopeFreeCx c = true
  | [], _, h, _ => absurd h (by simp)
  | x :: rest, c, h, hf => by
    rw [scopeFreeL, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp h with rfl | hrest
    · exact hf.1
    · exact scopeFreeCx_of_mem rest c hrest hf.2

/-! ## 照合

`List.attach` を使うのは、selector list の要素が元の list に属することを
停止性の証明で使うためである。node の list を回るところでは selector が
変わらないので、その必要は無い。
-/

mutual

/-- §17.1 "match a selector against an element"。 -/
def matchSelList (ctx : MatchCtx) (l : List Complex) (n : NodeId) : Bool :=
  l.attach.any (fun c => matchComplex ctx c.1 n)
termination_by lSize l
decreasing_by
  simp_wf
  exact cxSize_lt_lSize _ _ c.2

/-- §17.1 "match a complex selector against an element"。右から左へ見る。 -/
def matchComplex (ctx : MatchCtx) (c : Complex) (n : NodeId) : Bool :=
  match c with
  | .one parts => matchCompound ctx parts n
  | .seq parts comb left =>
    matchCompound ctx parts n &&
      (combCandidates ctx.tree comb n).any (fun m => matchComplex ctx left m)
termination_by cxSize c
decreasing_by
  all_goals simp_wf
  all_goals simp only [cxSize]
  all_goals omega

/-- compound selector は、含む simple selector のすべてに当たること。 -/
def matchCompound (ctx : MatchCtx) (parts : List Simple) (n : NodeId) : Bool :=
  parts.attach.all (fun s => matchSimple ctx s.1 n)
termination_by cpSize parts
decreasing_by
  simp_wf
  exact sSize_lt_cpSize _ _ s.2

/-- simple selector 一つの照合。 -/
def matchSimple (ctx : MatchCtx) (s : Simple) (n : NodeId) : Bool :=
  match ctx.tree.get? n with
  | none => false
  | some d =>
    -- element でない node は featureless である。`:scope` だけが当たる。
    if d.kind != NodeKind.element then isScopeSelector s && ctx.scope == some n
    else
      match s with
      | .typeSel name => typeHolds ctx.tree d name
      | .univ => true
      | .id v =>
        match plainAttr d "id" with
        | none => false
        | some av => av == v
      | .cls v =>
        match plainAttr d "class" with
        | none => false
        | some av => (splitWsAux [] av.toList).any (fun w => w == v.toList)
      | .attr name anyNs test =>
        match selectorAttr ctx.tree d anyNs name with
        | none => false
        | some a =>
          match test with
          | none => true
          | some tst => attrTestHolds tst a.value
      | .root =>
        match parentOf ctx.tree n with
        | none => false
        | some p => kindOf ctx.tree p == some NodeKind.document
      | .empty => (childrenOf ctx.tree n).all (fun c => emptyOk ctx.tree c)
      | .firstChild => (elementSiblings ctx.tree n).head? == some n
      | .lastChild => (elementSiblings ctx.tree n).getLast? == some n
      | .onlyChild => (elementSiblings ctx.tree n).length == 1
      | .firstOfType =>
        ((elementSiblings ctx.tree n).filter (sameTypeAs ctx.tree d)).head? == some n
      | .lastOfType =>
        ((elementSiblings ctx.tree n).filter (sameTypeAs ctx.tree d)).getLast? == some n
      | .onlyOfType =>
        ((elementSiblings ctx.tree n).filter (sameTypeAs ctx.tree d)).length == 1
      | .nth kind ab ofSel =>
        let sibs := elementSiblings ctx.tree n
        let pool :=
          match kind with
          | .child | .lastChild =>
            match ofSel with
            | none => sibs
            | some l => sibs.filter (fun m => matchSelList ctx l m)
          | .ofType | .lastOfType => sibs.filter (sameTypeAs ctx.tree d)
        let ordered :=
          match kind with
          | .child | .ofType => pool
          | .lastChild | .lastOfType => pool.reverse
        match indexOfNode ordered n with
        | none => false
        | some i => anbMatches ab (i + 1)
      | .isSel l => matchSelList ctx l n
      | .whereSel l => matchSelList ctx l n
      | .notSel l => !matchSelList ctx l n
      | .has l =>
        let cands := preorder ctx.tree (root ctx.tree n)
        cands.any (fun c => matchSelList { ctx with anchor := some n } l c)
      | .scope => ctx.scope == some n
      | .anchor => ctx.anchor == some n
termination_by sSize s
decreasing_by
  all_goals simp_wf
  all_goals simp only [sSize, oSize]
  all_goals omega

end

end Dom
