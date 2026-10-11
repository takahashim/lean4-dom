import Dom.Range.Api
import Dom.Mutation.Clone
import Dom.Mutation.Variadic

/-!
# `Range` の extract・clone the contents・`surroundContents()`（§5.5）

## subrange は状態に持たない

本文の step 17.3・20.3（clone the contents では 13.3・16.3）は subrange を **live range** として作り、
それを extract する。subrange が読まれるのは再帰した extract の step 1-11 だけで、そこまでに
木は変わらない（step 2 の collapsed、step 3 の端点、step 5 の common ancestor、step 7-10 の
contained / partially contained）。再帰の step 15 は subrange 自身を置き直すが、それを読む
ものは無い。だから subrange は端点の組（`RangeState`）として渡し、`s.ranges` には入れない。
`this` だけが `self = some i` として渡り、step 15 で置き直され、以後の mutation で調整される。

## subfragment を作らず、clone に直接入れる

本文は subrange を新しい DocumentFragment（subfragment）へ extract し、それを clone に append する
（step 17.4-17.5）。model は subfragment を作らず、clone を入れ先として再帰する。

違いが見えるのは三つの所だけで、どれも観測できない。

* **mutation record。** subfragment と clone は作ったばかりで、registered observer を持たず、
  祖先にも持たない。subfragment から clone へ子を移す insert と remove の record は、どの
  observer にも積まれない。外した contained child には transient registered observer が付きうるが、
  record の target は subfragment か clone で、外した node はその inclusive ancestor ではない。
* **live range と iterator。** 状態の live range も NodeIterator も、作ったばかりの node を指せない。
  NodeIterator の root が外した contained child であることはありうるが、その node を subfragment から
  外すときの pre-removing steps は「root なら何もしない」に当たる。
* **node の id。** subfragment に id を振らないので、作った node の id は **結果の DocumentFragment の
  tree order で、作った node だけを並べた順** になる。runner はその規則で id を振る。

## 失敗したときの状態

extract は step 15 で range を置き直し、step 16-20 で木を変えてから失敗しうる
（partially contained な doctype を clone して fragment に append するとき）。
失敗の結果はその時点の状態を持つ。append できなかった clone と、空のまま残った DocumentFragment は
どこからも辿れないので、`discard` で消す（`Dom/Mutation/Variadic.lean` と同じ約束）。
-/

namespace Dom

/--
DOM Standard §5.5 "get the common ancestor"。

start node の inclusive ancestor を近い順にたどり、end node の inclusive ancestor である最初のもの。
二つの端点が別の木にあれば無い（本文は親が null になるところで止まらない）。
-/
def commonAncestor (t : Tree) (r : RangeState) : Option NodeId :=
  (r.start.node :: ancestors t r.start.node).find? fun x => isInclusiveAncestorOf t x r.«end».node

/--
DOM Standard §5.5 "partially contained"。

node が start node と end node のどちらか一方だけの inclusive ancestor であること。
-/
def partiallyContained (t : Tree) (r : RangeState) (n : NodeId) : Bool :=
  isInclusiveAncestorOf t n r.start.node != isInclusiveAncestorOf t n r.«end».node

/-- 失敗に付いた状態を落とす。 -/
def dropErr {α : Type} : Except (DOMException × DOMState) α → Except DOMException α
  | .error (e, _) => .error e
  | .ok a => .ok a

@[simp] theorem dropErr_ok {α : Type} (a : α) :
    dropErr (.ok a : Except (DOMException × DOMState) α) = .ok a := rfl

@[simp] theorem dropErr_error {α : Type} (e : DOMException) (s : DOMState) :
    dropErr (.error (e, s) : Except (DOMException × DOMState) α) = .error e := rfl


/-- 失敗に、その時点の状態を付ける。 -/
def failWith {α : Type} (s : DOMState) : Except DOMException α → Except (DOMException × DOMState) α
  | .error e => .error (e, s)
  | .ok a => .ok a

/--
"clone of n" を作って data を置き換え、`into` に append する
（extract の step 4.1-4.3・16.1-16.3・19.1-19.3、clone the contents の対応する step）。

clone の node document は n の node document である（clone a node の document の既定値）。
append に失敗した clone はどこからも辿れないので消す。
-/
def appendDataClone (s : DOMState) (d : NodeData) (data : String) (into : NodeId) :
    Except (DOMException × DOMState) DOMState :=
  let (c, s₁) := cloneSingle s { d with data := data } d.ownerDocument
  match append s₁ c into with
  | .error e => .error (e, discard s₁ c)
  | .ok s₂ => .ok s₂

/--
"clone of n"（subtree は false）を作って `into` に append し、clone を返す
（extract の step 17.1-17.2・20.1-20.2、clone the contents の step 13.1-13.2・16.1-16.2）。
-/
def appendShallowClone (s : DOMState) (d : NodeData) (into : NodeId) :
    Except (DOMException × DOMState) (NodeId × DOMState) :=
  let (c, s₁) := cloneSingle s d d.ownerDocument
  match append s₁ c into with
  | .error e => .error (e, discard s₁ c)
  | .ok s₂ => .ok (c, s₂)

/-- step 7 の first partially contained child。 -/
def firstPartiallyContainedChild (t : Tree) (r : RangeState) (ca : NodeId) : Option NodeId :=
  if isInclusiveAncestorOf t r.start.node r.«end».node then none
  else (childrenOf t ca).find? (partiallyContained t r)

/-- step 9 の last partially contained child。 -/
def lastPartiallyContainedChild (t : Tree) (r : RangeState) (ca : NodeId) : Option NodeId :=
  if isInclusiveAncestorOf t r.«end».node r.start.node then none
  else (childrenOf t ca).reverse.find? (partiallyContained t r)

/-- step 10 の contained children。 -/
def containedChildren (t : Tree) (r : RangeState) (ca : NodeId) : List NodeId :=
  (childrenOf t ca).filter (containedInRange t r)

/--
CharacterData の一部を clone に写し、`cut` なら原本からその部分を消す
（extract の step 4・16・19、clone the contents の step 4・12・15）。

clone は n の data を `offset` から `count` 個の code unit に置き換えたもの。

n が CharacterData でないのは、range の start が end より後にあり、first（last）partially contained child が
end（start）node の側の CharacterData になったときだけである。本文はそのとき CharacterData でない
original start（end）node に substring data を求め、結果を定めない。model はそこで `outsideModel` を返す。
-/
def dataPart (cut : Bool) (s : DOMState) (n : NodeId) (offset count : Nat) (into : NodeId) :
    Except (DOMException × DOMState) DOMState :=
  match s.tree.get? n with
  | none => .error (.notFoundError, s)
  | some d =>
    if !d.kind.isCharacterData then .error (.outsideModel, s) else
    match failWith s (substringData s.tree n offset count) with
    | .error p => .error p
    | .ok sub =>
      match appendDataClone s d sub into with
      | .error p => .error p
      | .ok s₁ => if cut then failWith s₁ (replaceData s₁ n offset count "") else .ok s₁

/-- `extractInto` と `cloneContentsInto` が再帰を渡す形。 -/
abbrev Recur := DOMState → RangeState → NodeId → Except (DOMException × DOMState) DOMState

/--
first partially contained child の扱い（extract の step 16-17、clone the contents の step 12-13）。

CharacterData なら originalStartNode の start offset から後ろを写す（その child は
originalStartNode そのものである）。そうでなければ child を clone して `into` に append し、
(originalStart, (child, child の length)) の subrange を `recur` でその clone に入れる。
-/
def partialFirst (cut : Bool) (recur : Recur) (s : DOMState) (r : RangeState)
    (fp : Option NodeId) (into : NodeId) : Except (DOMException × DOMState) DOMState :=
  match fp with
  | none => .ok s
  | some fp =>
    match s.tree.get? fp with
    | none => .error (.notFoundError, s)
    | some fd =>
      if fd.kind.isCharacterData then
        dataPart cut s r.start.node r.start.offset (lengthOf s.tree r.start.node - r.start.offset) into
      else
        match appendShallowClone s fd into with
        | .error p => .error p
        | .ok (c, s₁) => recur s₁ { start := r.start, «end» := ⟨fp, lengthOf s₁.tree fp⟩ } c

/--
last partially contained child の扱い（extract の step 19-20、clone the contents の step 15-16）。
-/
def partialLast (cut : Bool) (recur : Recur) (s : DOMState) (r : RangeState)
    (lp : Option NodeId) (into : NodeId) : Except (DOMException × DOMState) DOMState :=
  match lp with
  | none => .ok s
  | some lp =>
    match s.tree.get? lp with
    | none => .error (.notFoundError, s)
    | some ld =>
      if ld.kind.isCharacterData then
        dataPart cut s r.«end».node 0 r.«end».offset into
      else
        match appendShallowClone s ld into with
        | .error p => .error p
        | .ok (c, s₁) => recur s₁ { start := ⟨lp, 0⟩, «end» := r.«end» } c

/-- contained children を順に `into` へ append する（extract の step 18）。 -/
def appendEach (s : DOMState) (into : NodeId) : List NodeId → Except (DOMException × DOMState) DOMState
  | [] => .ok s
  | c :: cs =>
    match append s c into with
    | .error e => .error (e, s)
    | .ok s₁ => appendEach s₁ into cs

/-- contained children を subtree ごと clone して `into` に append する（clone the contents の step 14）。 -/
def cloneEach (s : DOMState) (into : NodeId) : List NodeId → Except (DOMException × DOMState) DOMState
  | [] => .ok s
  | c :: cs =>
    match s.tree.get? c with
    | none => .error (.notFoundError, s)
    | some cd =>
      match cloneNodeIn s c cd.ownerDocument true with
      | .error e => .error (e, s)
      | .ok (copy, s₁) =>
        match append s₁ copy into with
        | .error e => .error (e, discard s₁ copy)
        | .ok s₂ => cloneEach s₂ into cs

/--
step 15 で `this` を (newNode, newOffset) に置く。subrange（`self = none`）は状態に無いので何もしない。

点は common ancestor があれば妥当である。妥当でなければ（model が別の木の端点を持つ range を
受けたとき）`outsideModel` にする。
-/
def setSelf (s : DOMState) (self : Option Nat) (bp : BoundaryPoint) :
    Except (DOMException × DOMState) DOMState :=
  match self with
  | none => .ok s
  | some i =>
    if checkValidBoundaryPoint s.tree bp then .ok (withRange s i { start := bp, «end» := bp })
    else .error (.outsideModel, s)

/--
DOM Standard §5.5 "extract"（`cut = true`）と "clone the contents"（`cut = false`）の、
step 1 の fragment を作った後の部分。`into` は fragment（再帰では clone）である。

二つの algorithm は同じ形をしていて、違いは次の三つだけである。

* extract は step 15 で `this` を置き直す（`self`）。clone the contents には無い（`self = none` で呼ぶ）。
* CharacterData の部分を写したあと、extract は原本からその部分を消す（`dataPart` の `cut`）。
* contained children を、extract は fragment へ移し、clone the contents は subtree ごと clone する。

fuel は木の深さで足りる（呼び出し側は `Tree.size + 1` を渡す）。
-/
def contentsInto (cut : Bool) : Nat → DOMState → RangeState → Option Nat → NodeId →
    Except (DOMException × DOMState) DOMState
  | 0, s, _, _, _ => .error (.outsideModel, s)
  | fuel + 1, s, r, self, into =>
    -- step 2
    if r.start == r.«end» then .ok s else
    match s.tree.get? r.start.node with
    | none => .error (.notFoundError, s)
    | some ds =>
      -- step 4
      if r.start.node == r.«end».node && ds.kind.isCharacterData then
        dataPart cut s r.start.node r.start.offset (r.«end».offset - r.start.offset) into
      else
      -- step 5
      match commonAncestor s.tree r with
      | none => .error (.outsideModel, s)
      | some ca =>
        let t := s.tree
        -- step 11
        if (containedChildren t r ca).any (fun c => kindOf t c == some .documentType) then
          .error (.hierarchyRequestError, s)
        else
        let recur : Recur := fun s' r' c => contentsInto cut fuel s' r' none c
        -- extract の step 12-15
        match setSelf s self (deleteContentsNewBP t r) with
        | .error p => .error p
        | .ok s₁ =>
          -- extract の step 16-17
          match partialFirst cut recur s₁ r (firstPartiallyContainedChild t r ca) into with
          | .error p => .error p
          | .ok s₂ =>
            -- extract の step 18
            let contained := containedChildren t r ca
            match (if cut then appendEach s₂ into contained else cloneEach s₂ into contained) with
            | .error p => .error p
            | .ok s₃ =>
              -- extract の step 19-20
              partialLast cut recur s₃ r (lastPartiallyContainedChild t r ca) into

/-- 失敗した状態から、空のまま残った fragment を消す。 -/
def discardOnError {α : Type} (frag : NodeId) :
    Except (DOMException × DOMState) α → Except (DOMException × DOMState) α
  | .error (e, s) => .error (e, discard s frag)
  | .ok a => .ok a

/--
`surroundContents()` が step 3 より後で失敗したとき、fragment に残った clone だけの部分木を消す。

step 1 が通れば partially contained な node は Text だけなので、fragment の子は CharacterData の
clone（step 4・16・19）か、木から移した contained child である。移した node があれば JavaScript から
その parent として fragment に辿れるので残す。clone だけなら辿れないので、`discardFragment` で消す
（`base` 以上の id が、この操作で作った node である）。
-/
def discardFragmentOnError {α : Type} (base frag : NodeId) :
    Except (DOMException × DOMState) α → Except (DOMException × DOMState) α
  | .error (e, s) =>
    .error (e, discardFragment s frag ((childrenOf s.tree frag).filter fun c => base.id ≤ c.id))
  | .ok a => .ok a

/--
step 1 の fragment を作る。node document は start node の node document である。
-/
def rangeFragment (s : DOMState) (r : RangeState) : Except DOMException (NodeId × DOMState) :=
  match s.tree.get? r.start.node with
  | none => .error .notFoundError
  | some ds => createDocumentFragment s ds.ownerDocument

/-- DOM Standard §5.5 `extractContents()`。fragment と状態を返す。 -/
def rangeExtractContents (s : DOMState) (i : Nat) :
    Except (DOMException × DOMState) (NodeId × DOMState) :=
  match s.ranges[i]? with
  | none => .error (.notFoundError, s)
  | some r =>
    match rangeFragment s r with
    | .error e => .error (e, s)
    | .ok (frag, s₁) =>
      discardOnError frag ((contentsInto true (s₁.tree.size + 1) s₁ r (some i) frag).map (frag, ·))

/-- DOM Standard §5.5 `cloneContents()`。fragment と状態を返す。 -/
def rangeCloneContents (s : DOMState) (i : Nat) :
    Except (DOMException × DOMState) (NodeId × DOMState) :=
  match s.ranges[i]? with
  | none => .error (.notFoundError, s)
  | some r =>
    match rangeFragment s r with
    | .error e => .error (e, s)
    | .ok (frag, s₁) =>
      discardOnError frag ((contentsInto false (s₁.tree.size + 1) s₁ r none frag).map (frag, ·))

/-- step 1：start node か end node の inclusive ancestor のうち、partially contained で Text でないものがある。 -/
def partiallyContainsNonText (t : Tree) (r : RangeState) : Bool :=
  ((r.start.node :: ancestors t r.start.node) ++ (r.«end».node :: ancestors t r.«end».node)).any
    fun n => partiallyContained t r n && !((kindOf t n).map NodeKind.isText).getD false

/--
DOM Standard §5.5 `surroundContents(newParent)`。

step 6 で newParent に append したあとの fragment は空で、どこからも辿れないので消す。
step 3 より後で失敗したときは、その時点の状態を返す（辿れなくなった fragment は消す。`discardFragmentOnError`）。
-/
def rangeSurroundContents (s : DOMState) (i : Nat) (newParent : NodeId) :
    Except (DOMException × DOMState) DOMState :=
  match s.ranges[i]? with
  | none => .error (.notFoundError, s)
  | some r =>
    match s.tree.get? newParent with
    | none => .error (.notFoundError, s)
    | some np =>
      -- step 1
      if partiallyContainsNonText s.tree r then .error (.invalidStateError, s)
      -- step 2
      else if np.kind == .document || np.kind == .documentType || np.kind == .documentFragment then
        .error (.invalidNodeTypeError, s)
      else
        -- step 3
        match rangeExtractContents s i with
        | .error p => .error p
        | .ok (frag, s₁) =>
          discardFragmentOnError (freshId s.tree) frag do
            -- step 4
            let s₂ ← failWith s₁ (if (childrenOf s₁.tree newParent).isEmpty then .ok s₁
              else replaceAll s₁ none newParent)
            -- step 5
            let s₃ ← failWith s₂ (rangeInsertNode s₂ i newParent)
            -- step 6
            let s₄ ← failWith s₃ (append s₃ frag newParent)
            -- step 7
            let s₅ ← failWith s₄ (rangeSelectNode s₄ i newParent)
            return discard s₅ frag

@[simp] theorem dropErr_failWith {α : Type} (s : DOMState) (r : Except DOMException α) :
    dropErr (failWith s r) = r := by
  cases r <;> rfl

/-- DOM Standard §5.5 `commonAncestorContainer`。 -/
def rangeCommonAncestorContainer (s : DOMState) (i : Nat) : Except DOMException NodeId :=
  match s.ranges[i]? with
  | none => .error .notFoundError
  | some r =>
    match commonAncestor s.tree r with
    | none => .error .outsideModel
    | some ca => .ok ca

end Dom
