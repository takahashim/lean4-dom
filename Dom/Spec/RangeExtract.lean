import Dom.Spec.RangeDelete
import Dom.Spec.RangeInsert
import Dom.Spec.TextQuery
import Dom.Spec.Create
import Dom.Properties.Clone
import Dom.Spec.ReplaceAllSound
import Dom.Spec.RangeSet

/-!
# extract・clone the contents・`surroundContents()` の関係意味論（§5.5）

"extract"（`cut = true`）と "clone the contents"（`cut = false`）は同じ形をしているので、
一つの関係 `ContentsInto` で書く。違いは三つで、関係の中で `cut` を見て分ける。

* extract は step 15 で `this` を置き直す（`SelfSet`）。clone the contents は `self = none` で呼ぶ。
* CharacterData の部分を clone したあと、extract は原本からその部分を消す（`DataPartResult`）。
* contained children を、extract は fragment へ append し（step 18）、clone the contents は
  subtree ごと clone して append する（step 14）。

step 1 の fragment は、関係の外で作って `into` として渡す（`ExtractResult` ほか）。

## subfragment

本文の step 17.3-17.5（20.3-20.5）は subrange を新しい DocumentFragment（subfragment）へ extract し、
それを clone に append する。関係も同じ順に書く（`SubContents`）。

## 本文と違う所

**subrange は状態に持たない。** 本文の subrange は live range だが、読まれるのは再帰した algorithm の
step 1-11（木が変わる前）だけで、step 15 で置き直されたものは読まれない。だから端点の組として渡す。

## 例外の状態

本文の例外は途中で投げられ、それまでの変更は残る。ほかの関係と同じく、関係は例外の種類だけを述べ、
その時点の状態は述べない（比べるのは差分テストである）。
-/

namespace Dom.Spec

open Dom

/-! ## §5.5 の語彙 -/

/--
**§5.5 "get the common ancestor"。**

container を start node から始め、end node の inclusive ancestor になるまで parent へ上る。止まる所は
「start node の inclusive ancestor で end node の inclusive ancestor であり、それより start node に
近い start node の inclusive ancestor はどれも end node の inclusive ancestor でない」ものとして一つに決まる。
-/
def CommonAncestor (t : Tree) (r : RangeState) (ca : NodeId) : Prop :=
  InclusiveAncestor t ca r.start.node ∧ InclusiveAncestor t ca r.«end».node ∧
    ∀ x, InclusiveAncestor t x r.start.node → Ancestor t ca x →
      ¬ InclusiveAncestor t x r.«end».node

/-- **§5.5 partially contained。** start node と end node のどちらか一方だけの inclusive ancestor である。 -/
def PartiallyContained (t : Tree) (r : RangeState) (n : NodeId) : Prop :=
  (InclusiveAncestor t n r.start.node ∧ ¬ InclusiveAncestor t n r.«end».node) ∨
    (¬ InclusiveAncestor t n r.start.node ∧ InclusiveAncestor t n r.«end».node)

/--
step 6-7：first partially contained child。original start node が original end node の inclusive ancestor
なら null、そうでなければ common ancestor の子のうち partially contained な最初のもの。
-/
def FirstPartial (t : Tree) (r : RangeState) (ca : NodeId) : Option NodeId → Prop
  | none => InclusiveAncestor t r.start.node r.«end».node ∨
      ∀ c ∈ childrenOf t ca, ¬ PartiallyContained t r c
  | some c => ¬ InclusiveAncestor t r.start.node r.«end».node ∧
      ∃ A B, childrenOf t ca = A ++ c :: B ∧ PartiallyContained t r c ∧
        ∀ x ∈ A, ¬ PartiallyContained t r x

/-- step 8-9：last partially contained child。 -/
def LastPartial (t : Tree) (r : RangeState) (ca : NodeId) : Option NodeId → Prop
  | none => InclusiveAncestor t r.«end».node r.start.node ∨
      ∀ c ∈ childrenOf t ca, ¬ PartiallyContained t r c
  | some c => ¬ InclusiveAncestor t r.«end».node r.start.node ∧
      ∃ A B, childrenOf t ca = A ++ c :: B ∧ PartiallyContained t r c ∧
        ∀ x ∈ B, ¬ PartiallyContained t r x

/-- step 10：contained children。common ancestor の子のうち contained なものを tree order で並べた列。 -/
def ContainedChildren (t : Tree) (r : RangeState) (ca : NodeId) (l : List NodeId) : Prop :=
  l.Sublist (childrenOf t ca) ∧ ∀ c ∈ childrenOf t ca, c ∈ l ↔ Contained t r c

/-- step 12-15：`this` を (newNode, newOffset) に置く。subrange は状態に無い。 -/
def SelfSet (s : DOMState) (self : Option Nat) (bp : BoundaryPoint) (s' : DOMState) : Prop :=
  (self = none ∧ s' = s) ∨
    (∃ i, self = some i ∧ s' = { s with ranges := s.ranges.set i { start := bp, «end» := bp } })

/-! ## clone -/

/--
"clone a node"（subtree は false）で n の clone c を作り、その data を x にする。

copy は原本と同じ kind・名前・attribute（id を除く）を持ち、parent も children も持たず、
原本の node document に属する（§4.4 "clone a single node"、document の既定値は n の node document）。
-/
def SingleClone (s : DOMState) (n : NodeId) (x : String) (c : NodeId) (s' : DOMState) : Prop :=
  ∃ d cd, s.tree.get? n = some d ∧ CreatesNode s c s' cd ∧ cd.shapeAnon = d.shapeAnon ∧
    cd.data = x ∧ cd.ownerDocument = d.ownerDocument

/--
"clone a node"（subtree は true）で n の clone c を作る。

木にあった node は変わらず、c は新しい node で、c を根とする subtree は n を根とする subtree の copy
（`CloneOf`）であり、live range は動かない。
-/
def DeepClone (s : DOMState) (n c : NodeId) (s' : DOMState) : Prop :=
  (∀ m md, s.tree.get? m = some md → s'.tree.get? m = some md) ∧
    s.tree.get? c = none ∧ CloneOf s'.tree c n ∧ s'.ranges = s.ranges

/-! ## node を作る段 -/

/--
**node を作る三つの段。** 本文は新しい node の id を決めないので、本文の関係（`Alloc.spec`）は木に無い id なら
何でも許す。そのままでは関係は結果を id の付け替えを除いてしか決めない。一意性と completeness は、model の
割り当て（`freshId` と attribute の id。`Dom/Spec/RangeExtractComplete.lean` の `Alloc.model`）で id を決めた
関係について述べる。
-/
structure Alloc where
  /-- "clone a node"（subtree は false）で n の clone c を作り、data を x にする。 -/
  single : DOMState → NodeId → String → NodeId → DOMState → Prop
  /-- node document が doc の新しい DocumentFragment を作る（extract の step 1）。 -/
  fragment : DOMState → NodeId → NodeId → DOMState → Prop
  /-- "clone a node"（subtree は true）で n の clone c を作る。 -/
  deep : DOMState → NodeId → NodeId → DOMState → Prop

/-- 本文どおりの段。新しい node の id は、木に無いものなら何でもよい。 -/
def Alloc.spec : Alloc where
  single := SingleClone
  fragment s doc sub s' := CreatesNode s sub s' { kind := .documentFragment, ownerDocument := doc }
  deep := DeepClone

/--
CharacterData の一部を写す（extract の step 4・16・19、clone the contents の step 4・12・15）。

n の data の offset から count 個を substring data で取り、n の clone の data にして `into` に append する。
`cut` なら（extract）n の data のその部分を replace data で消す。
-/
def DataPartResult (A : Alloc) (cut : Bool) (s : DOMState) (n : NodeId) (offset count : Nat)
    (into : NodeId) : Except DOMException DOMState → Prop
  | res =>
    (∃ e, SubstringResult s.tree n offset count (.error e) ∧ res = .error e) ∨
    (∃ x c s₁, SubstringResult s.tree n offset count (.ok x) ∧ A.single s n x c s₁ ∧
      AndThen (PreInsertResult s₁ c into none)
        (fun s₂ res₂ => (cut = true ∧ ReplaceDataResult s₂ n offset count "" res₂) ∨
          (cut = false ∧ res₂ = .ok s₂))
        res)

/-- extract の step 18：contained children を順に `into` へ append する。 -/
def AppendEachResult (into : NodeId) : DOMState → List NodeId → Except DOMException DOMState → Prop
  | s, [], res => res = .ok s
  | s, c :: cs, res =>
    AndThen (PreInsertResult s c into none) (fun s₁ res₁ => AppendEachResult into s₁ cs res₁) res

/-- clone the contents の step 14：contained children を subtree ごと clone して順に `into` へ append する。 -/
def CloneEachResult (A : Alloc) (into : NodeId) :
    DOMState → List NodeId → Except DOMException DOMState → Prop
  | s, [], res => res = .ok s
  | s, c :: cs, res =>
    ∃ copy s₁, A.deep s c copy s₁ ∧
      AndThen (PreInsertResult s₁ copy into none) (fun s₂ res₂ => CloneEachResult A into s₂ cs res₂) res

/-- step 18（extract）と step 14（clone the contents）。 -/
def ContainedStep (A : Alloc) (cut : Bool) (s : DOMState) (into : NodeId) (cs : List NodeId)
    (res : Except DOMException DOMState) : Prop :=
  (cut = true ∧ AppendEachResult into s cs res) ∨ (cut = false ∧ CloneEachResult A into s cs res)

/-! ## 全体 -/

/-- step 5-11 で決まるもの。common ancestor、first / last partially contained child、contained children。 -/
structure Setup (t : Tree) (r : RangeState) (ca : NodeId) (fp lp : Option NodeId)
    (cs : List NodeId) : Prop where
  common : CommonAncestor t r ca
  first : FirstPartial t r ca fp
  last : LastPartial t r ca lp
  contained : ContainedChildren t r ca cs

/-- step 2-4 を通って step 5 へ進む条件：collapsed でなく、同じ CharacterData の中でもない。 -/
def General (t : Tree) (r : RangeState) : Prop :=
  r.start ≠ r.«end» ∧ ¬ (r.start.node = r.«end».node ∧ IsCharacterData t r.start.node)

mutual

/--
**§5.5 "extract"（`cut = true`）と "clone the contents"（`cut = false`）の、step 1 の後の部分。**

`into` は step 1 の fragment（再帰では partially contained child の clone）、`self` は range が `this`
なら `some i`、subrange なら `none` である。
-/
inductive ContentsInto (A : Alloc) (cut : Bool) :
    DOMState → RangeState → Option Nat → NodeId → Except DOMException DOMState → Prop where
  /-- step 2：collapsed なら何もしない。 -/
  | collapsed {s r self into} : r.start = r.«end» → ContentsInto A cut s r self into (.ok s)
  /-- step 4：start node と end node が同じ CharacterData。 -/
  | single {s r self into res} : r.start ≠ r.«end» → r.start.node = r.«end».node →
      IsCharacterData s.tree r.start.node →
      DataPartResult A cut s r.start.node r.start.offset (r.«end».offset - r.start.offset) into res →
      ContentsInto A cut s r self into res
  /-- step 11：contained child に doctype がある。 -/
  | doctype {s r self into ca fp lp cs} : General s.tree r → Setup s.tree r ca fp lp cs →
      (∃ c ∈ cs, KindIs s.tree c .documentType) →
      ContentsInto A cut s r self into (.error .hierarchyRequestError)
  /-- step 16-17 が失敗する。 -/
  | firstError {s r self into ca fp lp cs bp s₁ e} : General s.tree r → Setup s.tree r ca fp lp cs →
      (∀ c ∈ cs, ¬ KindIs s.tree c .documentType) → DeleteNewBP s.tree r bp → SelfSet s self bp s₁ →
      PartialFirst A cut s₁ r fp into (.error e) →
      ContentsInto A cut s r self into (.error e)
  /-- step 18 が失敗する。 -/
  | containedError {s r self into ca fp lp cs bp s₁ s₂ e} : General s.tree r →
      Setup s.tree r ca fp lp cs → (∀ c ∈ cs, ¬ KindIs s.tree c .documentType) →
      DeleteNewBP s.tree r bp → SelfSet s self bp s₁ →
      PartialFirst A cut s₁ r fp into (.ok s₂) → ContainedStep A cut s₂ into cs (.error e) →
      ContentsInto A cut s r self into (.error e)
  /-- step 19-20 まで進む。 -/
  | last {s r self into ca fp lp cs bp s₁ s₂ s₃ res} : General s.tree r →
      Setup s.tree r ca fp lp cs → (∀ c ∈ cs, ¬ KindIs s.tree c .documentType) →
      DeleteNewBP s.tree r bp → SelfSet s self bp s₁ →
      PartialFirst A cut s₁ r fp into (.ok s₂) → ContainedStep A cut s₂ into cs (.ok s₃) →
      PartialLast A cut s₃ r lp into res →
      ContentsInto A cut s r self into res

/--
step 16-17（clone the contents の 12-13）：first partially contained child の扱い。

CharacterData なら（その child は original start node である）start offset から後ろを写す。
そうでなければ child を clone して `into` に append し、(original start, (child, child の length)) の
subrange を extract した subfragment をその clone へ append する（`SubContents`）。
-/
inductive PartialFirst (A : Alloc) (cut : Bool) :
    DOMState → RangeState → Option NodeId → NodeId → Except DOMException DOMState → Prop where
  | none {s r into} : PartialFirst A cut s r none into (.ok s)
  | data {s r fp into res} : IsCharacterData s.tree fp →
      DataPartResult A cut s r.start.node r.start.offset (lengthOf s.tree r.start.node - r.start.offset)
        into res →
      PartialFirst A cut s r (some fp) into res
  | cloneError {s r fp into c s₁ e} : InTree s.tree fp → ¬ IsCharacterData s.tree fp →
      (∃ fd, s.tree.get? fp = some fd ∧ A.single s fp fd.data c s₁) →
      PreInsertResult s₁ c into none (.error e) →
      PartialFirst A cut s r (some fp) into (.error e)
  | recurse {s r fp into c s₁ s₂ res} : InTree s.tree fp → ¬ IsCharacterData s.tree fp →
      (∃ fd, s.tree.get? fp = some fd ∧ A.single s fp fd.data c s₁) →
      PreInsertResult s₁ c into none (.ok s₂) →
      SubContents A cut s₂ { start := r.start, «end» := ⟨fp, lengthOf s₂.tree fp⟩ } c res →
      PartialFirst A cut s r (some fp) into res

/--
step 19-20（clone the contents の 15-16）：last partially contained child の扱い。

CharacterData なら（その child は original end node である）先頭から end offset までを写す。
そうでなければ child を clone して `into` に append し、((child, 0), original end) の subrange を
extract した subfragment をその clone へ append する（`SubContents`）。
-/
inductive PartialLast (A : Alloc) (cut : Bool) :
    DOMState → RangeState → Option NodeId → NodeId → Except DOMException DOMState → Prop where
  | none {s r into} : PartialLast A cut s r none into (.ok s)
  | data {s r lp into res} : IsCharacterData s.tree lp →
      DataPartResult A cut s r.«end».node 0 r.«end».offset into res →
      PartialLast A cut s r (some lp) into res
  | cloneError {s r lp into c s₁ e} : InTree s.tree lp → ¬ IsCharacterData s.tree lp →
      (∃ ld, s.tree.get? lp = some ld ∧ A.single s lp ld.data c s₁) →
      PreInsertResult s₁ c into none (.error e) →
      PartialLast A cut s r (some lp) into (.error e)
  | recurse {s r lp into c s₁ s₂ res} : InTree s.tree lp → ¬ IsCharacterData s.tree lp →
      (∃ ld, s.tree.get? lp = some ld ∧ A.single s lp ld.data c s₁) →
      PreInsertResult s₁ c into none (.ok s₂) →
      SubContents A cut s₂ { start := ⟨lp, 0⟩, «end» := r.«end» } c res →
      PartialLast A cut s r (some lp) into res

/--
step 17.3-17.5・20.3-20.5（clone the contents の 13.3-13.5・16.3-16.5）：subrange を extract（clone the contents）
した subfragment を、clone に append する。

"extracting subrange" は step 1 で、subrange の start node の node document に属する新しい DocumentFragment を作り、
そこへ step 2 以降を走らせる。subrange は `this` ではない（`self = none`）。
-/
inductive SubContents (A : Alloc) (cut : Bool) :
    DOMState → RangeState → NodeId → Except DOMException DOMState → Prop where
  | error {s r c sd sub s₁ e} : s.tree.get? r.start.node = some sd →
      A.fragment s sd.ownerDocument sub s₁ →
      ContentsInto A cut s₁ r none sub (.error e) →
      SubContents A cut s r c (.error e)
  | append {s r c sd sub s₁ s₂ res} : s.tree.get? r.start.node = some sd →
      A.fragment s sd.ownerDocument sub s₁ →
      ContentsInto A cut s₁ r none sub (.ok s₂) →
      PreInsertResult s₂ sub c none res →
      SubContents A cut s r c res

end

/--
**§5.5 extract と clone the contents の、結果まで含めた関係。** 成功すれば fragment と状態を返す。

step 1 で、start node の node document の DocumentFragment を作り、そこへ step 2-21 を走らせる。
-/
def ContentsResult (A : Alloc) (cut : Bool) (s : DOMState) (r : RangeState) (self : Option Nat) :
    Except DOMException (NodeId × DOMState) → Prop
  | res => ∃ sd frag s₁, s.tree.get? r.start.node = some sd ∧ A.fragment s sd.ownerDocument frag s₁ ∧
      ((∃ e, ContentsInto A cut s₁ r self frag (.error e) ∧ res = .error e) ∨
        (∃ s₂, ContentsInto A cut s₁ r self frag (.ok s₂) ∧ res = .ok (frag, s₂)))

/--
**§5.5 `surroundContents(newParent)` の、結果まで含めた関係。**

1. Text でない node が partially contained なら InvalidStateError。
2. newParent が Document・DocumentType・DocumentFragment なら InvalidNodeTypeError。
3. fragment は this を extract した結果。
4. newParent が children を持てば、null で replace all する。
5. newParent を this に insert する。
6. fragment を newParent に append する。
7. this で newParent を select する。
-/
def SurroundResult (s : DOMState) (i : Nat) (r : RangeState) (np : NodeId) :
    Except DOMException DOMState → Prop
  | res =>
    -- step 1
    ((∃ n, PartiallyContained s.tree r n ∧ InTree s.tree n ∧ ¬ IsText s.tree n) ∧
      res = .error .invalidStateError) ∨
    ((∀ n, PartiallyContained s.tree r n → InTree s.tree n → IsText s.tree n) ∧
      -- step 2
      ((((KindIs s.tree np .document ∨ KindIs s.tree np .documentType ∨
          KindIs s.tree np .documentFragment)) ∧ res = .error .invalidNodeTypeError) ∨
       (¬ (KindIs s.tree np .document ∨ KindIs s.tree np .documentType ∨
          KindIs s.tree np .documentFragment) ∧
        -- step 3
        ((∃ e, ContentsResult .spec true s r (some i) (.error e) ∧ res = .error e) ∨
         (∃ frag s₁, ContentsResult .spec true s r (some i) (.ok (frag, s₁)) ∧
          -- step 4
          ∃ s₂, ((childrenOf s₁.tree np = [] ∧ s₂ = s₁) ∨
              (childrenOf s₁.tree np ≠ [] ∧ ReplaceAllSpec s₁ none np s₂)) ∧
          -- step 5-7
          AndThen (fun res₃ => ∃ r₂, s₂.ranges[i]? = some r₂ ∧ InsertNodeResult s₂ i r₂ np res₃)
            (fun s₃ res₄ => AndThen (PreInsertResult s₃ frag np none)
              (fun s₄ res₅ => ∃ r₄, s₄.ranges[i]? = some r₄ ∧ SelectNodeResult s₄ i np res₅) res₄)
            res)))))

end Dom.Spec
