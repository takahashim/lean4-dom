import Dom.Exec.Types
import Dom.Validity.State
import Dom.CharacterData.Normalize
import Dom.Range.Api

/-!
# 操作列の評価

PLAN §7。scenario を読み込んで初期状態を組み立て、操作を順に適用して各 step の状態を出力する。

各 step の後で `AdmissibleDOMState` の七成分すべてを実行時にも検査する
（PLAN §3.5, §8）。破れていればその step 番号と成分の名前を出力に含める。
`checkAdmissibleDOMState` をそのまま呼ばず成分ごとに見るのは、
どの成分が破れたかを報告するためである
（`checkAdmissibleDOMState_iff` により、全成分が真であることと同値である）。
証明済みの preservation 定理があるので本来は起こらないが、
oracle の組み立て（初期状態の構築や操作の割り当て）の誤りはこれで検出できる。

JSON とは独立している。入出力形式は `Dom/Exec/Json.lean`、
その二つをつないで scenario 一つを走らせる入口は `Dom/Exec/Scenario.lean` にある。
-/

namespace Dom.Exec

/-! ## 初期状態の構築 -/

/--
初期状態の attribute に id を振るときの、その node の先頭の番号。

**node の id の昇順に、node の中では list 順に、1 から順に**振る。
0 から始めないのは、`maxAttrId` が attribute の無い木で 0 を返すからで、
そこから `freshAttrId` が返す最初の id が 1 になる。
差分テストの相手の runner も同じ規則で振るので、attribute の同一性を id で比べられる。
`NodeSpec` は id を持たない（scenario の JSON にも書かない）。
-/
def attrOffset (specs : List NodeSpec) (id : Nat) : Nat :=
  specs.foldl
    (fun m t => if t.id < id && t.kind == .element then m + t.attributes.length else m) 0

/--
scenario の `nodes` から木を組み立てる。

children の順序は配列の並び順で決まる。
組み立てた木が `WellFormed` でなければ拒否する（PLAN §7.1）。
-/
def buildTree (specs : List NodeSpec) : Except String Tree := do
  let ids := specs.map (·.id)
  unless Dom.ListUtil.nodupB ids do
    throw "node の id が重複している"
  let defaultDoc? := (specs.find? (·.kind == .document)).map (·.id)
  let entry (s : NodeSpec) : Except String (NodeId × NodeData) := do
    let owner ←
      match s.ownerDocument with
      | some o => pure o
      | none =>
        if s.kind == .document then pure s.id
        else
          match defaultDoc? with
          | some d => pure d
          | none => throw s!"document node が無いので node {s.id} の ownerDocument を決められない"
    let children := (specs.filter (fun c => c.parent == some s.id)).map fun c => NodeId.mk c.id
    -- `data` は CharacterData 以外では空とする（`NodeData` の doc comment のとおり）。
    return (⟨s.id⟩,
      { kind := s.kind
        parent := s.parent.map NodeId.mk
        children
        ownerDocument := ⟨owner⟩
        data := if s.kind.isCharacterData then s.data else ""
        -- attribute を持てるのは Element だけである（`AttributesValid`）。
        attributes :=
          if s.kind == .element then
            s.attributes.zipIdx.map fun (a, i) => { a with id := ⟨attrOffset specs s.id + i + 1⟩ }
          else []
        -- namespace / prefix / local name を持つのは Element だけである。
        -- 省略時は Dommy の `createElement("div")` に合わせる。
        «namespace» := if s.kind == .element then s.namespace.orElse (fun _ => some htmlNamespace)
                       else none
        «prefix» := if s.kind == .element then s.prefix else none
        localName := if s.kind == .element then s.localName.getD "div" else ""
        -- Document の type。省略時は Dommy の `Window` の document に合わせて HTML document。
        isHTMLDocument := s.kind == .document && s.isHTMLDocument.getD true })
  let entries ← specs.mapM entry
  let t : Tree := { nodes := entries.foldl (fun st p => st.insert p.1 p.2) NodeStore.empty }
  unless t.checkWellFormed do
    throw "初期状態が WellFormed を満たしていない"
  -- element の名前の妥当性。node 生成は model の対象外（roadmap §13.2）なので、
  -- これを崩せる algorithm は無く、`AdmissibleDOMState` の成分にはしていない。
  for spec in specs do
    if spec.kind == .element then
      unless isValidElementLocalName (spec.localName.getD "div") do
        throw s!"node {spec.id} の local name が valid element local name でない"
      if spec.prefix.isSome && (spec.namespace.orElse (fun _ => some htmlNamespace)).isNone then
        throw s!"node {spec.id} は prefix を持つのに namespace が無い"
    else
      unless spec.namespace.isNone && spec.prefix.isNone && spec.localName.isNone do
        throw s!"node {spec.id} は Element でないので namespace / prefix / local name を持てない"
  return t

/-! ## 操作の適用 -/

/--
`nextNode()` / `previousNode()` を i 番目の iterator に適用する。

collection の端で `null` が返る場合、仕様では iterator は変わらない。
index が範囲外の場合も何もしない。

**新しい状態と返る node の両方を返す。** `applyOperation` が前者、`returnValueOf` が
後者を取る。片方が捨てたものをもう片方が計算し直すと、二つが食い違いうるためである
（`toggleAttribute` や `takeRecords` は元から一つの関数が両方を返す形になっている）。
-/
def stepIterator (s : DOMState) (i : Nat)
    (f : Tree → IteratorState → Option (NodeId × IteratorState)) : DOMState × Option NodeId :=
  match s.iterators[i]? with
  | none => (s, none)
  | some it =>
    match f s.tree it with
    | none => (s, none)
    | some (n, it') => ({ s with iterators := s.iterators.set i it' }, some n)

/--
初期状態を組み立てる。range と iterator が valid であることも検査する。

要求するのは **admissible な状態**（`AdmissibleDOMState`）であることである。
range については両端が木の中にあることだけを見る。
順序（`BoundaryLE`）は仕様の invariant ではないので要求しない
（`notes/research-foundation-roadmap.md` §4。反例探索のために loader は
admissible な状態を広く受理してよい）。

ただし differential testing に使う scenario は、Dommy 側が
`setStart` / `setEnd` で range を組み立てる以上、順序の付いたものに限る必要がある。
それは loader の制約ではなく harness の制約なので、生成器の側で守る。
-/
def buildState (sc : Scenario) : Except String DOMState := do
  let t ← buildTree sc.nodes
  let registrations : List Registration := sc.observers.zipIdx.filterMap fun (o, i) =>
    o.target.map fun t =>
      { node := ⟨t⟩, observer := i, subtree := o.subtree, childList := o.childList,
        attributes := o.attributes, attributeOldValue := o.attributeOldValue,
        attributeFilter := o.attributeFilter,
        characterData := o.characterData, characterDataOldValue := o.characterDataOldValue }
  -- `observe` を一度呼んだ状態にあたるので、node list にもその target を入れておく。
  let observers : List ObserverState := sc.observers.map fun o =>
    { nodeList := match o.target with | none => [] | some t => [⟨t⟩] }
  let s : DOMState := { tree := t, ranges := sc.ranges, iterators := sc.iterators,
                        walkers := sc.walkers, listeners := sc.listeners,
                        observers, registrations }
  unless checkStructurallyValid t do
    throw "初期状態が構造上の制約（leaf に children、Document に parent など）を満たしていない"
  unless checkNodeDocumentsValid t do
    throw "初期状態の node document が整合していない"
  unless checkDocumentTreesValid t do
    throw "初期状態の Document の children が仕様の制約を満たしていない"
  unless checkRangeEndpointsValid s do
    throw "初期状態の range の端点が木の中にない"
  unless checkIteratorsValid s do
    throw "初期状態の iterator が valid でない"
  unless checkWalkersValid s do
    throw "初期状態の TreeWalker の root か current が木に無い"
  unless checkObserverRegistrationsValid s do
    throw "初期状態の observer registration が木に無い node か範囲外の observer を指している"
  unless checkAttributesValid t do
    throw "初期状態の attribute list が妥当でない（Element 以外が持つ、鍵が重複、prefix に namespace が無い）"
  return s

/-- node と状態を返す操作の戻り値。失敗した step の戻り値は観測に出ない。 -/
def createdNode (r : Except DOMException (NodeId × DOMState)) : ReturnValue :=
  match r with
  | .error _ => .unit
  | .ok (n, _) => .node (some n)

/-- node と状態を返す操作を、状態だけを返す形にする。 -/
def dropNode (r : Except DOMException (NodeId × DOMState)) : Except DOMException DOMState :=
  match r with
  | .error e => .error e
  | .ok (_, s) => .ok s

theorem dropNode_ok {r : Except DOMException (NodeId × DOMState)} {s' : DOMState}
    (h : dropNode r = .ok s') : ∃ n, r = .ok (n, s') := by
  unfold dropNode at h
  split at h
  · simp at h
  · next n s₀ => exact ⟨n, by rw [← Except.ok.inj h]⟩

/--
操作の戻り値。

どれも **操作前の状態と操作だけ** で決まるので、`applyOperation` の型を変えずに済む
（`deliveredBy` と同じ形）。失敗した step では使わない。

IDL の戻り値は次のとおり。

* `appendChild` / `insertBefore` — 入れた node（pre-insert step 5 が node を返す）
* `replaceChild` / `removeChild` — 取り除いた側の child（replace step 11 / pre-remove step 3）
* `nextNode()` / `previousNode()` — traverse が返した node、終端なら null
* `toggleAttribute` — attribute が結果として付いているか
* `takeRecords()` — 空にする前の record queue
* それ以外 — `undefined`
-/
def returnValueOf (s : DOMState) : Operation → ReturnValue
  | .appendChild _ n => .node (some ⟨n⟩)
  | .insertBefore _ n _ => .node (some ⟨n⟩)
  | .replaceChild _ _ c => .node (some ⟨c⟩)
  | .removeChild _ n => .node (some ⟨n⟩)
  | .iteratorNext i => .node (stepIterator s i nextNode).2
  | .iteratorPrevious i => .node (stepIterator s i previousNode).2
  | .toggleAttribute e qn f =>
    match toggleAttribute s ⟨e⟩ qn f with
    | .error _ => .unit
    | .ok (_, b) => .bool b
  | .takeRecords mo => .records (MutationObserver.takeRecords s mo).2
  -- 作る操作は、作った node を返す。id は `freshId`（操作前の木から決まる）である。
  | .createElement doc ln => createdNode (createElement s ⟨doc⟩ ln)
  | .createElementNS doc ns qn => createdNode (createElementNS s ⟨doc⟩ ns qn)
  | .createTextNode doc d => createdNode (createTextNode s ⟨doc⟩ d)
  | .createComment doc d => createdNode (createComment s ⟨doc⟩ d)
  | .createDocumentFragment doc => createdNode (createDocumentFragment s ⟨doc⟩)
  | .cloneNode n deep => createdNode (cloneNode s ⟨n⟩ deep)
  | .importNode doc n deep => createdNode (importNode s ⟨doc⟩ ⟨n⟩ deep)
  | .adoptNode doc n => createdNode (adoptNode s ⟨doc⟩ ⟨n⟩)
  -- 以下はすべて仕様上 `undefined` を返す。
  -- **catch-all にしない。** そうすると戻り値を持つ操作を足したときに
  -- ここを直し忘れても通ってしまう。網羅性検査に見張らせる。
  | .replaceChildren _ _ => .unit
  | .before _ _ => .unit
  | .after _ _ => .unit
  | .replaceWith _ _ => .unit
  | .remove _ => .unit
  | .moveBefore _ _ _ => .unit
  | .replaceData _ _ _ _ => .unit
  | .normalize _ => .unit
  | .rangeSetStart _ _ _ => .unit
  | .rangeSetEnd _ _ _ => .unit
  | .rangeSetStartSibling _ _ _ => .unit
  | .rangeSetEndSibling _ _ _ => .unit
  | .rangeCollapse _ _ => .unit
  | .rangeSelectNode _ _ => .unit
  | .rangeSelectNodeContents _ _ => .unit
  | .rangeIsPointInRange i n o =>
    match n with
    | none => .unit
    | some n =>
      match rangeIsPointInRange s i ⟨⟨n⟩, o⟩ with
      | .error _ => .unit
      | .ok b => .bool b
  | .rangeIntersectsNode i n =>
    match n with
    | none => .unit
    | some n =>
      match rangeIntersectsNode s i ⟨n⟩ with
      | .error _ => .unit
      | .ok b => .bool b
  | .rangeCompareBoundaryPoints i how j =>
    match rangeCompareBoundaryPoints s i how j with
    | .error _ => .unit
    | .ok v => .int v
  | .rangeComparePoint i n o =>
    match n with
    | none => .unit
    | some n =>
      match rangeComparePoint s i ⟨⟨n⟩, o⟩ with
      | .error _ => .unit
      | .ok v => .int v
  | .rangeDeleteContents _ => .unit
  | .rangeInsertNode _ _ => .unit
  | .walkerMove i m =>
    match walkerStep s i m with
    | .error _ => .unit
    | .ok (r, _) => .node r
  | .rangeToString i =>
    match rangeToString s i with
    | .error _ => .unit
    | .ok str => .str (some str)
  | .compareDocumentPosition n o => .int (compareDocumentPosition s.tree ⟨n⟩ ⟨o⟩)
  | .nodeContains n o => .bool (nodeContains s.tree ⟨n⟩ ⟨o⟩)
  | .getRootNode n => .node (some (getRootNode s.tree ⟨n⟩))
  | .isEqualNode n o => .bool (nodeEquals s.tree ⟨n⟩ ⟨o⟩)
  | .getTextContent n => .str (getTextContent s.tree ⟨n⟩)
  | .getNodeValue n => .str (getNodeValue s.tree ⟨n⟩)
  | .substringData n o c =>
    match substringData s.tree ⟨n⟩ o c with
    | .error _ => .unit
    | .ok str => .str (some str)
  | .getAttribute e q => .str (getAttribute s.tree ⟨e⟩ q)
  | .hasAttribute e q => .bool (hasAttribute s.tree ⟨e⟩ q)
  | .getAttributeNames e => .strs (getAttributeNames s.tree ⟨e⟩)
  | .lookupNamespaceURI n p => .str (lookupNamespaceURI s.tree ⟨n⟩ p)
  | .lookupPrefix n ns => .str (lookupPrefix s.tree ⟨n⟩ ns)
  | .isDefaultNamespace n ns => .bool (isDefaultNamespace s.tree ⟨n⟩ ns)
  | .addEventListener _ _ _ _ _ => .unit
  | .removeEventListener _ _ _ _ => .unit
  | .dispatchEvent t ty b c =>
    match dispatchEvent s ⟨t⟩ ty b c with
    | .error _ => .unit
    | .ok (_, r, _) => .bool r
  | .appendData _ _ => .unit
  | .insertData _ _ _ => .unit
  | .deleteData _ _ _ => .unit
  | .setData _ _ => .unit
  | .setAttribute _ _ _ => .unit
  | .setAttributeNS _ _ _ _ => .unit
  | .removeAttribute _ _ => .unit
  | .removeAttributeNS _ _ _ => .unit
  | .observe _ _ _ => .unit
  | .disconnect _ => .unit
  | .notify => .unit

/--
その操作が microtask checkpoint なら、配送される record を返す。

`notifyMutationObservers` は状態の純関数なので、操作を適用する前の状態から計算できる。
`applyOperation` の型を変えずに観測へ載せるためにこう分けてある。

こちらは catch-all のままにしてある。record が配送されるのは microtask checkpoint
だけで、これは操作の種類を増やしても変わらない仕様上の事実だからである
（`returnValueOf` の側は、操作を足せば戻り値も増えるので列挙してある）。
-/
def deliveredBy (s : DOMState) : Operation → List (Nat × List MutationRecord)
  | .notify => (notifyMutationObservers s).2
  | _ => []

/--
その操作が event の配送なら、呼ばれた listener の列を返す。

`deliveredBy` と同じく、操作前の状態から決まる純関数である。
-/
def invokedBy (s : DOMState) : Operation → List Invocation
  | .dispatchEvent t ty b c =>
    match dispatchEvent s ⟨t⟩ ty b c with
    | .error _ => []
    | .ok (_, _, log) => log
  | _ => []

/--
値を返すだけの操作の前提。

木も live object も変えないので、指した node が木にあることだけを見て状態を返す。
仕様上の受け手が存在しない（IDL の receiver が無い）場合は差分テストの対象外なので、
`NotFoundError` にしておく。
-/
def requireNodes (s : DOMState) (ns : List NodeId) : Except DOMException DOMState :=
  if ns.all fun n => (s.tree.get? n).isSome then .ok s else .error .notFoundError

/--
WebIDL の non-nullable な `Node` 引数を受け取る。

引数の変換は method の step に入る前に走るので、null は
**手順を一つも実行しないうちに** `TypeError` になる。
`Range.setStart(null, 木より大きい offset)` が `IndexSizeError` ではなく
`TypeError` になるのはこのためである。
-/
def withNode {α : Type} (n : Option Nat) (f : NodeId → Except DOMException α) :
    Except DOMException α :=
  match n with
  | none => .error .typeError
  | some n => f ⟨n⟩

/-- 一つの操作を public API に割り当てる。 -/
def applyOperation (s : DOMState) : Operation → Except DOMException DOMState
  | .appendChild p n => appendChild s ⟨p⟩ ⟨n⟩
  | .insertBefore p n c => insertBefore s ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)
  | .replaceChild p n c => replaceChild s ⟨p⟩ ⟨n⟩ ⟨c⟩
  | .removeChild p n => removeChild s ⟨p⟩ ⟨n⟩
  | .replaceChildren p n => replaceChildren s ⟨p⟩ (n.map NodeId.mk)
  | .before tgt n => before s ⟨tgt⟩ ⟨n⟩
  | .after tgt n => after s ⟨tgt⟩ ⟨n⟩
  | .replaceWith tgt n => replaceWith s ⟨tgt⟩ ⟨n⟩
  | .remove tgt => nodeRemove s ⟨tgt⟩
  | .moveBefore p n c => moveBefore s ⟨p⟩ ⟨n⟩ (c.map NodeId.mk)
  | .iteratorNext i => .ok (stepIterator s i nextNode).1
  | .iteratorPrevious i => .ok (stepIterator s i previousNode).1
  | .replaceData n o c d => replaceData s ⟨n⟩ o c d
  | .appendData n d => appendData s ⟨n⟩ d
  | .insertData n o d => insertData s ⟨n⟩ o d
  | .deleteData n o c => deleteData s ⟨n⟩ o c
  | .setData n d => setData s ⟨n⟩ d
  | .normalize tgt => normalize s ⟨tgt⟩
  | .rangeSetStart i n o => withNode n fun n => rangeSetStart s i ⟨n, o⟩
  | .rangeSetEnd i n o => withNode n fun n => rangeSetEnd s i ⟨n, o⟩
  | .rangeSetStartSibling i n a => withNode n fun n => rangeSetStartSibling s i n a
  | .rangeSetEndSibling i n a => withNode n fun n => rangeSetEndSibling s i n a
  | .rangeCollapse i t => rangeCollapse s i t
  | .rangeSelectNode i n => withNode n fun n => rangeSelectNode s i n
  | .rangeSelectNodeContents i n => withNode n fun n => rangeSelectNodeContents s i n
  | .rangeIsPointInRange i n o =>
    withNode n fun n => (rangeIsPointInRange s i ⟨n, o⟩).map (fun _ => s)
  | .rangeIntersectsNode i n => withNode n fun n => (rangeIntersectsNode s i n).map (fun _ => s)
  | .rangeCompareBoundaryPoints i how j => (rangeCompareBoundaryPoints s i how j).map (fun _ => s)
  | .rangeComparePoint i n o =>
    withNode n fun n => (rangeComparePoint s i ⟨n, o⟩).map (fun _ => s)
  | .rangeDeleteContents i => rangeDeleteContents s i
  | .rangeInsertNode i n => withNode n fun n => rangeInsertNode s i n
  | .walkerMove i m => (walkerStep s i m).map (·.2)
  | .rangeToString i => (rangeToString s i).map (fun _ => s)
  | .compareDocumentPosition n o => requireNodes s [⟨n⟩, ⟨o⟩]
  | .nodeContains n o => requireNodes s [⟨n⟩, ⟨o⟩]
  | .getRootNode n => requireNodes s [⟨n⟩]
  | .isEqualNode n o => requireNodes s [⟨n⟩, ⟨o⟩]
  | .getTextContent n => requireNodes s [⟨n⟩]
  | .getNodeValue n => requireNodes s [⟨n⟩]
  | .substringData n o c => (substringData s.tree ⟨n⟩ o c).map (fun _ => s)
  | .getAttribute e _ => requireNodes s [⟨e⟩]
  | .hasAttribute e _ => requireNodes s [⟨e⟩]
  | .getAttributeNames e => requireNodes s [⟨e⟩]
  | .lookupNamespaceURI n _ => requireNodes s [⟨n⟩]
  | .lookupPrefix n _ => requireNodes s [⟨n⟩]
  | .isDefaultNamespace n _ => requireNodes s [⟨n⟩]
  | .addEventListener t ty src cap once => addEventListener s ⟨t⟩ ty src cap once
  | .removeEventListener t ty cb cap => removeEventListener s ⟨t⟩ ty cb cap
  | .dispatchEvent t ty b c => (dispatchEvent s ⟨t⟩ ty b c).map (·.1)
  | .setAttribute e qn v => setAttribute s ⟨e⟩ qn v
  | .setAttributeNS e ns qn v => setAttributeNS s ⟨e⟩ ns qn v
  | .removeAttribute e qn => removeAttribute s ⟨e⟩ qn
  | .removeAttributeNS e ns ln => removeAttributeNS s ⟨e⟩ ns ln
  | .toggleAttribute e qn f => (toggleAttribute s ⟨e⟩ qn f).map Prod.fst
  | .observe mo target opts => MutationObserver.observe s mo ⟨target⟩ opts
  | .disconnect mo => .ok (MutationObserver.disconnect s mo)
  | .takeRecords mo => .ok (MutationObserver.takeRecords s mo).1
  | .createElement doc ln => dropNode (createElement s ⟨doc⟩ ln)
  | .createElementNS doc ns qn => dropNode (createElementNS s ⟨doc⟩ ns qn)
  | .createTextNode doc d => dropNode (createTextNode s ⟨doc⟩ d)
  | .createComment doc d => dropNode (createComment s ⟨doc⟩ d)
  | .createDocumentFragment doc => dropNode (createDocumentFragment s ⟨doc⟩)
  | .cloneNode n deep => dropNode (cloneNode s ⟨n⟩ deep)
  | .importNode doc n deep => dropNode (importNode s ⟨doc⟩ ⟨n⟩ deep)
  | .adoptNode doc n => dropNode (adoptNode s ⟨doc⟩ ⟨n⟩)
  | .notify => .ok (notifyMutationObservers s).1

/--
操作列を順に適用する。例外が起きた step で打ち切る（PLAN §7.2）。

返り値の第二成分は、invariant が破れた step の番号（0 始まり）。

range については **両端が木の中にあること** だけを invariant とする。
順序（start ≤ end）は仕様の invariant ではない。木を変える algorithm の側には
`setStart` / `setEnd` のような正規化が無く、insert step 5（offset の調整）が
step 7 の adopt→remove より前に走るせいで、順序は実際に逆転しうる。
`test/scenarios/range-order-broken-by-insert.json` がその最小例である。
-/
def runOperations : DOMState → List Operation → Nat → List StepResult × Option (Nat × String)
  | _, [], _ => ([], none)
  | s, op :: ops, i =>
    match applyOperation s op with
    | .error e => ([.failed s e], none)
    | .ok s' =>
      let delivered := deliveredBy s op
      let returned := returnValueOf s op
      let invoked := invokedBy s op
      if !s'.tree.checkWellFormed then ([.ok s' delivered returned invoked], some (i, "wellFormed"))
      else if !checkStructurallyValid s'.tree then
        ([.ok s' delivered returned invoked], some (i, "structurallyValid"))
      else if !checkNodeDocumentsValid s'.tree then
        ([.ok s' delivered returned invoked], some (i, "nodeDocumentsValid"))
      else if !checkDocumentTreesValid s'.tree then
        ([.ok s' delivered returned invoked], some (i, "documentTreesValid"))
      else if !checkRangeEndpointsValid s' then
        ([.ok s' delivered returned invoked], some (i, "rangeEndpointsValid"))
      else if !checkIteratorsValid s' then ([.ok s' delivered returned invoked], some (i, "iteratorsValid"))
      else if !checkObserverRegistrationsValid s' then
        ([.ok s' delivered returned invoked], some (i, "observerRegistrationsValid"))
      else if !checkAttributesValid s'.tree then
        ([.ok s' delivered returned invoked], some (i, "attributesValid"))
      else
        let (rest, viol) := runOperations s' ops (i + 1)
        (.ok s' delivered returned invoked :: rest, viol)

/--
scenario を評価して、invariant 違反があればその step 番号と名前を返す。

`Dom/Exec/Invariant.lean` の `runOperations_no_violation` により、
初期状態が admissible ならこれは必ず `none` である。
`some` が返るのは harness 側（初期状態の構築や操作の割り当て）の誤りを意味する。
-/
def checkScenario (sc : Scenario) : Except String (Option (Nat × String)) := do
  let s ← buildState sc
  return (runOperations s sc.operations 0).2

end Dom.Exec
