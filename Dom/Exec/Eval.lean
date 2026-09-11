import Dom.Exec.Types
import Dom.Validity.State

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
        attributes := if s.kind == .element then s.attributes else []
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
  unless checkObserverRegistrationsValid s do
    throw "初期状態の observer registration が木に無い node か範囲外の observer を指している"
  unless checkAttributesValid t do
    throw "初期状態の attribute list が妥当でない（Element 以外が持つ、鍵が重複、prefix に namespace が無い）"
  return s

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
  | .iteratorNext i =>
    .node (match s.iterators[i]? with
           | none => none
           | some it => (nextNode s.tree it).map Prod.fst)
  | .iteratorPrevious i =>
    .node (match s.iterators[i]? with
           | none => none
           | some it => (previousNode s.tree it).map Prod.fst)
  | .toggleAttribute e qn f =>
    match toggleAttribute s ⟨e⟩ qn f with
    | .error _ => .unit
    | .ok (_, b) => .bool b
  | .takeRecords mo => .records (MutationObserver.takeRecords s mo).2
  | _ => .unit

/--
その操作が microtask checkpoint なら、配送される record を返す。

`notifyMutationObservers` は状態の純関数なので、操作を適用する前の状態から計算できる。
`applyOperation` の型を変えずに観測へ載せるためにこう分けてある。
-/
def deliveredBy (s : DOMState) : Operation → List (Nat × List MutationRecord)
  | .notify => (notifyMutationObservers s).2
  | _ => []

/--
`nextNode()` / `previousNode()` を i 番目の iterator に適用する。

collection の端で `null` が返る場合、仕様では iterator は変わらない。
index が範囲外の場合も何もしない。
-/
def stepIterator (s : DOMState) (i : Nat)
    (f : Tree → IteratorState → Option (NodeId × IteratorState)) : DOMState :=
  match s.iterators[i]? with
  | none => s
  | some it =>
    match f s.tree it with
    | none => s
    | some (_, it') => { s with iterators := s.iterators.set i it' }

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
  | .iteratorNext i => .ok (stepIterator s i nextNode)
  | .iteratorPrevious i => .ok (stepIterator s i previousNode)
  | .replaceData n o c d => replaceData s ⟨n⟩ o c d
  | .appendData n d => appendData s ⟨n⟩ d
  | .insertData n o d => insertData s ⟨n⟩ o d
  | .deleteData n o c => deleteData s ⟨n⟩ o c
  | .setData n d => setData s ⟨n⟩ d
  | .setAttribute e qn v => setAttribute s ⟨e⟩ qn v
  | .setAttributeNS e ns qn v => setAttributeNS s ⟨e⟩ ns qn v
  | .removeAttribute e qn => removeAttribute s ⟨e⟩ qn
  | .removeAttributeNS e ns ln => removeAttributeNS s ⟨e⟩ ns ln
  | .toggleAttribute e qn f => (toggleAttribute s ⟨e⟩ qn f).map Prod.fst
  | .observe mo target opts => MutationObserver.observe s mo ⟨target⟩ opts
  | .disconnect mo => .ok (MutationObserver.disconnect s mo)
  | .takeRecords mo => .ok (MutationObserver.takeRecords s mo).1
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
      if !s'.tree.checkWellFormed then ([.ok s' delivered returned], some (i, "wellFormed"))
      else if !checkStructurallyValid s'.tree then
        ([.ok s' delivered returned], some (i, "structurallyValid"))
      else if !checkNodeDocumentsValid s'.tree then
        ([.ok s' delivered returned], some (i, "nodeDocumentsValid"))
      else if !checkDocumentTreesValid s'.tree then
        ([.ok s' delivered returned], some (i, "documentTreesValid"))
      else if !checkRangeEndpointsValid s' then
        ([.ok s' delivered returned], some (i, "rangeEndpointsValid"))
      else if !checkIteratorsValid s' then ([.ok s' delivered returned], some (i, "iteratorsValid"))
      else if !checkObserverRegistrationsValid s' then
        ([.ok s' delivered returned], some (i, "observerRegistrationsValid"))
      else if !checkAttributesValid s'.tree then
        ([.ok s' delivered returned], some (i, "attributesValid"))
      else
        let (rest, viol) := runOperations s' ops (i + 1)
        (.ok s' delivered returned :: rest, viol)

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
