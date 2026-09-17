# 主定理の一覧

`notes/research-foundation-roadmap.md` §16。

木・Range・NodeIterator・CharacterData に分散した結果を、
状態遷移系全体に関する少数の定理として並べる。
依存する axiom は `Audit.lean` が CI で検査している。
許容しているのは `propext` / `Classical.choice` / `Quot.sound` の三つだけで、
`sorryAx` は無い。

## 1. 妥当な状態は決定可能である

| 定理 | module |
| --- | --- |
| `Dom.checkAdmissibleDOMState_iff` | `Dom/Validity/State.lean` |

```lean
theorem checkAdmissibleDOMState_iff (s : DOMState) :
    checkAdmissibleDOMState s = true ↔ AdmissibleDOMState s
```

`AdmissibleDOMState` は七つの成分（構造・node document・Document の children・
Range の端点・NodeIterator・observer registration・attribute list）の連言である。
boolean の checker と `Prop` が一致するので、
evaluator は実行時に同じ条件を検査できる。

## 2. すべての操作が admissibility を保つ

| 定理 | module |
| --- | --- |
| `Dom.Exec.admissible_applyOperation` | `Dom/Exec/Invariant.lean` |

```lean
theorem admissible_applyOperation {s s' : DOMState} {op : Operation}
    (h : AdmissibleDOMState s) (hop : applyOperation s op = .ok s') : AdmissibleDOMState s'
```

`Operation` は harness が扱う全 public API と NodeIterator の走査である。
個別の操作は `Dom/Validity/Admissible.lean` にある。

| 操作 | 定理 |
| --- | --- |
| `appendChild` | `Dom.admissible_appendChild` |
| `insertBefore` | `Dom.admissible_insertBefore` |
| `replaceChild` | `Dom.admissible_replaceChild` |
| `removeChild` | `Dom.admissible_removeChild` |
| `replaceChildren` | `Dom.admissible_replaceChildren` |
| `before` / `after` / `replaceWith` / `remove` | `Dom.admissible_before` ほか |
| `moveBefore` | `Dom.admissible_moveBefore` |
| `appendData` / `insertData` / `deleteData` / `setData` | `Dom.admissible_appendData` ほか |
| `normalize` | `Dom.admissible_normalize` |
| `Range.setStart` / `setEnd` / `setStartBefore` ほか / `collapse` / `selectNode` / `selectNodeContents` | `Dom.admissible_rangeSetStart` ほか |
| `Range.deleteContents` / `insertNode` | `Dom.admissible_rangeDeleteContents`, `Dom.admissible_rangeInsertNode` |
| `TreeWalker` の走査七つ | `Dom.admissible_walkerStep` |
| 値を返すだけの十二（`compareDocumentPosition` ほか） | `Dom.Exec.admissible_requireNodes` |
| `addEventListener` / `removeEventListener` / `dispatchEvent` | `Dom.admissible_addEventListener` ほか |
| `MutationObserver.observe` / `disconnect` / `takeRecords` | `Dom.admissible_observe` ほか |
| notify mutation observers | `Dom.admissible_notifyMutationObservers` |
| `setAttribute` / `setAttributeNS` / `removeAttribute` / `removeAttributeNS` / `toggleAttribute` | `Dom.admissible_setAttribute` ほか |

§4.2.3 の algorithm 側は `Dom.admissible_remove` / `_insert` / `_replace` /
`_replaceAll` / `_move` / `_replaceData`。

## 3. 有限の操作列が admissibility を保つ

| 定理 | module |
| --- | --- |
| `Dom.Exec.run_preserves_admissibility` | `Dom/Exec/Invariant.lean` |

```lean
theorem run_preserves_admissibility :
    ∀ (ops : List Operation) {s s' : DOMState},
      AdmissibleDOMState s → run s ops = .ok s' → AdmissibleDOMState s'
```

## 4. 到達可能な状態は妥当である

| 定理 | module |
| --- | --- |
| `Dom.Exec.reachable_admissible` | `Dom/Exec/Invariant.lean` |

```lean
theorem reachable_admissible {initial : DOMState → Prop}
    (hinit : ∀ s, initial s → AdmissibleDOMState s) {s : DOMState}
    (hr : ReachableFrom initial s) : AdmissibleDOMState s
```

`AdmissibleDOMState` は局所不変条件の閉包、`ReachableFrom` は構成可能性であり、
別の概念として分けてある。

## 5. `remove` は live object を保つ

| 定理 | module |
| --- | --- |
| `Dom.remove_preserves_live_objects` | `Dom/Validity/Admissible.lean` |

```lean
theorem remove_preserves_live_objects {s s' : DOMState} {n : NodeId} {b : Bool}
    (h : AdmissibleDOMState s) (hr : remove s n b = .ok s') :
    RangeEndpointsValid s' ∧ IteratorsValid s'
```

## 6. `insert` は Range の端点を木の中に保つ

| 定理 | module |
| --- | --- |
| `Dom.insert_preserves_endpoints` | `Dom/Properties/Range.lean` |

DocumentFragment を展開する場合も含む。
**順序（start ≤ end）は保たない。**それが 9 の結果である。

## 7. `move` は remove と insertAt の合成に一致する

| 定理 | module |
| --- | --- |
| `Dom.move_matches_remove_insert_observation` | `Dom/Validity/Admissible.lean` |

```lean
theorem move_matches_remove_insert_observation {s s' : DOMState} {node newParent : NodeId}
    {child : Option NodeId} (hm : move s node newParent child = .ok s') :
    ∃ s₁, remove s node = .ok s₁ ∧
      insertAt s₁.tree newParent node child = .ok s'.tree ∧
      s'.ranges = (liveRangeInsertAdjust s₁ newParent child 1).ranges ∧
      s'.iterators = s₁.iterators
```

`move` は node document を付け替えないので、`insert`（adopt を含む）ではなく
primitive の `insertAt` との一致になる。

## 8. `replace data` は live object を保つ

| 定理 | module |
| --- | --- |
| `Dom.replaceData_preserves_live_object_validity` | `Dom/Validity/Admissible.lean` |

## 9. `insert` は Range の順序を保たない（negative result）

| 定理 | module |
| --- | --- |
| `Dom.exists_insert_breaking_boundaryLE` | `Dom/Properties/Counterexample.lean` |
| `Dom.boundaryLE_not_preserved_by_insert` | 同上 |

```lean
theorem exists_insert_breaking_boundaryLE :
    ∃ (s s' : DOMState) (parent node child : NodeId) (r r' : RangeState),
      AdmissibleDOMState s ∧ s.ranges = [r] ∧
      BoundaryLE s.tree r.start r.«end» ∧
      insertBefore s parent node (some child) = .ok s' ∧
      AdmissibleDOMState s' ∧ s'.ranges = [r'] ∧
      ValidBoundaryPoint s'.tree r'.start ∧ ValidBoundaryPoint s'.tree r'.«end» ∧
      ¬ BoundaryLE s'.tree r'.start r'.«end»
```

反例の状態は具体的に構成してあり、証明は `decide` だけを使う。
`native_decide` は使っていないので kernel で検査される。
同じ例の JSON 版が `test/scenarios/range-order-broken-by-insert.json` である。

## 10. `TreeWalker` は走査で木から出ない（ただし remove には追随しない）

| 定理 | module |
| --- | --- |
| `Dom.walkersValid_walkerStep` | `Dom/Properties/Walker.lean` |

```lean
theorem walkersValid_walkerStep {s s' : DOMState} {i : Nat} {m : WalkerMethod}
    {r : Option NodeId} (hwf : WellFormed s.tree) (h : WalkersValid s)
    (hs : walkerStep s i m = .ok (r, s')) : WalkersValid s'
```

`WalkersValid` は「root と current が木にある」である。
`NodeIterator` の `ValidIterator` のように
**「current は root の inclusive descendant」までは要求しない**。
§6.2 には "removing steps" が無いので remove がその関係を壊すからで、
それは仕様どおりの挙動である（`test/scenarios/walker-not-adjusted-by-remove.json`）。
そのため `walkers` は `AdmissibleDOMState` の成分ではない
（`Dom/Validity/Walkers.lean` にその理由を書いてある）。

## 11. `compareDocumentPosition` は実装依存の枝でも一貫している

| 定理 | module |
| --- | --- |
| `Dom.compareDocumentPosition_disconnected_consistent` | `Dom/Query/NodeQuery.lean` |

```lean
theorem compareDocumentPosition_disconnected_consistent {t : Tree} {a b : NodeId}
    (hne : a ≠ b) (hr : root t a ≠ root t b) :
    (compareDocumentPosition t a b = 37 ∧ compareDocumentPosition t b a = 35) ∨
    (compareDocumentPosition t a b = 35 ∧ compareDocumentPosition t b a = 37)
```

仕様 §4.4 step 6 は、同じ木にない二つの node について
PRECEDING と FOLLOWING のどちらを返すかを実装に任せたうえで、
**一貫していること**を求めている。model は node id の順で決めるので、
逆から呼べば逆の答えになる。37 は `DISCONNECTED+IMPLEMENTATION_SPECIFIC+FOLLOWING`、
35 は `+PRECEDING` である。

## 12. event の配送は listener list しか変えない

| 定理 | module |
| --- | --- |
| `Dom.listenersOnly_dispatchEvent` | `Dom/Validity/Events.lean` |
| `Dom.admissible_dispatchEvent` | 同上 |

```lean
theorem listenersOnly_dispatchEvent {s s' : DOMState} {target : NodeId} {ty : String}
    {b c r : Bool} {log : List Invocation}
    (hd : dispatchEvent s target ty b c = .ok (s', r, log)) : ListenersOnly s s'
```

`ListenersOnly s s'` は `{ s with listeners := s'.listeners } = s'`、
つまり「listener list 以外は同じ」である。配送は木も range も iterator も触らないので、
admissibility の保存はここから出る。listener の callback は model の外だが、
scenario が宣言した副作用（`ListenerAction`）は listener list しか変えないので、
この定理はその範囲での主張である。

## 13. 実行関数は関係意味論を満たす（`remove`）

| 定理 | module |
| --- | --- |
| `Dom.Spec.remove_sound` | `Dom/Spec/RemoveSound.lean` |
| `Dom.Spec.adopt_sound` | `Dom/Spec/AdoptSound.lean` |
| `Dom.Spec.insert_sound` | `Dom/Spec/InsertSound.lean` |
| `Dom.Spec.replaceData_sound` | `Dom/Spec/ReplaceDataSound.lean` |

```lean
theorem remove_sound {s s' : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h : remove s n b = .ok s') : RemoveSpec s n b s'
```

`RemoveSpec`（`Dom/Spec/Remove.lean`）は仕様本文から独立に書き写した関係で、
実行側の algorithm を一つも呼ばない。仕様の副作用ごとに六つの component に分かれる。

| component | 仕様の step | soundness |
| --- | --- | --- |
| `RemovePre` | 1-2 | `remove_ok` |
| `RangeAdjusted` | 3 | `Dom.Spec.remove_sound_range` |
| `IteratorAdjusted` | 4 | `Dom.Spec.remove_sound_iterator` |
| `TreeRemoved` | 7 | `Dom.Spec.remove_sound_tree` |
| `TransientAdded` | 20 | `Dom.Spec.remove_sound_transient` |
| `RecordQueued` | 21 | `Dom.Spec.remove_sound_record` |

`adopt`（§4.5）と `insert`（§4.2.3）も同じ形で入れた。`insert` は step 4 で `remove` を、
step 7.1 で `adopt` を呼ぶので、関係もそれぞれ `RemoveSpec` / `AdoptSpec` を composition する
（仕様本文がそう書いているとおりの構成であり、実行関数の再利用ではない）。

`remove` の逆向きのうち **一意性** は示してある。

| 定理 | module |
| --- | --- |
| `Dom.Spec.removeSpec_deterministic` | `Dom/Spec/RemoveDeterministic.lean` |

```lean
theorem removeSpec_deterministic {s s₁ s₂ : DOMState} {n : NodeId} {b : Bool}
    (hwf : WellFormed s.tree) (h₁ : RemoveSpec s n b s₁) (h₂ : RemoveSpec s n b s₂) :
    (∀ m, s₁.tree.get? m = s₂.tree.get? m) ∧ s₁.ranges = s₂.ranges ∧ ...
```

木の表現そのものは決まらない（store が association list なので、同じ `get?` を持つ表現が
複数ある）。決まるのは **観測**である。registered observer list は順序を決めていないので
所属の一致になる。soundness と合わせると「`remove` の結果は、関係が許す唯一の観測である」
と言える。completeness（関係を満たす状態が必ず作れること）はまだ無い。

### 観測が等しい状態どうしの congruence

`insert` のように関係を繋いだものの一意性には、上の形では足りない。
途中の状態は観測としてしか一致しないので、
「入力の観測が等しければ出力の観測も等しい」が要る。

| 定理 | module |
| --- | --- |
| `Dom.Spec.ObsEq` | `Dom/Spec/ObsEq.lean` |
| `Dom.Spec.removeSpec_congr` | `Dom/Spec/RemoveCongr.lean` |
| `Dom.Spec.adoptSpec_congr` | `Dom/Spec/AdoptCongr.lean` |
| `Dom.Spec.insertSpec_congr` | `Dom/Spec/InsertCongr.lean` |
| `Dom.Spec.insertSpec_deterministic` | `Dom/Spec/InsertCongr.lean` |

```lean
theorem insertSpec_deterministic {s o₁ o₂ : DOMState} {suppress : Bool}
    (hwf : WellFormed s.tree)
    (hacyc : ∀ ns, NodesToInsert s.tree node ns →
      ∀ m ∈ ns, ¬ InclusiveAncestor s.tree m parent)
    (h₁ : InsertSpec s node parent child suppress o₁)
    (h₂ : InsertSpec s node parent child suppress o₂) : ObsEq o₁ o₂
```

`hacyc`（入れる node が `parent` の inclusive ancestor でない）は §4.2.1 の
pre-insertion validity が保証するもので、`insert` 本体は前提として受け取る。
これが無いと木が循環し、`TreeInserted` の結果が well-formed でなくなる。

`ObsEq` は `DOMState` の十成分すべてを見る。木・range・iterator・registration・
record queue・pending・microtask に加えて、`walkers` / `listeners` / `detachedAttrs`
である。後の三つは §4.2.3 の algorithm が触れないが `Observation` には出るので、
抜くと determinism も completeness も「将来の操作から区別できない」ことを
意味しなくなる（`Dom/Basic/State.lean` の `Untouched`）。
関係の側は frame 条件としてこれを持つ。

## 14. oracle は自分の invariant を破らない

| 定理 | module |
| --- | --- |
| `Dom.Exec.runOperations_no_violation` | `Dom/Exec/Invariant.lean` |

```lean
theorem runOperations_no_violation :
    ∀ (ops : List Operation) {s : DOMState} (i : Nat),
      AdmissibleDOMState s → (runOperations s ops i).2 = none
```

evaluator は各 step の後で `AdmissibleDOMState` の七成分を実行時に検査する。
admissible な初期状態から始めれば、この検査は決して発火しない。
`invariantViolation` が出たら harness 側の誤りである。

## 15. `cloneNode` は妥当な木の上では失敗しない

| 定理 | module |
| --- | --- |
| `Dom.cloneNode_isOk` / `Dom.cloneNodeIn_isOk` / `Dom.importNode_isOk` | `Dom/Properties/CloneOk.lean` |
| `Dom.adopt_isOk` / `Dom.adoptNode_isOk` | 同上 |

```lean
theorem cloneNode_isOk {s : DOMState} {n : NodeId} {deep : Bool} {d : NodeData}
    (hv : AdmissibleDOMState s) (hd : s.tree.get? n = some d) :
    ∃ c s', cloneNode s n deep = .ok (c, s')
```

model の `cloneNode` は §4.2.3 の `append` を呼ぶので、原理的には pre-insert validity の
検査に落ちて `HierarchyRequestError` を返しうる。落ちうる場所は三つ（fuel の枯渇、
pre-insert validity、`append` の中の `adopt` と `insertAt`）で、妥当な木ではどれも起きない。

`adoptNode` のほうは落ちうる場所が四つある。受け手が Document であること・node が
木にあること・node が Document でないことは仮定で、残るのは step 2 の `remove` だけである。
`adopt` は parent がある node にしか `remove` を呼ばないので、`remove_succeeds_iff`
（`Dom/Properties/Contract.lean`）がそのまま効く。step 1 の `ownerDocumentOf` は
`get?` の像なので、node が木にあれば必ず `some` になる。

要は `AppendableInto` の `docKinds` である。**append 先に既に入れた children の kind 列と、
これから入れる残りの kind 列を繋いだもの**が Document の制約を満たす、という形にしてある。
一つ append すると前半が一つ伸びて後半が一つ縮むだけなので繋いだ列は変わらず、
条件が自分で自分を保つ。最初にそれが成り立つのは、繋いだ列が原本の children の
kind 列そのものだからである。

## 16. selector の API が満たすこと

| 定理 | module |
| --- | --- |
| `Dom.querySelector_eq_head` ほか | `Dom/Properties/Selector.lean` |

```lean
theorem querySelector_eq_head (t : Tree) (selectors : String) (node : NodeId) :
    querySelector t selectors node = (querySelectorAll t selectors node).map List.head?

theorem matchTree_sublist (t : Tree) (sel : SelectorList) (node : NodeId) :
    (matchTree t sel node).Sublist (preorder t node)

theorem mem_matchTree_iff (hwf : WellFormed t) {node : NodeId} {d : NodeData}
    (hn : t.get? node = some d) (sel : SelectorList) (e : NodeId) :
    e ∈ matchTree t sel node ↔
      Descendant t e node ∧ isElementNode t e = true ∧
        matchSelList { tree := t, scope := some node } sel e = true
```

`querySelectorAll()` の結果は候補列（`preorder`）の部分列なので **tree order に並ぶ**。
`preorder_nodup` と合わせて **重複が無い**（`matchTree_nodup`）。
入るのはちょうど「scoping root の descendant である element で selector に当たるもの」である。

`closest()` については、返るのが inclusive ancestor である element で selector に当たること
（`closest_spec`）、**それより近いものは当たらないこと**（`closest_first`）、
当たるものが無いときだけ null を返すこと（`closest_eq_none_iff`）を示してある。

## 17. scoping root が見えるのは `:scope` からだけ

| 定理 | module |
| --- | --- |
| `Dom.scope_irrelevant` / `Dom.mem_matchTree_iff_matches` | `Dom/Properties/Selector.lean` |

```lean
theorem matchSelList_scope_irrelevant {t : Tree} {s₁ s₂ a : Option NodeId}
    {l : List Complex} {n : NodeId} (hf : scopeFreeL l = true) :
    matchSelList ⟨t, s₁, a⟩ l n = matchSelList ⟨t, s₂, a⟩ l n
```

`matchSimple` が `ctx.scope` を読むのは `Simple.scope` の枝だけなので、
そこを塞げば scoping root は観測できない。

これが要るのは `matches()` と `querySelectorAll()` を繋ぐためである。前者の scoping root は
element 自身、後者は受け手なので、`:scope` を含む selector では両者が食い違う。
含まなければ一致する（`mem_matchTree_iff_matches`）。

照合は四つの相互再帰なので functional induction が作れない
（`:nth-child(... of S)` の `filter` に再帰呼び出しが入るため）。代わりに
selector の大きさについての強い帰納法で、四つの命題を同時に示している。

## 18. selector の照合は仕様の関係を満たす（部分）

| 定理 | module |
| --- | --- |
| `Dom.Spec.anbMatches_iff` / `Dom.Spec.mem_combCandidates_*` | `Dom/Spec/Selector.lean` |

```lean
def AnBIndex (ab : AnB) (i : Nat) : Prop := ∃ n : Nat, ab.a * (n : Int) + ab.b = (i : Int)

theorem anbMatches_iff (ab : AnB) (i : Nat) : anbMatches ab i = true ↔ AnBIndex ab i

def ElementSiblingImmediatelyBefore (t : Tree) (e f : NodeId) : Prop :=
  ∃ p pre post, elementChildrenOf t p = pre ++ e :: f :: post

theorem mem_combCandidates_nextSibling (hwf : WellFormed t) {n p : NodeId}
    (hp : parentOf t n = some p) (hn : isElementNode t n = true) (e : NodeId) :
    e ∈ combCandidates t .nextSibling n ↔ ElementSiblingImmediatelyBefore t e n
```

16・17 は実行関数についての定理なので、仕様の翻訳を誤っていたら誤ったまま証明できる。
`Dom/Spec/` と同じく、仕様本文から独立に書き写した関係を置いて照合がそれを満たすことを
示す。照合全体は重いので、**翻訳を誤りやすく差分テストが薄いところ**に絞ってある。

`<a-n-plus-b>` は `n` が **非負**に限るのが効く。`A` が負なら表す index は有限個になり、
`:nth-child(-n+3)` が「先頭から三つ」を指す。生成器はこの形を作っていなかった。

combinator のほうは、`~` が「前のどれか」・`+` が「すぐ前」であることを書き写した。
実行側は `takeWhile` と `getLast?` で書いており、向きと一つずれが入りうるのはそこである。
実際 `getLast?` を `head?` に変えると、この定理は通らなくなる一方、
固定 scenario 110 本と生成 scenario 200 本はどちらも気付かない
（`docs/status.md` の「定理に歯があるか確かめた」）。

### attribute selector の値の照合（§6.3）

```lean
def AttrOpHolds : AttrOp -> List Char -> List Char -> Prop
  | .exact, v, w => v = w
  | .includes, _, w => w ≠ [] ∧ NoWhitespace w
  | .dashMatch, v, w => v = w ∨ ∃ rest, v = w ++ Char.ofNat 0x2D :: rest
  | .prefixMatch, v, w => w ≠ [] ∧ ∃ rest, v = w ++ rest
  | .suffixMatch, v, w => w ≠ [] ∧ ∃ pre, v = pre ++ w
  | .substring, v, w => w ≠ [] ∧ ∃ pre post, v = pre ++ w ++ post

theorem attrTestHolds_iff (test : AttrTest) (value : String) (h : test.op ≠ .includes) :
    attrTestHolds test value = true ↔
      AttrOpHolds test.op (caseFold test.case value.toList)
        (caseFold test.case test.value.toList)
```

`~=` の「空白で区切った語のどれか」だけは、語の切り出しの帰納法が重いので定理にしていない。
仕様が明記する二つの但し書き（値が空、値が空白を含む）は
`includes_empty_never` / `includes_whitespace_never` にしてあり、
語境界そのものは固定 scenario が見ている。

### `:nth-*()` が数える列（§14.3-14.7）

```lean
def InclusiveElementSibling (t : Tree) (m n : NodeId) : Prop :=
  isElementNode t m = true ∧ (m = n ∨ ∃ p, parentOf t n = some p ∧ parentOf t m = some p)

theorem mem_elementSiblings_iff (hwf : WellFormed t) (hn : isElementNode t n = true) (m) :
    m ∈ elementSiblings t n ↔ InclusiveElementSibling t m n

theorem matchSimple_nth_iff (hd : ctx.tree.get? n = some d) (hel : d.kind = NodeKind.element)
    (hnd : (nthPoolOf ctx d kind ofSel n).Nodup) :
    matchSimple ctx (.nth kind ab ofSel) n = true ↔
      ∃ pre post, nthPoolOf ctx d kind ofSel n = pre ++ n :: post ∧
        AnBIndex ab (if countsFromEnd kind then post.length + 1 else pre.length + 1)
```

数える列が inclusive sibling であること（parent を持たない element なら自分だけ）、
index が 1 始まりであること、`:nth-last-*()` が末尾から数えることを押さえる。

### type selector の大文字小文字・`:root`・`:empty`（§6.1・§14.1・§14.2）

```lean
def TypeSelectorMatches (t : Tree) (d : NodeData) (name : String) : Prop :=
  (HtmlElementInHtmlDocument t d ∧ asciiLowercase name = d.localName) ∨
    (¬ HtmlElementInHtmlDocument t d ∧ name = d.localName)

theorem typeHolds_iff (t) (d) (name) : typeHolds t d name = true ↔ TypeSelectorMatches t d name
```

名前の照合は既定で "identical to"。HTML が HTML namespace の element について定める規則は
**selector の側を ASCII lowercase して local name と比べる**もので、対称な
case-insensitive **ではない**。仕様自身が「ほぼ同じ」と註記しており、script で作った
大文字の local name は selector で当たらない。ここを取り違えても、
生成器の名前が全部小文字だったので差分テストは気付かなかった。

`:root` は「parent が Document である element」、`:empty` は
「どの子も emptiness を壊さない」を関係として書いてある。

### `:has()` の候補と attribute の namespace（§14.10・§6.2）

```lean
theorem matchSimple_has_iff (hwf : WellFormed ctx.tree) (hd : ctx.tree.get? n = some d)
    (hel : d.kind = NodeKind.element) (l : List Complex) :
    matchSimple ctx (.has l) n = true ↔
      ∃ c, InclusiveDescendant ctx.tree c (root ctx.tree n) ∧
        matchSelList { ctx with anchor := some n } l c = true

def SelectorAttrMatches (t) (d) (anyNs : Bool) (name) (a : Attr) : Prop :=
  AttrNameMatches t d name a ∧ (anyNs = true ∨ a.namespace = none)
```

`:has()` の引数は relative selector なので、`+` や `~` も書ける。
だから候補は anchor の部分木に限らず、**同じ木のどの element でもよい**。

`[att]` は namespace を持たない attribute だけに当たる（`[*|att]` は問わない）。
class と id も同じである。

## 19. pre-remove steps の二つの調整は可換である

| 定理 | module |
| --- | --- |
| `Dom.liveRangePreRemoveBP_comm` | `Dom/Properties/Range.lean` |

```lean
theorem liveRangePreRemoveBP_comm (t : Tree) (node parent : NodeId) (index : Nat)
    (bp : BoundaryPoint) :
    rangeShiftAfterRemove parent index (rangeMoveOutOfSubtree t node parent index bp)
      = rangeMoveOutOfSubtree t node parent index (rangeShiftAfterRemove parent index bp)
```

§5.5 は step 3-4（部分木の外へ移す）と step 5-6（offset をずらす）の順序を定めるが、
二つは**無条件に可換**である。step 5-6 は `node` を変えないので step 3-4 の条件に
影響せず、step 3-4 が移した先の offset はちょうど `index` なので step 5-6 の条件に
当てはまらない。

この定理は、差分テストで順序を入れ替えても不一致が出ないことの説明になっている。

## 契約

例外の検査順序と成功条件は `Dom/Properties/Contract.lean` にある。
`docs/traceability.md` の表に algorithm ごとの現状を並べてある。

| 定理 | 内容 |
| --- | --- |
| `Dom.remove_succeeds_iff` | `remove` が成功する必要十分条件 |
| `Dom.remove_error_iff` | `remove` が失敗する必要十分条件 |
| `Dom.replace_cycle_precedes_notFound` | cycle は reference child の検査より先に返る |
| `Dom.ensurePreInsertionValidity_step1` 〜 `_step3` | pre-insert 検査の step 1-3 の優先順位 |
| `Dom.moveValidity_step1` 〜 `_step4` | move 検査の step 1-4 の優先順位 |

## 実行関数と証明の置き場所

module の層は次のとおりで、逆向きの import は一つだけである
（`Dom/Properties/Counterexample.lean` が `Dom/Exec/Invariant.lean` を見る。
harness そのものについての反例なので意図したもの）。

| 層 | 内容 |
| --- | --- |
| 0 | `Infra/`、`Dom/Util/` — 仕様に依らない道具 |
| 1 | `Dom/Basic/`、`Selectors/` — 木と観測の語彙、selector の構文 |
| 2 | `Dom/Mutation/` ほか — 仕様の algorithm の翻訳 |
| 3 | `Dom/Validity/`、`Dom/Properties/`、`Dom/Spec/` — 不変条件・契約・関係意味論 |
| 4 | `Dom/Exec/` — 差分テストの harness |

**層 2 の module は仕様の節に沿って切ってある。** 凝集度の基準は「同じ algorithm か」
であって「同じ型を触るか」ではない。`docs/traceability.md` の表が algorithm から
evaluator を引けるのはそのためで、ここを普通の意味で整理し直すと表が引けなくなる。

契約（実行関数についての定理）は `Dom/Properties/`、関係意味論（仕様本文から
独立に書き写したもの）は `Dom/Spec/` に置く。selector の契約が
`Dom/Selector/Spec.lean` に居て `Dom/Spec/Selector.lean` と紛らわしかったので、
`Dom/Properties/Selector.lean` に移した。

## 定理そのものを検査する

定理が通ることと、定理が**意味のあることを言っている**ことは別である。
次の四つで検査している。

### 1. 空虚でないか

`AdmissibleDOMState` は七つの条件の連言なので、それを満たす状態が本当にあるかは自明でない。
`Dom/Properties/Witness.lean` が具体的な木を一つ組み立て、決定手続き
`checkAdmissibleDOMState` が `true` を返すことを `rfl` で確かめ、
`checkAdmissibleDOMState_iff` を通して `AdmissibleDOMState` を得ている。
そのうえで `cloneNode_isOk` / `adoptNode_isOk` / `remove_succeeds_iff` を
その状態に当てている。

経験的な証人は固定 scenario 側にもある。`lake exe dom-model --check test/scenarios` が
154 本の毎 step で admissibility を実行時に検査している。

### 2. 仮定が飾りでないか

同じ file で、仮定を外すと結論が成り立たなくなることを見る。
`adoptNode` に Document を渡すと `NotSupportedError`、parent の無い node を
`remove` すると `NotFoundError`、`ParentNode` でない受け手に `querySelector()` を
呼ぶと `TypeError` になる。

### 3. 関係が実装の言い換えになっていないか

`ruby test/spec_dependence.rb` が、`Dom/Spec/` の関係の定義が実行側の名前を
触っているかを機械的に出す。§4.2.3 の関係（`Insert` / `Remove` / `Replace` /
`Adopt` / `Move` / `Record`）は `Dom.Basic.*` しか import していないので、
実行関数を呼びようがない。import graph がそのまま保証になっている。

Selectors の関係だけは照合の実装と同じ module を見るので、この script が要る。
いま触れているのは `elementChildrenOf` / `isElementNode`（薄い補助）と、
`nthPoolOf` / `NthPoolMember` の `matchSelList` である。後者は仕様自身が
「S に当たる inclusive sibling」と照合を使って定義しているので避けられない。
代わりに `mem_nthPoolOf_iff` を置いて、**数える列の中身は仕様の語彙
（inclusive element sibling と same type）で決まる**ようにしてある。

URL の関係（`Url/Spec/`）も同じ script が見る。実行側は `Url/Parser.lean` の
state machine、語彙は §1.3 の percent-encode と §4.1 の record、§3.2 の host、
Infra である。いま触れているものは無い。`encChar` は §1.3 の操作なので
`Url/Parser.lean` から `Url/Percent.lean` へ移した。

### 4'. 証明が定義の「形」に結合していないか

3 までは「定理が何を言っているか」の検査だが、もう一つ別の結合がある。
**証明が、定義の意味ではなく書き方に依っている**ことがある。

例。`liveRangePreRemoveBP` は二つの step の合成である。

```lean
def liveRangePreRemoveBP (t : Tree) (node parent : NodeId) (index : Nat) (bp : BoundaryPoint) :=
  rangeShiftAfterRemove parent index (rangeMoveOutOfSubtree t node parent index bp)
```

合成の順序を入れ替えると build が落ちる。だが `liveRangePreRemoveBP_comm` が言うとおり、
**二つは無条件に可換**なので、関数の値はどの入力でも変わらない。落ちているのは
`Dom/Properties/Path.lean` の `bpKey_detach` で、証明が

```lean
  unfold liveRangePreRemoveBP rangeMoveOutOfSubtree
  by_cases hin : InclusiveAncestor t n bp.node
  · rw [if_pos …]
```

と書いてあるからである。展開したときに外側に来るのがどちらの `if` かを当てにしており、
入れ替えると `hin` の型が `InclusiveAncestor t n bp.node` ではなく
`InclusiveAncestor t n (rangeShiftAfterRemove p i bp).node` になって合わなくなる。
**値は同じで、綴りだけが違う。**

これが分かっていないと、壊して測る方法で「定理が守っている」と読み違える。
実際、七件のうち二件がこれだった（`docs/status.md`）。

対処は二段ある。

1. **形が効かない理由を定理にする。** `rangeShiftAfterRemove_node`
   （offset をずらしても `node` は変わらない）と `liveRangePreRemoveBP_comm`。
   前者は `simp` 補題なので、以後の証明はこれを使えば順序に依らずに書ける。
2. **既存の証明を書き直す。** こちらはやっていない。`simp` 補題を足しただけでは
   既存の証明は直らない（`rw [if_pos …]` の側が使っていないため）。定義が変わる
   見込みが無いので、費用に見合わないと判断した。**いま得ているのは
   「結合があると知っていること」で、測定を読み違えないためのものである。**

### 4. 実装を壊したときに落ちるか

`docs/status.md` の測定。六つの subsystem で、仕様の step を一つずつ壊して
定理・固定 scenario・生成 scenario のどれが捕まえるかを見た。
**「定理が落ちた」は「観測できる誤りを入れた」と同じではない**ことも分かっている
（七件中二件が偽陽性で、どちらも「仕様は順序を定めているが実装はどちらでもよい」
という定理になった）。

## axiom 依存

`Audit.lean` を CI で elaborate する。

```sh
lake env lean Audit.lean
```

許容外の axiom（`sorryAx` を含む）に依存する定理があると失敗する。
