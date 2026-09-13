import Dom.Basic.State
import Dom.Observer.Record
import Dom.Attribute.Algorithms

/-!
# 観測モデル

`notes/research-foundation-roadmap.md` §9。

Dommy との差分テストで **何を比べるか** を型で固定する。
Lean の `DOMState` と Ruby 側の内部表現が同じである必要は無い。
同じ `Observation` に落ちることを「一致した」の意味とする。

## 比較する

* node の kind
* parent と順序付きの children（tree order はこの二つから決まる）
* node document
* CharacterData の data
* Element の attribute list（順序も含む）
* Element の namespace / namespace prefix / local name / `tagName`
* live Range の両端
* NodeIterator の root / reference / pointer-before-reference flag
* MutationObserver に積まれた record の列
* microtask checkpoint で各 observer の callback に配送された record
* 操作の **戻り値**（返す node、boolean、record の列）
* 操作の成否と例外
* 例外が起きた場合に状態が変わらないこと（`observe` に前の状態を渡すことで表す）

## 比較しない

* store の表現（entry の並び、id の割り当て方）。`observe` は id の昇順に正規化する。
* object identity のうち wrapper そのもの。model は node を生成しないので
  wrapper を作る API の同一性は観測できない（roadmap §13.3）。
  node を返す method の戻り値は `NodeId` で比べるので、
  「返ってきたのは渡した node そのものか」は観測できる。
* `Attr` の identity。`setAttributeNode` と `NamedNodeMap` はそれを要求するので扱わない。
* 文字列の内部表現。`data` は Lean の `String` として比べる。UTF-16 の code unit 境界は
  扱わない（roadmap §13.1）。
* `Attr` node としての attribute。model の attribute は element の状態であり
  node tree には入らないので、`NamedNodeMap` や `Attr` の同一性は観測できない。
* MutationObserver の callback そのもの。配送された record の列だけを見る。
* Shadow tree。
-/

namespace Dom

/-- 観測できる node の情報。 -/
structure ObservedNode where
  id : NodeId
  kind : NodeKind
  parent : Option NodeId
  children : List NodeId
  nodeDocument : NodeId
  data : String
  attributes : List Attr
  «namespace» : Option String
  «prefix» : Option String
  localName : String
  /-- `tagName`。Element 以外では `none`。 -/
  tagName : Option String
deriving DecidableEq, Repr, Inhabited

/-- 操作の結果。 -/
inductive OperationResult where
  | ok
  | failed (e : DOMException)
deriving DecidableEq, Repr, Inhabited

/--
操作の戻り値。

IDL が `undefined` を返す操作は `unit`。
`Node?` を返す操作（`appendChild` / `insertBefore` / `replaceChild` / `removeChild` と
`NodeIterator` の走査）は `node`、`toggleAttribute` は `bool`、
`takeRecords` は `records` である。

失敗した step には戻り値が無いので `unit` にする。
-/
inductive ReturnValue where
  | unit
  | node (n : Option NodeId)
  | bool (b : Bool)
  | records (rs : List MutationRecord)
  /-- `compareBoundaryPoints` と `comparePoint` の −1 / 0 / 1、`compareDocumentPosition` の mask。 -/
  | int (i : Int)
  /-- `textContent` のように null になりうる `DOMString?`。 -/
  | str (s : Option String)
  /-- `getAttributeNames()` の `sequence<DOMString>`。 -/
  | strs (l : List String)
deriving DecidableEq, Repr, Inhabited

/-- 一 step の観測。 -/
structure Observation where
  nodes : List ObservedNode
  ranges : List RangeState
  iterators : List IteratorState
  /-- §6.2 の `TreeWalker`。root は動かないので `current` だけが観測対象になる。 -/
  walkers : List WalkerState := []
  /-- observer ごとの record queue。`takeRecords()` が返すものである。 -/
  records : List (List MutationRecord)
  /-- microtask checkpoint で callback に渡された record。配送が無い step では空。 -/
  delivered : List (Nat × List MutationRecord) := []
  /-- 操作の戻り値。 -/
  returned : ReturnValue := .unit
  result : OperationResult
deriving DecidableEq, Repr, Inhabited

/-- 昇順に並んだ list から重複を落とす。 -/
def dedupSorted : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedupSorted (y :: rest) else x :: dedupSorted (y :: rest)

theorem mem_dedupSorted {x : Nat} : ∀ l : List Nat, x ∈ dedupSorted l ↔ x ∈ l
  | [] => by simp [dedupSorted]
  | [_] => by simp [dedupSorted]
  | y :: z :: rest => by
    by_cases h : y = z
    · rw [dedupSorted, if_pos h, mem_dedupSorted (z :: rest)]
      constructor
      · exact fun hm => List.mem_cons_of_mem _ hm
      · intro hm
        rcases List.mem_cons.mp hm with he | hm'
        · rw [he, h]; exact List.mem_cons_self ..
        · exact hm'
    · rw [dedupSorted, if_neg h]
      simp only [List.mem_cons, mem_dedupSorted (z :: rest)]

/-- 一つの node の観測。 -/
def observedNodeOf (t : Tree) (n : NodeId) (d : NodeData) : ObservedNode where
  id := n
  kind := d.kind
  parent := d.parent
  children := childrenOf t n
  nodeDocument := d.ownerDocument
  data := d.data
  attributes := d.attributes
  «namespace» := d.namespace
  «prefix» := d.prefix
  localName := d.localName
  tagName := Dom.tagName t n

/-- 木の観測。node は id の昇順に並べ、store の表現には依存させない。 -/
def observedNodes (s : DOMState) : List ObservedNode :=
  (dedupSorted ((s.tree.nodes.keys.map (·.id)).mergeSort (· ≤ ·))).filterMap fun i =>
    (s.tree.get? ⟨i⟩).map (observedNodeOf s.tree ⟨i⟩)

/--
状態と操作結果の観測。

例外で失敗した step では、仕様上状態は変わらないので、
`s` に **操作前の状態** を渡して「変わっていないこと」も比較対象に含める。
-/
def observe (s : DOMState) (result : OperationResult)
    (delivered : List (Nat × List MutationRecord) := [])
    (returned : ReturnValue := .unit) : Observation where
  nodes := observedNodes s
  ranges := s.ranges
  iterators := s.iterators
  walkers := s.walkers
  records := s.observers.map (·.records)
  delivered := delivered
  returned := returned
  result := result

/-! ## 観測は木を落とさないし、木に無いものを作らない -/

theorem mem_observedNodes {s : DOMState} {n : NodeId} {d : NodeData}
    (hd : s.tree.get? n = some d) : observedNodeOf s.tree n d ∈ observedNodes s := by
  unfold observedNodes
  refine List.mem_filterMap.mpr ⟨n.id, ?_, ?_⟩
  · rw [mem_dedupSorted]
    refine (List.mem_mergeSort ..).mpr ?_
    exact List.mem_map.mpr ⟨n, NodeStore.mem_keys_of_get?_eq_some hd, rfl⟩
  · rw [hd]
    rfl

theorem observedNodes_spec {s : DOMState} {on : ObservedNode} (h : on ∈ observedNodes s) :
    ∃ d, s.tree.get? on.id = some d ∧ on = observedNodeOf s.tree on.id d := by
  unfold observedNodes at h
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp h
  cases hd : s.tree.get? ⟨i⟩ with
  | none => rw [hd] at hi; simp at hi
  | some d =>
    rw [hd] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    have hid : on.id = ⟨i⟩ := by rw [← hi]; rfl
    rw [hid]
    exact ⟨d, hd, by rw [← hi]⟩

end Dom
