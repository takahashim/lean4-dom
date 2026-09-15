import Dom.Basic.Tree

/-!
# 新しい node の id

仕様に node の id は無い。`NodeId` は model が node の同一性を表すために持つもので、
node を作る algorithm（§4.5 の `createElement` ほか）を書くには
「まだ誰も使っていない id」が要る。

**allocator を状態に足すのではなく、木から導く。** store にある id の最大より
一つ大きいものを使う。こうすると「新しい」ことが `DOMState` の invariant ではなく
store についての定理になり、既存の不変条件を増やさずに済む。

これが成り立つのは、**model が store から node を消さない**からである。
`detach` は parent を切るだけで entry は残る。だから最大値は下がらず、
一度使った id が後でまた新しいものとして出てくることはない。
-/

namespace Dom

/-- store にある id の最大。空なら 0。 -/
def maxId (t : Tree) : Nat := t.nodes.keys.foldl (fun m k => max m k.id) 0

/-- `foldl max` は初期値以上で、要素の id 以上である。 -/
theorem le_foldl_max : ∀ (l : List NodeId) (init : Nat), init ≤ l.foldl (fun m k => max m k.id) init
  | [], _ => Nat.le_refl _
  | k :: rest, init =>
    Nat.le_trans (Nat.le_max_left init k.id) (le_foldl_max rest (max init k.id))

theorem id_le_foldl_max : ∀ (l : List NodeId) (init : Nat) {k : NodeId}, k ∈ l →
    k.id ≤ l.foldl (fun m k => max m k.id) init
  | [], _, _, h => absurd h (by simp)
  | x :: rest, init, k, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact Nat.le_trans (Nat.le_max_right init k.id) (le_foldl_max rest (max init k.id))
    · exact id_le_foldl_max rest (max init x.id) hrest

/-- 木にある node の id は `maxId` 以下である。 -/
theorem id_le_maxId {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    n.id ≤ maxId t :=
  id_le_foldl_max _ 0 (NodeStore.mem_keys_of_get?_eq_some h)

/-- 新しい node に割り当てる id。 -/
def freshId (t : Tree) : NodeId := ⟨maxId t + 1⟩

/-- **`freshId` は木に無い。** -/
theorem freshId_get?_eq_none (t : Tree) : t.get? (freshId t) = none := by
  cases h : t.get? (freshId t) with
  | none => rfl
  | some d =>
    exfalso
    have := id_le_maxId h
    simp only [freshId] at this
    omega

/-- したがって、木にある node は `freshId` ではない。 -/
theorem ne_freshId {t : Tree} {n : NodeId} {d : NodeData} (h : t.get? n = some d) :
    n ≠ freshId t := by
  intro he
  rw [he, freshId_get?_eq_none] at h
  simp at h

end Dom
