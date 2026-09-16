import Dom.Exec.Invariant

/-!
# `BoundaryLE` の negative result

`docs/status.md` の「`insert` 側の `BoundaryLE` は **保たれない**（仕様の性質）」。

live range の「start ≤ end」は、**仕様の invariant ではない**。
`insert` は step 5（parent を指す boundary point の offset を `+count` する）を
step 7 の adopt → remove より前に走らせる。
動かす node の中にあった boundary point は step 7 で `(旧 parent, 旧 index)` に出るが、
その時点では step 5 の `+count` はもう済んでいる。
node 自身はその位置より前に入るので、start と end が逆転しうる。

ここでは具体的な admissible 状態と一つの `insertBefore` を挙げて、それを定理として残す。
`test/scenarios/range-order-broken-by-insert.json` が同じ例の JSON 版である。

* node 0：Document
* node 1：element（node 0 の子）、children は [2, 3]
* node 2：Comment（data "cc"）
* node 3：Text（data "tt"）
* range：start = (2, 0)、end = (3, 2)

`element1.insertBefore(text3, comment2)` を呼ぶと children は [3, 2] になり、
range は start = (2, 0)、end = (1, 1) になる。
node 2 は index 1 なので start は end より後ろであり、順序は壊れている。
-/

namespace Dom

/-- §8 の反例に使う初期状態。 -/
def boundaryLECounterexample : DOMState where
  tree :=
    { nodes :=
        (((NodeStore.empty.insert ⟨0⟩
            { kind := .document, parent := none, children := [⟨1⟩], ownerDocument := ⟨0⟩ }).insert
            ⟨1⟩
            { kind := .element, parent := some ⟨0⟩, children := [⟨2⟩, ⟨3⟩],
              ownerDocument := ⟨0⟩ }).insert ⟨2⟩
            { kind := .comment, parent := some ⟨1⟩, ownerDocument := ⟨0⟩, data := "cc" }).insert
            ⟨3⟩
            { kind := .text, parent := some ⟨1⟩, ownerDocument := ⟨0⟩, data := "tt" } }
  ranges := [{ start := ⟨⟨2⟩, 0⟩, «end» := ⟨⟨3⟩, 2⟩ }]

/-- 反例の操作の結果。 -/
def boundaryLECounterexampleStep : Except DOMException DOMState :=
  insertBefore boundaryLECounterexample ⟨1⟩ ⟨3⟩ (some ⟨2⟩)

/-- 反例の操作は成功し、range は start = (2, 0)、end = (1, 1) になる。 -/
def boundaryLECounterexampleAfter : DOMState :=
  match boundaryLECounterexampleStep with
  | .ok s => s
  | .error _ => boundaryLECounterexample

theorem boundaryLECounterexample_step :
    insertBefore boundaryLECounterexample ⟨1⟩ ⟨3⟩ (some ⟨2⟩)
      = .ok boundaryLECounterexampleAfter := rfl

/--
§8 の negative result。

**`insert` は live range の start ≤ end を保たない。**

admissible な状態と、両端が正しく並んだ range と、一回の `insertBefore` があって、
操作後も状態は admissible で range の両端は木の中にあるのに、
start ≤ end が成り立たない。

range は操作の前後でちょうど一つなので、対応関係に曖昧さは無い。
-/
theorem exists_insert_breaking_boundaryLE :
    ∃ (s s' : DOMState) (parent node child : NodeId) (r r' : RangeState),
      AdmissibleDOMState s ∧
      s.ranges = [r] ∧
      BoundaryLE s.tree r.start r.«end» ∧
      insertBefore s parent node (some child) = .ok s' ∧
      AdmissibleDOMState s' ∧
      s'.ranges = [r'] ∧
      ValidBoundaryPoint s'.tree r'.start ∧
      ValidBoundaryPoint s'.tree r'.«end» ∧
      ¬ BoundaryLE s'.tree r'.start r'.«end» := by
  refine ⟨boundaryLECounterexample, boundaryLECounterexampleAfter, ⟨1⟩, ⟨3⟩, ⟨2⟩,
    { start := ⟨⟨2⟩, 0⟩, «end» := ⟨⟨3⟩, 2⟩ }, { start := ⟨⟨2⟩, 0⟩, «end» := ⟨⟨1⟩, 1⟩ },
    ?_, rfl, ?_, boundaryLECounterexample_step, ?_, rfl, ?_, ?_, ?_⟩
  · exact (checkAdmissibleDOMState_iff _).mp (by decide)
  · exact (checkBoundaryLE_iff _ _ _).mp (by decide)
  · exact (checkAdmissibleDOMState_iff _).mp (by decide)
  · exact (checkValidBoundaryPoint_iff _ _).mp (by decide)
  · exact (checkValidBoundaryPoint_iff _ _).mp (by decide)
  · intro hle
    have := (checkBoundaryLE_iff boundaryLECounterexampleAfter.tree ⟨⟨2⟩, 0⟩ ⟨⟨1⟩, 1⟩).mpr hle
    exact absurd this (by decide)

/--
同じ反例を admissibility の側から見たもの。

`AdmissibleDOMState` に `BoundaryLE` を入れてしまうと、`insert` で閉じない。
`Dom/Validity/State.lean` が range について両端の validity しか要求しないのはこのためである。
-/
theorem boundaryLE_not_preserved_by_insert :
    ¬ ∀ (s s' : DOMState) (parent node : NodeId) (child : Option NodeId),
        AdmissibleDOMState s →
        (∀ r ∈ s.ranges, BoundaryLE s.tree r.start r.«end») →
        insertBefore s parent node child = .ok s' →
        ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end» := by
  intro h
  obtain ⟨s, s', parent, node, child, r, r', hadm, hr, hle, hstep, _, hr', _, _, hbad⟩ :=
    exists_insert_breaking_boundaryLE
  refine hbad (h s s' parent node (some child) hadm ?_ hstep r' ?_)
  · intro x hx
    rw [hr] at hx
    rcases List.mem_singleton.mp hx with rfl
    exact hle
  · rw [hr']
    simp

end Dom
