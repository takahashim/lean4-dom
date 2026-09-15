import Dom.Basic.NodeId
import Dom.Util.List

/-!
# `NodeStore`：`NodeId` から `NodeData` への finite map

model と theorem は、この module が公開する interface
（`get?`, `insert`, `erase`, `keys`, `size`）とその補題だけを通して store に触れる。
表現を差し替えたくなったとき、変更をこの module に閉じ込めるためである（PLAN §3.1）。

現在の表現は association list である。PLAN §3.1 は `Std.HashMap` を挙げているが、
Phase 1 の成果物は証明であり、必要な補題（`get?_insert_ne` など）を
外部 library の API 名に依存せず自前で証明できるほうが version 更新に強い。
`Std.HashMap` へ差し替える場合も、以下の補題群が同じ statement で成り立てばよい。
-/

namespace Dom

namespace Store

/-- association list に対する検索。先に現れた entry を優先する。 -/
def find? : List (NodeId × NodeData) → NodeId → Option NodeData
  | [], _ => none
  | (k, v) :: rest, k' => if k = k' then some v else find? rest k'

/-- association list から key `k` の entry をすべて取り除く。 -/
def eraseKey : List (NodeId × NodeData) → NodeId → List (NodeId × NodeData)
  | [], _ => []
  | (k, v) :: rest, k' => if k = k' then eraseKey rest k' else (k, v) :: eraseKey rest k'

end Store

/-- `NodeId` から `NodeData` への finite map。 -/
structure NodeStore where
  entries : List (NodeId × NodeData)
deriving Repr, Inhabited

namespace NodeStore

/-- 空の store。 -/
def empty : NodeStore := ⟨[]⟩

instance : EmptyCollection NodeStore := ⟨empty⟩

/-- `k` に対応する `NodeData`。存在しなければ `none`。 -/
def get? (s : NodeStore) (k : NodeId) : Option NodeData :=
  Store.find? s.entries k

/-- `k` の entry を取り除く。存在しなければ何もしない。 -/
def erase (s : NodeStore) (k : NodeId) : NodeStore :=
  ⟨Store.eraseKey s.entries k⟩

/-- `k` を `v` に対応付ける。既存の entry は置き換える。 -/
def insert (s : NodeStore) (k : NodeId) (v : NodeData) : NodeStore :=
  ⟨(k, v) :: Store.eraseKey s.entries k⟩

/-- store に含まれる key の列挙。重複を含まない保証はしない（補題側で必要としない）。 -/
def keys (s : NodeStore) : List NodeId :=
  s.entries.map Prod.fst

/-- store の entry 数。fuel の上界として使う。 -/
def size (s : NodeStore) : Nat :=
  s.entries.length

/-- `k` が store にあるか。 -/
def contains (s : NodeStore) (k : NodeId) : Bool :=
  (s.get? k).isSome

/-- `s` の各 entry に `f` を適用する。key は変えない。 -/
def mapValues (s : NodeStore) (f : NodeId → NodeData → NodeData) : NodeStore :=
  ⟨s.entries.map (fun p => (p.1, f p.1 p.2))⟩

/-- `k` の entry がある場合に限り `f` を適用する。 -/
def modify (s : NodeStore) (k : NodeId) (f : NodeData → NodeData) : NodeStore :=
  match s.get? k with
  | none => s
  | some d => s.insert k (f d)

end NodeStore

/-! ## interface の補題 -/

namespace Store

theorem find?_nil (k : NodeId) : find? [] k = none := rfl

theorem find?_cons_self (k : NodeId) (v : NodeData) (l : List (NodeId × NodeData)) :
    find? ((k, v) :: l) k = some v := by
  simp [find?]

theorem find?_cons_self' {a k : NodeId} (h : a = k) (v : NodeData)
    (l : List (NodeId × NodeData)) : find? ((a, v) :: l) k = some v := by
  simp [find?, h]

theorem find?_cons_ne {k k' : NodeId} (h : k ≠ k') (v : NodeData)
    (l : List (NodeId × NodeData)) :
    find? ((k, v) :: l) k' = find? l k' := by
  simp [find?, h]

theorem eraseKey_cons_self {a k : NodeId} (h : a = k) (v : NodeData)
    (l : List (NodeId × NodeData)) : eraseKey ((a, v) :: l) k = eraseKey l k := by
  simp [eraseKey, h]

theorem eraseKey_cons_ne {a k : NodeId} (h : a ≠ k) (v : NodeData)
    (l : List (NodeId × NodeData)) :
    eraseKey ((a, v) :: l) k = (a, v) :: eraseKey l k := by
  simp [eraseKey, h]

theorem find?_eraseKey_self :
    ∀ (l : List (NodeId × NodeData)) (k : NodeId), find? (eraseKey l k) k = none
  | [], _ => rfl
  | (a, v) :: rest, k => by
    by_cases h : a = k
    · rw [eraseKey_cons_self h]; exact find?_eraseKey_self rest k
    · rw [eraseKey_cons_ne h, find?_cons_ne h]; exact find?_eraseKey_self rest k

theorem find?_eraseKey_ne :
    ∀ (l : List (NodeId × NodeData)) {k k' : NodeId}, k ≠ k' →
      find? (eraseKey l k) k' = find? l k'
  | [], _, _, _ => rfl
  | (a, v) :: rest, k, k', h => by
    by_cases ha : a = k
    · have hak' : a ≠ k' := by rw [ha]; exact h
      rw [eraseKey_cons_self ha, find?_cons_ne hak']
      exact find?_eraseKey_ne rest h
    · rw [eraseKey_cons_ne ha]
      by_cases ha' : a = k'
      · rw [ha', find?_cons_self, find?_cons_self]
      · rw [find?_cons_ne ha', find?_cons_ne ha']
        exact find?_eraseKey_ne rest h

theorem length_eraseKey_le :
    ∀ (l : List (NodeId × NodeData)) (k : NodeId), (eraseKey l k).length ≤ l.length
  | [], _ => Nat.le_refl _
  | (a, v) :: rest, k => by
    by_cases h : a = k
    · rw [eraseKey_cons_self h, List.length_cons]
      exact Nat.le_trans (length_eraseKey_le rest k) (Nat.le_succ _)
    · rw [eraseKey_cons_ne h, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (length_eraseKey_le rest k)

theorem keys_eraseKey_subset :
    ∀ (l : List (NodeId × NodeData)) (k : NodeId),
      (eraseKey l k).map Prod.fst ⊆ l.map Prod.fst
  | [], _ => by simp [eraseKey]
  | (a, v) :: rest, k => by
    by_cases h : a = k
    · rw [eraseKey_cons_self h, List.map_cons]
      exact List.subset_cons_of_subset _ (keys_eraseKey_subset rest k)
    · rw [eraseKey_cons_ne h, List.map_cons, List.map_cons]
      exact List.cons_subset_cons _ (keys_eraseKey_subset rest k)

/-- 検索が成功する key は key の列に現れる。 -/
theorem mem_keys_of_find?_eq_some :
    ∀ (l : List (NodeId × NodeData)) {k : NodeId} {d : NodeData},
      find? l k = some d → k ∈ l.map Prod.fst
  | [], _, _, h => by simp [find?] at h
  | (a, v) :: rest, k, d, h => by
    by_cases ha : a = k
    · simp [ha]
    · rw [find?_cons_ne ha] at h
      exact List.mem_cons_of_mem _ (mem_keys_of_find?_eq_some rest h)

/-- 検索が成功する key と値の組は、entry の列に現れる。 -/
theorem mem_entries_of_find?_eq_some :
    ∀ (l : List (NodeId × NodeData)) {k : NodeId} {d : NodeData},
      find? l k = some d → (k, d) ∈ l
  | [], _, _, h => by simp [find?] at h
  | (a, v) :: rest, k, d, h => by
    by_cases ha : a = k
    · rw [find?_cons_self' ha] at h
      rw [← Option.some.inj h, ha]
      exact List.mem_cons_self ..
    · rw [find?_cons_ne ha] at h
      exact List.mem_cons_of_mem _ (mem_entries_of_find?_eq_some rest h)

end Store

namespace NodeStore

@[simp] theorem get?_empty (k : NodeId) : (empty).get? k = none := rfl

@[simp] theorem get?_insert_self (s : NodeStore) (k : NodeId) (v : NodeData) :
    (s.insert k v).get? k = some v :=
  Store.find?_cons_self k v _

theorem get?_insert_ne (s : NodeStore) {k k' : NodeId} (h : k ≠ k') (v : NodeData) :
    (s.insert k v).get? k' = s.get? k' := by
  show Store.find? ((k, v) :: Store.eraseKey s.entries k) k' = Store.find? s.entries k'
  rw [Store.find?_cons_ne h, Store.find?_eraseKey_ne _ h]

theorem get?_insert (s : NodeStore) (k k' : NodeId) (v : NodeData) :
    (s.insert k v).get? k' = if k = k' then some v else s.get? k' := by
  by_cases h : k = k'
  · subst h; simp
  · simp [get?_insert_ne s h, h]

@[simp] theorem get?_erase_self (s : NodeStore) (k : NodeId) :
    (s.erase k).get? k = none :=
  Store.find?_eraseKey_self s.entries k

theorem get?_erase_ne (s : NodeStore) {k k' : NodeId} (h : k ≠ k') :
    (s.erase k).get? k' = s.get? k' :=
  Store.find?_eraseKey_ne s.entries h

theorem get?_erase (s : NodeStore) (k k' : NodeId) :
    (s.erase k).get? k' = if k = k' then none else s.get? k' := by
  by_cases h : k = k'
  · subst h; simp
  · simp [get?_erase_ne s h, h]

theorem mem_keys_of_get?_eq_some {s : NodeStore} {k : NodeId} {d : NodeData}
    (h : s.get? k = some d) : k ∈ s.keys :=
  Store.mem_keys_of_find?_eq_some s.entries h

theorem mem_entries_of_get?_eq_some {s : NodeStore} {k : NodeId} {d : NodeData}
    (h : s.get? k = some d) : (k, d) ∈ s.entries :=
  Store.mem_entries_of_find?_eq_some s.entries h

theorem length_keys (s : NodeStore) : s.keys.length = s.size := by
  simp [keys, size]

theorem size_erase_le (s : NodeStore) (k : NodeId) : (s.erase k).size ≤ s.size :=
  Store.length_eraseKey_le s.entries k

theorem size_insert_le (s : NodeStore) (k : NodeId) (v : NodeData) :
    (s.insert k v).size ≤ s.size + 1 :=
  Nat.succ_le_succ (Store.length_eraseKey_le s.entries k)

theorem contains_iff (s : NodeStore) (k : NodeId) :
    s.contains k = true ↔ ∃ d, s.get? k = some d := by
  simp [contains, Option.isSome_iff_exists]

@[simp] theorem get?_mapValues (s : NodeStore) (f : NodeId → NodeData → NodeData) (k : NodeId) :
    (s.mapValues f).get? k = (s.get? k).map (f k) := by
  obtain ⟨entries⟩ := s
  show Store.find? (entries.map (fun p => (p.1, f p.1 p.2))) k
    = (Store.find? entries k).map (f k)
  induction entries with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    by_cases h : a = k
    · subst h; simp [Store.find?]
    · rw [List.map_cons]
      rw [Store.find?_cons_ne h, Store.find?_cons_ne h]
      exact ih

theorem get?_modify_self (s : NodeStore) (k : NodeId) (f : NodeData → NodeData) :
    (s.modify k f).get? k = (s.get? k).map f := by
  cases h : s.get? k with
  | none => simp [modify, h]
  | some d => simp [modify, h]

theorem get?_modify_ne (s : NodeStore) {k k' : NodeId} (h : k ≠ k') (f : NodeData → NodeData) :
    (s.modify k f).get? k' = s.get? k' := by
  cases hd : s.get? k with
  | none => simp [modify, hd]
  | some d => simp [modify, hd, get?_insert_ne s h]

end NodeStore

end Dom
