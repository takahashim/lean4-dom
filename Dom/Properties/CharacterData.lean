import Dom.CharacterData.ReplaceData
import Dom.Properties.Range

/-!
# Phase 7 の theorem

PLAN §10.2 に挙げた性質を証明する。

* `replaceData_preserves_wellformed` — 木は変わらないので直ちに従う
* `replaceData_preserves_endpoints` — range の両端は木の中に留まる

`replace data` は node の `data` しか変えないので、
parent と children、kind、node document はどれも変わらない。
-/

namespace Dom

/-! ## data だけを変える変更 -/

/-- `data` だけを差し替えた木。 -/
def withData (t : Tree) (n : NodeId) (d : NodeData) (newData : String) : Tree :=
  { t with nodes := t.nodes.insert n { d with data := newData } }

theorem get?_withData {t : Tree} {n : NodeId} {d : NodeData} (_hd : t.get? n = some d)
    (newData : String) (m : NodeId) :
    (withData t n d newData).get? m =
      if m = n then some { d with data := newData } else t.get? m := by
  show (t.nodes.insert n { d with data := newData }).get? m = _
  rw [NodeStore.get?_insert]
  by_cases h : m = n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]
    rfl

theorem parentOf_withData {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (newData : String) (m : NodeId) : parentOf (withData t n d newData) m = parentOf t m := by
  unfold parentOf
  rw [get?_withData hd]
  by_cases h : m = n
  · subst h; simp [hd]
  · rw [if_neg h]

theorem childrenOf_withData {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (newData : String) (m : NodeId) : childrenOf (withData t n d newData) m = childrenOf t m := by
  unfold childrenOf
  rw [get?_withData hd]
  by_cases h : m = n
  · subst h; simp [hd]
  · rw [if_neg h]

theorem shapePreserving_withData {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (newData : String) : ShapePreserving t (withData t n d newData) := by
  intro m
  rw [get?_withData hd]
  by_cases h : m = n
  · subst h; simp [hd, NodeData.shape]
  · rw [if_neg h]

/-- PLAN §10.2。`data` だけを変える変更は well-formedness を保つ。 -/
theorem wellFormed_withData {t : Tree} {n : NodeId} {d : NodeData} (hwf : WellFormed t)
    (hd : t.get? n = some d) (newData : String) : WellFormed (withData t n d newData) := by
  refine wellFormed_of ?_ ?_ ?_ ?_
  · intro c q
    rw [parentOf_withData hd, childrenOf_withData hd]
    exact mem_childrenOf_iff hwf c q
  · intro m dm hm
    rw [get?_withData hd] at hm
    by_cases h : m = n
    · rw [if_pos h] at hm
      cases hm
      show d.children.Nodup
      exact hwf.children_nodup n d hd
    · rw [if_neg h] at hm
      exact hwf.children_nodup m dm hm
  · intro m hm
    refine hwf.acyclic m (ancestor_of_parentOf_subset ?_ hm)
    intro x y hxy
    rw [← parentOf_withData hd newData x]
    exact hxy
  · refine ownerDocument_is_document_of hwf ?_ ?_
    · intro m dm hm
      rw [get?_withData hd] at hm
      by_cases h : m = n
      · rw [if_pos h] at hm; cases hm; exact ⟨d, by rw [← h] at hd; exact hd, rfl⟩
      · rw [if_neg h] at hm; exact ⟨dm, hm, rfl⟩
    · intro m d₀ hm
      rw [get?_withData hd]
      by_cases h : m = n
      · rw [if_pos h]
        rw [h, hd] at hm
        cases hm
        exact ⟨_, rfl, rfl⟩
      · rw [if_neg h]; exact ⟨d₀, hm, rfl⟩

/-! ## replaceData -/

/-- `replaceData` が成功したときの結果の形。 -/
theorem replaceData_ok {s s' : DOMState} {n : NodeId} {offset count : Nat} {data : String}
    (h : replaceData s n offset count data = .ok s') :
    ∃ d spliced, s.tree.get? n = some d ∧ d.kind.isCharacterData = true ∧ offset ≤ d.length ∧
      spliceData? d.data offset (adjustedCount d.length offset count) data = some spliced ∧
      s'.tree = withData s.tree n d spliced ∧
      s'.ranges = s.ranges.map
        (replaceDataAdjustRange n offset (adjustedCount d.length offset count)
          (Utf16.length data)) ∧
      s'.iterators = s.iterators := by
  unfold replaceData at h
  split at h
  · simp at h
  · next d hd =>
    split at h
    · simp at h
    · next hk =>
      split at h
      · simp at h
      · next hlen =>
        split at h
        · simp at h
        · next spliced hsp =>
          rw [← Except.ok.inj h]
          exact ⟨d, spliced, hd, by simpa using hk, by omega, hsp, rfl, rfl, by simp⟩

/-- `replace data` は `data` しか変えないので kind と attribute list は変わらない。 -/
theorem shapePreserving_replaceData {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hr : replaceData s n offset count data = .ok s') :
    ShapePreserving s.tree s'.tree := by
  obtain ⟨d, _, hd, _, _, _, htree, _, _⟩ := replaceData_ok hr
  rw [htree]
  exact shapePreserving_withData hd _

/-- PLAN §10.2。`replaceData` は well-formedness を保つ。 -/
theorem replaceData_preserves_wellformed {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hwf : WellFormed s.tree) (h : replaceData s n offset count data = .ok s') :
    WellFormed s'.tree := by
  obtain ⟨d, _, hd, _, _, _, ht, _, _⟩ := replaceData_ok h
  rw [ht]
  exact wellFormed_withData hwf hd _

/-- PLAN §10.2。`replaceData` は range の両端を木の中に保つ。 -/
theorem replaceData_preserves_endpoints {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hv : RangeEndpointsValid s)
    (h : replaceData s n offset count data = .ok s') : RangeEndpointsValid s' := by
  obtain ⟨d, spliced, hd, hk, hoff, hsp, ht, hr, _⟩ := replaceData_ok h
  obtain ⟨c, hc⟩ : ∃ c, c = adjustedCount d.length offset count := ⟨_, rfl⟩
  rw [← hc] at hr hsp
  have hdlen : d.length = Utf16.length d.data := NodeData.length_characterData hk
  -- 切断が成功したことから長さの等式が出る。
  -- 「pair を割らない」という条件をここから先へ持ち出す必要はない。
  have hnew : Utf16.length spliced + c = Utf16.length d.data + Utf16.length data :=
    length_spliceData? hsp
  have hsum : offset + c ≤ Utf16.length d.data := by
    rw [← hdlen, hc]; exact adjustedCount_le hoff
  -- 各 boundary point について
  have hbp : ∀ bp, ValidBoundaryPoint s.tree bp →
      ValidBoundaryPoint s'.tree (replaceDataAdjustBP n offset c (Utf16.length data) bp) := by
    intro bp hbpv
    obtain ⟨db, hdb, hoffb⟩ := hbpv
    unfold replaceDataAdjustBP
    by_cases hne : bp.node ≠ n
    · rw [if_pos hne]
      exact ⟨db, by rw [ht, get?_withData hd, if_neg hne]; exact hdb, hoffb⟩
    · have heq : bp.node = n := by simpa using hne
      rw [if_neg hne]
      have hdbd : d = db := by rw [heq, hd] at hdb; exact Option.some.inj hdb
      subst hdbd
      have hnode : s'.tree.get? bp.node = some { d with data := spliced } := by
        rw [ht, get?_withData hd, if_pos heq]
      have hnlen : ({ d with data := spliced } : NodeData).length = Utf16.length spliced :=
        NodeData.length_characterData hk
      have hb : bp.offset ≤ Utf16.length d.data := by rw [← hdlen]; exact hoffb
      by_cases h1 : offset < bp.offset ∧ bp.offset ≤ offset + c
      · rw [if_pos h1]
        exact ⟨_, hnode, by show offset ≤ _; rw [hnlen]; omega⟩
      · rw [if_neg h1]
        by_cases h2 : offset + c < bp.offset
        · rw [if_pos h2]
          exact ⟨_, hnode, by show bp.offset + Utf16.length data - c ≤ _; rw [hnlen]; omega⟩
        · rw [if_neg h2]
          have hle : bp.offset ≤ offset := by
            rcases Nat.lt_or_ge offset bp.offset with hlt | hge
            · exact (h1 ⟨hlt, by omega⟩).elim
            · exact hge
          exact ⟨_, hnode, by show bp.offset ≤ _; rw [hnlen]; omega⟩
  intro r hrmem
  rw [hr] at hrmem
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hrmem
  obtain ⟨hs, he⟩ := hv r₀ hr₀
  rw [← hrr]
  exact ⟨hbp _ hs, hbp _ he⟩

/-! ## wrapper -/

theorem appendData_preserves_wellformed {s s' : DOMState} {n : NodeId} {data : String}
    (hwf : WellFormed s.tree) (h : appendData s n data = .ok s') : WellFormed s'.tree := by
  unfold appendData at h
  split at h
  · simp at h
  · exact replaceData_preserves_wellformed hwf h

theorem insertData_preserves_wellformed {s s' : DOMState} {n : NodeId} {offset : Nat}
    {data : String} (hwf : WellFormed s.tree) (h : insertData s n offset data = .ok s') :
    WellFormed s'.tree :=
  replaceData_preserves_wellformed hwf h

theorem deleteData_preserves_wellformed {s s' : DOMState} {n : NodeId} {offset count : Nat}
    (hwf : WellFormed s.tree) (h : deleteData s n offset count = .ok s') : WellFormed s'.tree :=
  replaceData_preserves_wellformed hwf h

theorem setData_preserves_wellformed {s s' : DOMState} {n : NodeId} {data : String}
    (hwf : WellFormed s.tree) (h : setData s n data = .ok s') : WellFormed s'.tree := by
  unfold setData at h
  split at h
  · simp at h
  · exact replaceData_preserves_wellformed hwf h

theorem appendData_preserves_endpoints {s s' : DOMState} {n : NodeId} {data : String}
    (hv : RangeEndpointsValid s) (h : appendData s n data = .ok s') : RangeEndpointsValid s' := by
  unfold appendData at h
  split at h
  · simp at h
  · exact replaceData_preserves_endpoints hv h

theorem insertData_preserves_endpoints {s s' : DOMState} {n : NodeId} {offset : Nat}
    {data : String} (hv : RangeEndpointsValid s) (h : insertData s n offset data = .ok s') :
    RangeEndpointsValid s' :=
  replaceData_preserves_endpoints hv h

theorem deleteData_preserves_endpoints {s s' : DOMState} {n : NodeId} {offset count : Nat}
    (hv : RangeEndpointsValid s) (h : deleteData s n offset count = .ok s') :
    RangeEndpointsValid s' :=
  replaceData_preserves_endpoints hv h

theorem setData_preserves_endpoints {s s' : DOMState} {n : NodeId} {data : String}
    (hv : RangeEndpointsValid s) (h : setData s n data = .ok s') : RangeEndpointsValid s' := by
  unfold setData at h
  split at h
  · simp at h
  · exact replaceData_preserves_endpoints hv h

/-! ## 同じ node の上の順序 -/

theorem replaceDataAdjustBP_at {n : NodeId} {offset count newLen : Nat} {bp : BoundaryPoint}
    (h : bp.node = n) :
    replaceDataAdjustBP n offset count newLen bp =
      if offset < bp.offset ∧ bp.offset ≤ offset + count then { bp with offset := offset }
      else if offset + count < bp.offset then { bp with offset := bp.offset + newLen - count }
      else bp := by
  unfold replaceDataAdjustBP
  rw [if_neg (by simpa using h)]

theorem replaceDataAdjustBP_other {n : NodeId} {offset count newLen : Nat} {bp : BoundaryPoint}
    (h : bp.node ≠ n) : replaceDataAdjustBP n offset count newLen bp = bp := by
  unfold replaceDataAdjustBP
  rw [if_pos h]

theorem replaceDataAdjustBP_mono {n : NodeId} {offset count newLen : Nat} {a b : BoundaryPoint}
    (hnode : a.node = b.node) (hle : a.offset ≤ b.offset) :
    (replaceDataAdjustBP n offset count newLen a).node =
        (replaceDataAdjustBP n offset count newLen b).node ∧
      (replaceDataAdjustBP n offset count newLen a).offset ≤
        (replaceDataAdjustBP n offset count newLen b).offset := by
  by_cases hne : a.node = n
  · have hbn : b.node = n := by rw [← hnode]; exact hne
    have ha := replaceDataAdjustBP_at (n := n) (offset := offset) (count := count)
      (newLen := newLen) hne
    have hb := replaceDataAdjustBP_at (n := n) (offset := offset) (count := count)
      (newLen := newLen) hbn
    rw [ha, hb]
    by_cases h1 : offset < a.offset ∧ a.offset ≤ offset + count
    · rw [if_pos h1]
      by_cases h2 : offset < b.offset ∧ b.offset ≤ offset + count
      · rw [if_pos h2]; exact ⟨hnode, Nat.le_refl _⟩
      · rw [if_neg h2]
        by_cases h3 : offset + count < b.offset
        · rw [if_pos h3]
          exact ⟨hnode, by show offset ≤ b.offset + newLen - count; omega⟩
        · rw [if_neg h3]; exact ⟨hnode, by show offset ≤ b.offset; omega⟩
    · rw [if_neg h1]
      by_cases h3 : offset + count < a.offset
      · rw [if_pos h3]
        rw [if_neg (show ¬(offset < b.offset ∧ b.offset ≤ offset + count) from fun hc => by omega),
          if_pos (show offset + count < b.offset by omega)]
        exact ⟨hnode, by show a.offset + newLen - count ≤ b.offset + newLen - count; omega⟩
      · rw [if_neg h3]
        by_cases h2 : offset < b.offset ∧ b.offset ≤ offset + count
        · rw [if_pos h2]; exact ⟨hnode, by show a.offset ≤ offset; omega⟩
        · rw [if_neg h2]
          by_cases h4 : offset + count < b.offset
          · rw [if_pos h4]
            exact ⟨hnode, by show a.offset ≤ b.offset + newLen - count; omega⟩
          · rw [if_neg h4]; exact ⟨hnode, hle⟩
  · have hbn : b.node ≠ n := by rw [← hnode]; exact hne
    rw [replaceDataAdjustBP_other hne, replaceDataAdjustBP_other hbn]
    exact ⟨hnode, hle⟩

/-- PLAN §8.3 / §10.2。`replaceData` は「両端が同じ node を指す range」の順序を保つ。 -/
theorem replaceData_preserves_sameNodeOrdered {s s' : DOMState} {n : NodeId}
    {offset count : Nat} {data : String} (hv : RangesSameNodeOrdered s)
    (h : replaceData s n offset count data = .ok s') : RangesSameNodeOrdered s' := by
  obtain ⟨d, _, hd, hk, hoff, _, ht, hr, _⟩ := replaceData_ok h
  intro r hrmem
  rw [hr] at hrmem
  obtain ⟨r₀, hr₀, hrr⟩ := List.mem_map.mp hrmem
  obtain ⟨hn, ho⟩ := hv r₀ hr₀
  rw [← hrr]
  exact replaceDataAdjustBP_mono hn ho

theorem replaceData_preserves_boundaryLE {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hv : RangesSameNodeOrdered s)
    (h : replaceData s n offset count data = .ok s') :
    ∀ r ∈ s'.ranges, BoundaryLE s'.tree r.start r.«end» :=
  boundaryLE_of_sameNodeOrdered (replaceData_preserves_sameNodeOrdered hv h)

end Dom
