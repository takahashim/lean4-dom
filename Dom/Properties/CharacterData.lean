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

theorem kindPreserving_withData {t : Tree} {n : NodeId} {d : NodeData} (hd : t.get? n = some d)
    (newData : String) : KindPreserving t (withData t n d newData) := by
  intro m
  rw [get?_withData hd]
  by_cases h : m = n
  · subst h; simp [hd]
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
    ∃ d, s.tree.get? n = some d ∧ d.kind.isCharacterData = true ∧ offset ≤ d.length ∧
      s'.tree = withData s.tree n d
        (spliceData d.data offset (adjustedCount d.length offset count) data) ∧
      s'.ranges = s.ranges.map
        (replaceDataAdjustRange n offset (adjustedCount d.length offset count) data.length) ∧
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
        rw [← Except.ok.inj h]
        exact ⟨d, hd, by simpa using hk, by omega, rfl, rfl, rfl⟩

/-- PLAN §10.2。`replaceData` は well-formedness を保つ。 -/
theorem replaceData_preserves_wellformed {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hwf : WellFormed s.tree) (h : replaceData s n offset count data = .ok s') :
    WellFormed s'.tree := by
  obtain ⟨d, hd, _, _, ht, _, _⟩ := replaceData_ok h
  rw [ht]
  exact wellFormed_withData hwf hd _

/-- PLAN §10.2。`replaceData` は range の両端を木の中に保つ。 -/
theorem replaceData_preserves_endpoints {s s' : DOMState} {n : NodeId} {offset count : Nat}
    {data : String} (hv : RangeEndpointsValid s)
    (h : replaceData s n offset count data = .ok s') : RangeEndpointsValid s' := by
  obtain ⟨d, hd, hk, hoff, ht, hr, _⟩ := replaceData_ok h
  obtain ⟨c, hc⟩ : ∃ c, c = adjustedCount d.length offset count := ⟨_, rfl⟩
  rw [← hc] at ht hr
  have hdlen : d.length = d.data.length := NodeData.length_characterData hk
  have hoff' : offset ≤ d.data.length := by rw [← hdlen]; exact hoff
  have hsum : offset + c ≤ d.data.length := by
    rw [← hdlen, hc]; exact adjustedCount_le hoff
  have hnew : (spliceData d.data offset c data).length + c = d.data.length + data.length :=
    length_spliceData hoff' hsum
  -- 各 boundary point について
  have hbp : ∀ bp, ValidBoundaryPoint s.tree bp →
      ValidBoundaryPoint s'.tree (replaceDataAdjustBP n offset c data.length bp) := by
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
      have hnode : s'.tree.get? bp.node =
          some { d with data := spliceData d.data offset c data } := by
        rw [ht, get?_withData hd, if_pos heq]
      have hnlen : ({ d with data := spliceData d.data offset c data } : NodeData).length =
          (spliceData d.data offset c data).length :=
        NodeData.length_characterData hk
      have hb : bp.offset ≤ d.data.length := by rw [← hdlen]; exact hoffb
      by_cases h1 : offset < bp.offset ∧ bp.offset ≤ offset + c
      · rw [if_pos h1]
        exact ⟨_, hnode, by show offset ≤ _; rw [hnlen]; omega⟩
      · rw [if_neg h1]
        by_cases h2 : offset + c < bp.offset
        · rw [if_pos h2]
          exact ⟨_, hnode, by show bp.offset + data.length - c ≤ _; rw [hnlen]; omega⟩
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

end Dom
