import Dom.Properties.NodeQuery

/-!
# 名前空間の探索の性質（§4.4）

`lookupNamespaceURI` / `lookupPrefix` は "locate a namespace" / "locate a namespace prefix" を
element chain の上で走らせる。二つは互いの逆のように見えるが、そうではない。

* **element 自身の prefix は往復する**（`lookupNamespaceURI_lookupPrefix_own`）。
  `lookupPrefix(ns)` が element 自身の prefix を返すなら、`lookupNamespaceURI` はそれを
  element 自身の namespace に戻す。ただし `NamespaceWellFormed` が要る。
  prefix が `xml` / `xmlns` のとき、"locate a namespace" は木を見ずに固定値を返すからである。
* **一般には往復しない**（`lookup_round_trip_fails`）。同じ element に、自分の prefix を別の
  namespace に結ぶ `xmlns:` 属性があると、`lookupPrefix` は属性を、`lookupNamespaceURI` は
  element 自身を見る（step 3 が step 4 より先）。仕様どおりの挙動で、Chromium・WebKit・Dommy も
  そう答える（Firefox は `docs/status.md` の既知の divergence）。
* **step 2 と step 4 の非対称は、名前が整っていれば消える**（`find?_xmlnsDecl_eq`）。
  "locate a namespace prefix" の step 2 は「prefix が `xmlns`」しか見ず、namespace を見ない。
  "locate a namespace" の step 4 は namespace が XMLNS namespace であることも求める。
  `NamespaceWellFormed` は prefix `xmlns` の attribute を XMLNS namespace に置くので、
  二つが拾う attribute は同じになる。
-/

namespace Dom

/-! ## element 自身の prefix -/

/--
**element 自身の prefix は、element 自身の namespace に解決される。**

prefix が空文字列だと `lookupNamespaceURI` は null を渡したことになるので除く。
-/
theorem lookupNamespaceURI_own_prefix {t : Tree} {n : NodeId} {d : NodeData} {p ns : String}
    (hn : t.get? n = some d) (hk : d.kind = .element) (hp : d.prefix = some p) (hp' : p ≠ "")
    (hns : d.namespace = some ns) (hw : NamespaceWellFormed d.namespace d.prefix d.localName) :
    lookupNamespaceURI t n (some p) = some ns := by
  obtain ⟨rest, hchain⟩ := elementChain_of_element (e := n) (t := t)
    (by rw [kindOf_of_get? hn, hk])
  unfold lookupNamespaceURI locateNamespace
  rw [if_neg (by simpa using hp'), hn]
  simp only [hk, hchain, locateNamespaceIn, hn]
  by_cases hx : p = "xml"
  · subst hx
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [← hns, hw.xmlPrefix hp]
  · by_cases hxs : p = "xmlns"
    · subst hxs
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [if_neg (by decide), ← hns, hw.xmlnsPrefix hp]
    · have h1 : (some p == some "xml") = false := by simpa using hx
      have h2 : (some p == some "xmlns") = false := by simpa using hxs
      simp [h1, h2, hns, hp]

/-- **`lookupPrefix` は、element 自身の namespace に element 自身の prefix を返す**（step 1）。 -/
theorem lookupPrefix_own_namespace {t : Tree} {n : NodeId} {d : NodeData} {p ns : String}
    (hn : t.get? n = some d) (hk : d.kind = .element) (hp : d.prefix = some p)
    (hns : d.namespace = some ns) (hns' : ns ≠ "") :
    lookupPrefix t n (some ns) = some p := by
  obtain ⟨rest, hchain⟩ := elementChain_of_element (e := n) (t := t)
    (by rw [kindOf_of_get? hn, hk])
  simp [lookupPrefix, hns', hn, hk, hchain, locateNamespacePrefixIn, hns, hp]

/-- **element 自身の prefix は往復する。** -/
theorem lookupNamespaceURI_lookupPrefix_own {t : Tree} {n : NodeId} {d : NodeData}
    {p ns : String} (hn : t.get? n = some d) (hk : d.kind = .element) (hp : d.prefix = some p)
    (hp' : p ≠ "") (hns : d.namespace = some ns) (hns' : ns ≠ "")
    (hw : NamespaceWellFormed d.namespace d.prefix d.localName) :
    lookupPrefix t n (some ns) = some p ∧ lookupNamespaceURI t n (some p) = some ns :=
  ⟨lookupPrefix_own_namespace hn hk hp hns hns',
    lookupNamespaceURI_own_prefix hn hk hp hp' hns hw⟩

/-! ## 一般には往復しない -/

/--
往復しない例。Document の下に element が一つあり、その element は

* namespace `urn:x`、prefix `a`
* attribute `xmlns:a="urn:y"`（XMLNS namespace、prefix `xmlns`、local name `a`）

を持つ。名前はどれも `NamespaceWellFormed` を満たす。
-/
def lookupRoundTripCounterexample : Tree :=
  { nodes :=
      (NodeStore.empty.insert ⟨0⟩
          { kind := .document, children := [⟨1⟩], ownerDocument := ⟨0⟩ }).insert ⟨1⟩
        { kind := .element, parent := some ⟨0⟩, ownerDocument := ⟨0⟩,
          «namespace» := some "urn:x", «prefix» := some "a", localName := "e",
          attributes := [{ id := ⟨1⟩, «namespace» := some xmlnsNamespace, «prefix» := some "xmlns",
                           localName := "a", value := "urn:y", ownerDocument := ⟨0⟩ }] } }

/--
**`lookupPrefix` と `lookupNamespaceURI` は互いの逆ではない。**

well-formed な木の、名前の整った element で、`lookupPrefix("urn:y")` は `a` を返すが、
`lookupNamespaceURI("a")` は `urn:y` ではなく `urn:x` を返す。
"locate a namespace prefix" の step 1 は element 自身の namespace（`urn:x`）が違うので
step 2 の attribute に進み、"locate a namespace" の step 3 は element 自身の prefix が
一致するので step 4 の attribute を見ない。
-/
theorem lookup_round_trip_fails :
    ∃ (t : Tree) (n : NodeId) (d : NodeData) (ns p : String),
      t.checkWellFormed = true ∧ t.get? n = some d ∧
      namespaceWellFormedB d.namespace d.prefix d.localName = true ∧
      (d.attributes.all fun a => namespaceWellFormedB a.namespace a.prefix a.localName) = true ∧
      lookupPrefix t n (some ns) = some p ∧
      lookupNamespaceURI t n (some p) ≠ some ns :=
  ⟨lookupRoundTripCounterexample, ⟨1⟩, _, "urn:y", "a", by decide, rfl, by decide, by decide,
    by decide, by decide⟩

/-! ## step 2 と step 4 の非対称 -/

private theorem find?_congr_mem {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: rest, h => by
    rw [List.find?_cons, List.find?_cons, h x (List.mem_cons_self ..),
      find?_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/--
**名前の整った attribute list では、"locate a namespace prefix" step 2 が拾う attribute は、
namespace も確かめたときと同じである。**

step 2 は「prefix が `xmlns` で値が namespace」しか見ない。"locate a namespace" step 4 は
これに「namespace が XMLNS namespace」を足す。`NamespaceWellFormed.xmlnsPrefix` が
後者を前者から導くので、二つの探索は同じ attribute で止まる。
-/
theorem find?_xmlnsDecl_eq {as : List Attr}
    (h : ∀ a ∈ as, NamespaceWellFormed a.namespace a.prefix a.localName) (v : String) :
    as.find? (fun a => a.prefix == some "xmlns" && a.value == v) =
      as.find? (fun a => a.namespace == some xmlnsNamespace && a.prefix == some "xmlns" &&
        a.value == v) := by
  apply find?_congr_mem
  intro a ha
  by_cases hp : a.prefix = some "xmlns"
  · simp [hp, (h a ha).xmlnsPrefix hp]
  · have hf : (a.prefix == some "xmlns") = false := by simpa using hp
    simp [hf]

end Dom
