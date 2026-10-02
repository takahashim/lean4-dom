import Url.UrlencodedRoundtrip

/-!
# application/x-www-form-urlencoded parser の関係仕様（§5.1）

`parseUrlencoded`（`Url/Urlencoded.lean`）は、byte 列を `&` で切り、各片を最初の `=` で分ける。
切り分けは accumulator を持った走査（`splitAmp.go`、`splitFirstEq.go`）で書いてある。

ここでは同じものを、走査を写さずに**分け方の条件**として書く。

* step 1「`&` で strictly split する」：片を `&` を挟んで並べると入力に戻り、どの片にも `&` が無い
  （`SplitOnAmp`）。
* step 3.2-3.3「最初の `=` の前と後」：片は「`=` を含まない name、`=`、value」と並ぶ。
  `=` が無ければ name は片全体、value は空（`NameValue`）。
* step 3.1 と 3.4-3.6：空の片は飛ばし、`+` を空白に直して percent-decode し、UTF-8 として読む
  （`FormTuples`）。

`parseUrlencoded_iff` が、parser の出力はこの関係を満たすものにちょうど一致する、と言う。
`&` と `=` での分け方は一通りしかないので（`splitAmp_unique`、`splitFirstEq_unique`）、
関係は決定的で、parser はそれを計算している。

関係は `splitAmp` / `splitFirstEq` / `plusToSpace` / `parsePiece` / `parseUrlencoded` を呼ばない。
共有するのは §1.3 の `percentDecodeBytes` と Encoding Standard の `utf8DecodeString` だけである。
-/

namespace Url.Spec

open Infra

/-- 片を区切りの byte を挟んで並べる。§5.1 step 1 の split の逆である。 -/
def joinOn (sep : UInt8) : List Bytes → Bytes
  | [] => []
  | p :: ps => p ++ ps.flatMap (fun x => sep :: x)

/--
§5.1 step 1：入力を 0x26（`&`）で strictly split した結果が `pieces` である。

strictly split は区切りの数より一つ多い片を返すので、片の列は空でない。
-/
def SplitOnAmp (input : Bytes) (pieces : List Bytes) : Prop :=
  pieces ≠ [] ∧ joinOn (UInt8.ofNat 0x26) pieces = input ∧ ∀ p ∈ pieces, ∀ b ∈ p, b.toNat ≠ 0x26

/--
§5.1 step 3.2-3.3：片 `bytes` の name と value。

`=` を含むなら、name は最初の `=` より前、value はその後ろ全部。含まなければ name は片全体で、
value は空。「最初の」は「name に `=` が無い」と言えば足りる。
-/
def NameValue (bytes name value : Bytes) : Prop :=
  (bytes = name ++ UInt8.ofNat 0x3D :: value ∧ ∀ b ∈ name, b.toNat ≠ 0x3D) ∨
  ((∀ b ∈ bytes, b.toNat ≠ 0x3D) ∧ name = bytes ∧ value = [])

/-- §5.1 step 3.4-3.5：`+` を空白に直し、percent-decode して UTF-8 として読む。 -/
def decodeFormPart (x : Bytes) : String :=
  utf8DecodeString (percentDecodeBytes (x.map fun b => if b.toNat = 0x2B then UInt8.ofNat 0x20 else b))

/-- §5.1 step 3：片の列から name-value の組の列を作る。空の片は飛ばす（step 3.1）。 -/
inductive FormTuples : List Bytes → List (String × String) → Prop
  | nil : FormTuples [] []
  | skip {ps : List Bytes} {out : List (String × String)} :
      FormTuples ps out → FormTuples ([] :: ps) out
  | pair {bytes name value : Bytes} {ps : List Bytes} {out : List (String × String)} :
      bytes ≠ [] → NameValue bytes name value → FormTuples ps out →
      FormTuples (bytes :: ps) ((decodeFormPart name, decodeFormPart value) :: out)

/-- **§5.1 application/x-www-form-urlencoded parser の関係。** -/
def FormParses (input : Bytes) (out : List (String × String)) : Prop :=
  ∃ pieces, SplitOnAmp input pieces ∧ FormTuples pieces out

/-! ## `&` での分割 -/

/-- 走査は、積んだ accumulator と残りを並べ直したものを分ける。 -/
theorem splitAmp_go_spec : ∀ (l acc : Bytes), (∀ b ∈ acc, b.toNat ≠ 0x26) →
    splitAmp.go l acc ≠ [] ∧
      joinOn (UInt8.ofNat 0x26) (splitAmp.go l acc) = acc.reverse ++ l ∧
      ∀ p ∈ splitAmp.go l acc, ∀ b ∈ p, b.toNat ≠ 0x26
  | [], acc, h => by
    refine ⟨by simp [splitAmp.go], by simp [splitAmp.go, joinOn], ?_⟩
    intro p hp b hb
    simp only [splitAmp.go, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact h b (List.mem_reverse.mp hb)
  | x :: rest, acc, h => by
    simp only [splitAmp.go]
    split
    · next hx =>
      obtain ⟨hne, hj, hall⟩ := splitAmp_go_spec rest [] (by simp)
      refine ⟨by simp, ?_, ?_⟩
      · have hx' : x = UInt8.ofNat 0x26 := by
          have : x.toNat = 0x26 := by simpa using hx
          exact UInt8.toNat.inj (by simp [this])
        cases hg : splitAmp.go rest [] with
        | nil => exact absurd hg hne
        | cons q qs =>
          rw [hg] at hj
          simp only [joinOn, List.reverse_nil, List.nil_append] at hj ⊢
          rw [List.flatMap_cons, ← List.append_assoc, ← hj, hx']
          simp
      · intro p hp b hb
        rcases List.mem_cons.mp hp with hp | hp
        · subst hp; exact h b (List.mem_reverse.mp hb)
        · exact hall p hp b hb
    · next hx =>
      have hacc : ∀ b ∈ x :: acc, b.toNat ≠ 0x26 := by
        intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · subst hb; simpa using hx
        · exact h b hb
      obtain ⟨hne, hj, hall⟩ := splitAmp_go_spec rest (x :: acc) hacc
      exact ⟨hne, by rw [hj]; simp, hall⟩

/-- **parser の `&` での分割は step 1 を満たす。** -/
theorem splitAmp_spec (input : Bytes) : SplitOnAmp input (splitAmp input) := by
  show SplitOnAmp input (splitAmp.go input [])
  obtain ⟨hne, hj, hall⟩ := splitAmp_go_spec input [] (by simp)
  exact ⟨hne, by simpa using hj, hall⟩

/-- **`&` での分け方は一通りしかない。** -/
theorem splitAmp_unique {input : Bytes} {pieces : List Bytes} (h : SplitOnAmp input pieces) :
    splitAmp input = pieces := by
  obtain ⟨hne, hj, hall⟩ := h
  cases pieces with
  | nil => exact absurd rfl hne
  | cons p ps =>
    subst hj
    exact splitAmp_intercalate p ps (fun b hb => by simpa using hall p List.mem_cons_self b hb)
      (fun q hq b hb => by simpa using hall q (List.mem_cons_of_mem _ hq) b hb)

/-! ## 最初の `=` での分割 -/

theorem splitFirstEq_go_spec : ∀ (l acc : Bytes), (∀ b ∈ acc, b.toNat ≠ 0x3D) →
    NameValue (acc.reverse ++ l) (splitFirstEq.go l acc).1 (splitFirstEq.go l acc).2
  | [], acc, h => by
    right
    refine ⟨?_, by simp [splitFirstEq.go], by simp [splitFirstEq.go]⟩
    intro b hb
    exact h b (List.mem_reverse.mp (by simpa using hb))
  | x :: rest, acc, h => by
    simp only [splitFirstEq.go]
    split
    · next hx =>
      left
      have hx' : x = UInt8.ofNat 0x3D := by
        have : x.toNat = 0x3D := by simpa using hx
        exact UInt8.toNat.inj (by simp [this])
      exact ⟨by rw [hx'], fun b hb => h b (List.mem_reverse.mp hb)⟩
    · next hx =>
      have hacc : ∀ b ∈ x :: acc, b.toNat ≠ 0x3D := by
        intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · subst hb; simpa using hx
        · exact h b hb
      have := splitFirstEq_go_spec rest (x :: acc) hacc
      simpa using this

/-- **parser の `=` での分割は step 3.2-3.3 を満たす。** -/
theorem splitFirstEq_spec (bs : Bytes) :
    NameValue bs (splitFirstEq bs).1 (splitFirstEq bs).2 := by
  show NameValue bs (splitFirstEq.go bs []).1 (splitFirstEq.go bs []).2
  simpa using splitFirstEq_go_spec bs [] (by simp)

/-- `=` を含まない片は、name が片全体、value が空になる。 -/
theorem splitFirstEq_no_eq {bs : Bytes} (h : ∀ b ∈ bs, b.toNat ≠ 0x3D) :
    splitFirstEq bs = (bs, []) := by
  show splitFirstEq.go bs [] = _
  have := splitFirstEq_go_append bs (fun b hb => by simpa using h b hb) [] []
  rw [List.append_nil] at this
  rw [this]
  simp [splitFirstEq.go]

/-- **name と value の分け方は一通りしかない。** -/
theorem splitFirstEq_unique {bs name value : Bytes} (h : NameValue bs name value) :
    splitFirstEq bs = (name, value) := by
  rcases h with ⟨rfl, hn⟩ | ⟨hb, rfl, rfl⟩
  · exact splitFirstEq_append name value (fun b hb => by simpa using hn b hb)
  · exact splitFirstEq_no_eq hb

/-! ## 片の列 -/

theorem decodeFormPart_eq (x : Bytes) :
    decodeFormPart x = utf8DecodeString (percentDecodeBytes (plusToSpace x)) := by
  unfold decodeFormPart plusToSpace
  congr 2
  apply List.map_congr_left
  intro b _
  by_cases h : b.toNat = 0x2B <;> simp [h]

theorem formTuples_filterMap : ∀ (ps : List Bytes), FormTuples ps (ps.filterMap parsePiece)
  | [] => .nil
  | [] :: ps => by
    rw [List.filterMap_cons]
    exact .skip (formTuples_filterMap ps)
  | (b :: bs) :: ps => by
    rw [List.filterMap_cons]
    have hp : parsePiece (b :: bs) = some (decodeFormPart (splitFirstEq (b :: bs)).1,
        decodeFormPart (splitFirstEq (b :: bs)).2) := by
      simp [parsePiece, decodeFormPart_eq]
    rw [hp]
    exact .pair (by simp) (splitFirstEq_spec _) (formTuples_filterMap ps)

theorem formTuples_unique {ps : List Bytes} {out : List (String × String)}
    (h : FormTuples ps out) : out = ps.filterMap parsePiece := by
  induction h with
  | nil => rfl
  | skip _ ih => rw [List.filterMap_cons, ih]; rfl
  | @pair bytes name value ps out hne hnv _ ih =>
    rw [List.filterMap_cons, ← ih]
    have hp : parsePiece bytes = some (decodeFormPart name, decodeFormPart value) := by
      have hb : bytes.isEmpty = false := by
        cases bytes with
        | nil => exact absurd rfl hne
        | cons _ _ => rfl
      simp [parsePiece, hb, splitFirstEq_unique hnv, decodeFormPart_eq]
    rw [hp]

/-! ## 組み立て -/

theorem parseUrlencoded_eq (input : Bytes) :
    parseUrlencoded input = (splitAmp input).filterMap parsePiece := rfl

/-- **parser の出力は関係を満たす。** -/
theorem parseUrlencoded_spec (input : Bytes) : FormParses input (parseUrlencoded input) :=
  ⟨splitAmp input, splitAmp_spec input, by
    rw [parseUrlencoded_eq]; exact formTuples_filterMap _⟩

/--
**§5.1 の parser は関係をちょうど計算する。**

関係を満たす出力は parser の出力だけである。分け方が一通りしかないので、関係は決定的である。
-/
theorem parseUrlencoded_iff (input : Bytes) (out : List (String × String)) :
    FormParses input out ↔ parseUrlencoded input = out := by
  constructor
  · rintro ⟨pieces, hs, ht⟩
    rw [parseUrlencoded_eq, splitAmp_unique hs, formTuples_unique ht]
  · rintro rfl
    exact parseUrlencoded_spec input

/-- 関係は決定的である。 -/
theorem FormParses.deterministic {input : Bytes} {out out' : List (String × String)}
    (h : FormParses input out) (h' : FormParses input out') : out = out' := by
  rw [← (parseUrlencoded_iff input out).mp h, (parseUrlencoded_iff input out').mp h']

end Url.Spec
