import Url.Idna
import Url.HostRoundtrip

/-!
# UTS #46 の表を渡した ToASCII も往復の条件を満たす

`Url/HostRoundtrip.lean` の `ToAsciiOk` は、host parser の出力が serialize して読み直すと戻るために
ToASCII に求める三つの条件である（出力は空でない ASCII で forbidden domain code point を含まない、
冪等、IPv4 の列を素通しする）。既定の `asciiDomainToASCII` は `toAsciiOk_ascii` で満たす。
ここでは表を渡した `toASCII t` も満たすことを示す。

ASCII だけの入力は `toASCII` が `asciiDomainToASCII` に委ねている（`Url/Idna.lean`）。
したがって IPv4 の列はそのまま返り、冪等性は「出力が小文字の ASCII である」ことに帰着する。
出力の label は、ASCII なら写像の結果（valid な code point）そのもので、そうでなければ `xn--` と
Punycode の符号化である。Punycode が書く桁は小文字なので、残るのは
**ASCII の大文字が表で valid でないこと**（`NoUpperValid`）だけである。
UTS #46 の表では ASCII の大文字は `mapped` なので成り立つ。表は実行時に読むので、
`Resolved` と同じく実行時に検査し（`checkNoUpperValid`）、その検査が健全であることを示す。
-/

namespace Url

open Infra

/-! ## Punycode の出力の文字 -/

namespace Punycode

/-- `encodeDigits` が書く文字は桁の文字である。 -/
theorem encodeDigits_chars (P : Char → Prop) (hP : ∀ d, d < 36 → P (digitChar d)) (bias : Nat) :
    ∀ (k q : Nat) (c : Char), c ∈ encodeDigits bias k q → P c
  | k, q, c, hc => by
    rw [encodeDigits] at hc
    have h1 := threshold_pos k bias
    have h2 := threshold_le k bias
    split at hc
    · next hq =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; exact hP _ (by omega)
    · next hq =>
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc
        refine hP _ ?_
        have : (q - threshold k bias) % (36 - threshold k bias) < 36 - threshold k bias :=
          Nat.mod_lt _ (by omega)
        omega
      · exact encodeDigits_chars P hP bias (k + 36) _ c hc
termination_by _ q => q
decreasing_by
  have _h1 := threshold_pos k bias
  have _h2 := threshold_le k bias
  calc (q - threshold k bias) / (36 - threshold k bias)
      ≤ q - threshold k bias := Nat.div_le_self _ _
    _ < q := by omega

theorem scanOne_chars (P : Char → Prop) (hP : ∀ d, d < 36 → P (digitChar d)) (b m : Nat)
    (st : EncState) (c : Char) (h : ∀ x ∈ st.out, P x) : ∀ x ∈ (scanOne b m st c).out, P x := by
  unfold scanOne
  split
  · exact h
  · split
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · exact encodeDigits_chars P hP st.bias 36 st.delta x hx
    · exact h

theorem scanFold_chars (P : Char → Prop) (hP : ∀ d, d < 36 → P (digitChar d)) (b m : Nat) :
    ∀ (l : List Char) (st : EncState),
    (∀ x ∈ st.out, P x) → ∀ x ∈ (l.foldl (scanOne b m) st).out, P x
  | [], _, h => h
  | c :: rest, st, h =>
    scanFold_chars P hP b m rest (scanOne b m st c) (scanOne_chars P hP b m st c h)

theorem encodeLoop_chars (P : Char → Prop) (hP : ∀ d, d < 36 → P (digitChar d))
    (input : List Char) (b : Nat) : ∀ (todo : List Nat) (n : Nat)
    (st : EncState), (∀ x ∈ st.out, P x) → ∀ x ∈ (encodeLoop input b todo n st).out, P x
  | [], _, _, h => h
  | m :: rest, n, st, h => by
    rw [encodeLoop]
    refine encodeLoop_chars P hP input b rest (m + 1) _ ?_
    exact scanFold_chars P hP b m input _ h

/--
**符号化の出力の文字は、入力の ASCII の文字か、区切りの `-` か、桁の文字である。**

`encode_ascii` を性質 `P` について一般にしたもの。
-/
theorem encode_chars (P : Char → Prop) (hP : ∀ d, d < 36 → P (digitChar d)) (hdash : P '-')
    (input : List Char) (hin : ∀ c ∈ input, c.toNat < 0x80 → P c) :
    ∀ c ∈ encode input, P c := by
  intro c hc
  unfold encode at hc
  rcases List.mem_append.mp hc with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · have hm := List.mem_filter.mp hx
      exact hin c hm.1 (by simpa using hm.2)
    · split at hx
      · simp at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; exact hdash
  · exact encodeLoop_chars P hP input _ _ _ _ (by simp) c hx

/-- 桁の文字は小文字である。 -/
theorem digitChar_lower {d : Nat} (h : d < 36) : asciiLowerChar (digitChar d) = digitChar d := by
  have hall : ∀ e ∈ List.range 36, asciiLowerChar (digitChar e) = digitChar e := by decide
  exact hall d (List.mem_range.mpr h)

end Punycode

/-! ## 表の性質 -/

/-- **ASCII の大文字は valid でない。** UTS #46 の表では `mapped`（小文字へ写す）である。 -/
def IdnaTable.NoUpperValid (t : IdnaTable) : Prop :=
  ∀ c, isAsciiUpperAlpha c = true → t.status c ≠ .valid

/-- 大文字でなければ小文字にしても変わらない。 -/
theorem asciiLowerChar_of_not_upper {c : Char} (h : isAsciiUpperAlpha c = false) :
    asciiLowerChar c = c := by
  unfold asciiLowerChar; rw [if_neg (by simp [h])]

/-- valid な code point は小文字にしても変わらない。 -/
theorem lower_of_valid {t : IdnaTable} (hup : t.NoUpperValid) {c : Char}
    (h : t.status c = .valid) : asciiLowerChar c = c := by
  cases hu : isAsciiUpperAlpha c with
  | false => exact asciiLowerChar_of_not_upper hu
  | true => exact absurd h (hup c hu)

/-- `NoUpperValid` を区間の上で検査する。ASCII の大文字は 26 個しかない。 -/
def checkNoUpperValid (rs : Array IdnaRange) : Bool :=
  (List.range 26).all fun i => (tableOfRanges rs).status (Char.ofNat (0x41 + i)) != .valid

/-- **実行時の検査が `NoUpperValid` を落とす。** -/
theorem checkNoUpperValid_sound {rs : Array IdnaRange} (h : checkNoUpperValid rs = true) :
    (tableOfRanges rs).NoUpperValid := by
  intro c hc
  simp only [isAsciiUpperAlpha, Bool.and_eq_true, decide_eq_true_eq] at hc
  unfold checkNoUpperValid at h
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  have := h (c.toNat - 0x41) (by omega)
  rwa [show 0x41 + (c.toNat - 0x41) = c.toNat by omega, Char.ofNat_toNat] at this

/-! ## label と domain -/

/-- strict split の各項の文字は、元の列の文字である。 -/
theorem strictSplit_go_mem (sep : Char) : ∀ (l acc : List Char),
    ∀ lab ∈ strictSplit.go sep l acc, ∀ c ∈ lab, c ∈ l ∨ c ∈ acc
  | [], acc, lab, hl, c, hc => by
    simp only [strictSplit.go, List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    exact Or.inr (List.mem_reverse.mp hc)
  | x :: rest, acc, lab, hl, c, hc => by
    simp only [strictSplit.go] at hl
    split at hl
    · rcases List.mem_cons.mp hl with hl | hl
      · subst hl; exact Or.inr (List.mem_reverse.mp hc)
      · rcases strictSplit_go_mem sep rest [] lab hl c hc with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · simp at h
    · rcases strictSplit_go_mem sep rest (x :: acc) lab hl c hc with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact Or.inl List.mem_cons_self
        · exact Or.inr h

theorem strictSplit_mem {l : List Char} {sep : Char} :
    ∀ lab ∈ strictSplit l sep, ∀ c ∈ lab, c ∈ l := by
  intro lab hl c hc
  rcases strictSplit_go_mem sep l [] lab hl c hc with h | h
  · exact h
  · simp at h

/-- `mapM` の結果の各項は、元の列のどれかを写したものである。 -/
theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp at hy
  | x :: rest, l', h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some b =>
      rw [hx] at h
      cases hr : rest.mapM f with
      | none => rw [hr] at h; simp at h
      | some w =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with hy | hy
        · subst hy; exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨z, hz, hfz⟩ := mapM_some_mem hr y hy
          exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

/-- `List.intercalate` の文字は、区切りの文字か、どれかの項の文字である。 -/
theorem mem_intercalate {sep : List Char} :
    ∀ {ls : List (List Char)} {c : Char}, c ∈ sep.intercalate ls → c ∈ sep ∨ ∃ l ∈ ls, c ∈ l
  | [], c, h => by simp at h
  | [a], c, h => by simp at h; exact Or.inr ⟨a, by simp, h⟩
  | a :: b :: rest, c, h => by
    rw [List.intercalate_cons_cons] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inl h
    · rcases mem_intercalate h with h | ⟨l, hl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, h⟩

/-- `asciiDomainCheck` は検査するだけで、通れば同じ文字列を返す。 -/
theorem asciiDomainCheck_eq {r s : String}
    (h : asciiDomainToASCII.asciiDomainCheck r = some s) : s = r := by
  unfold asciiDomainToASCII.asciiDomainCheck at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact (Option.some.inj h).symm

/--
**label を ASCII に直した結果は小文字である。** 元の label の文字が valid なら。

ASCII の label はそのまま返るので元の文字が、そうでなければ `xn--` と Punycode の桁が出る。
`xn--` の label を復号し直した場合も、復号した中身が valid であることを確かめてから符号化し直す。
-/
theorem labelToASCII_lower (t : IdnaTable) (hup : t.NoUpperValid) {label l : List Char}
    (hv : ∀ c ∈ label, t.status c = .valid) (h : labelToASCII t label = some l) :
    ∀ c ∈ l, asciiLowerChar c = c := by
  have hpfx : ∀ (d : List Char), (∀ c ∈ d, c.toNat < 0x80 → asciiLowerChar c = c) →
      ∀ c ∈ "xn--".toList ++ Punycode.encode d, asciiLowerChar c = c := by
    intro d hd c hc
    rcases List.mem_append.mp hc with hx | hx
    · have hm : c = 'x' ∨ c = 'n' ∨ c = '-' ∨ c = '-' := by simpa using hx
      rcases hm with h | h | h | h <;> subst h <;> decide
    · exact Punycode.encode_chars (fun c => asciiLowerChar c = c)
        (fun _ hd => Punycode.digitChar_lower hd) (by decide) d hd c hx
  unfold labelToASCII at h
  split at h
  · split at h
    · split at h
      · simp at h
      · next decoded _ =>
        split at h
        · next hval =>
          split at h
          · rw [← Option.some.inj h]
            exact fun c hc => lower_of_valid hup (hv c hc)
          · rw [← Option.some.inj h]
            refine hpfx decoded fun c hc _ => lower_of_valid hup ?_
            simp only [validALabel, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hval
            exact hval.1 c hc
        · simp at h
    · rw [← Option.some.inj h]
      exact fun c hc => lower_of_valid hup (hv c hc)
  · rw [← Option.some.inj h]
    exact hpfx label fun c hc _ => lower_of_valid hup (hv c hc)

/-- **`toASCII` の出力は小文字の ASCII である。** -/
theorem toASCII_lower_ascii (t : IdnaTable) (hres : t.Resolved) (hup : t.NoUpperValid)
    {domain : List Char} {s : String} (h : toASCII t domain = some s) :
    ∀ c ∈ s.toList, isAscii c = true ∧ asciiLowerChar c = c := by
  unfold toASCII at h
  split at h
  · intro c hc
    have := (asciiDomainToASCII_out h).2 c hc
    exact ⟨this.1, this.2.1⟩
  · split at h
    · simp at h
    · split at h
      · simp at h
      · next m hm =>
        split at h
        · simp at h
        · split at h
          · simp at h
          · next ls hls =>
            have heq := asciiDomainCheck_eq h
            intro c hc
            rw [heq, String.toList_intercalate, List.map_map] at hc
            rcases mem_intercalate hc with hc | ⟨l, hl, hc⟩
            · have hd : c = '.' := by simpa using hc
              subst hd; exact ⟨by decide, by decide⟩
            · simp only [List.mem_map, Function.comp_apply, String.toList_ofList] at hl
              obtain ⟨l', hl', rfl⟩ := hl
              obtain ⟨lab, hlab, hlt⟩ := mapM_some_mem hls l' hl'
              have hv : ∀ x ∈ lab, t.status x = .valid := fun x hx =>
                mapAll_valid t hres _ m hm x (strictSplit_mem lab hlab x hx)
              refine ⟨?_, labelToASCII_lower t hup hv hlt c hc⟩
              have := labelToASCII_ascii t lab l' hlt c hc
              simp only [isAscii, decide_eq_true_eq]
              omega

/-- `toASCII` の出力は空でない。 -/
theorem toASCII_toList_ne_nil (t : IdnaTable) {x : List Char} {a : String}
    (h : toASCII t x = some a) : ¬a.toList = [] := by
  have he := toASCII_ne_empty t h
  intro hx
  have ha : a = "" := String.toList_inj.mp (by rw [hx]; rfl)
  rw [ha] at he
  cases he

/-- `toASCII` の出力の文字は forbidden domain code point でない。 -/
theorem toASCII_char_no_forbidden (t : IdnaTable) {x : List Char} {a : String}
    (h : toASCII t x = some a) : ∀ c ∈ a.toList, isForbiddenDomain c = false := by
  have hnf := toASCII_no_forbidden t h
  simp [String.any] at hnf
  intro c hc
  simpa using hnf c hc

/-- **表を渡した `toASCII` も往復の条件を満たす。** 表が `Resolved` と `NoUpperValid` を満たせば。 -/
theorem toAsciiOk_table (t : IdnaTable) (hres : t.Resolved) (hup : t.NoUpperValid) :
    ToAsciiOk (toASCII t) where
  out x a h := ⟨toASCII_toList_ne_nil t h, fun c hc =>
    ⟨(toASCII_lower_ascii t hres hup h c hc).1, toASCII_char_no_forbidden t h c hc⟩⟩
  idem x a h := by
    have hla := toASCII_lower_ascii t hres hup h
    have hfd := toASCII_char_no_forbidden t h
    unfold toASCII
    rw [if_pos (by
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro c hc
      have := (hla c hc).1
      simp only [isAscii, decide_eq_true_eq] at this
      omega)]
    rw [asciiDomainToASCII_id (toASCII_toList_ne_nil t h)
      (fun c hc => ⟨(hla c hc).1, (hla c hc).2, hfd c hc⟩), String.ofList_toList]
  ipv4 addr := by
    unfold toASCII
    rw [if_pos (by
      simp only [List.all_eq_true, decide_eq_true_eq]
      exact fun c hc => (ipv4Serializer_char_facts hc).1)]
    exact asciiDomainToASCII_ipv4 addr

/-- **実行時の二つの検査が通れば、読み込んだ表の `toASCII` は往復の条件を満たす。** -/
theorem toAsciiOk_ranges {rs : Array IdnaRange} (h1 : checkResolved rs = true)
    (h2 : checkNoUpperValid rs = true) : ToAsciiOk (toASCII (tableOfRanges rs)) :=
  toAsciiOk_table _ (checkResolved_sound h1) (checkNoUpperValid_sound h2)

end Url
