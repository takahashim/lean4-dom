import Url.Roundtrip.Assemble

/-!
# port の往復
-/

namespace Url

open Infra

/-! ## port

10 進で書いた port を読み直すところ。`portValue_toString` が数の往復を言う。
-/

/-- 10 進の畳み込みは、初期値を桁数ぶん持ち上げる。 -/
theorem portFold_acc : ∀ (l : List Char) (a : Nat),
    l.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) a
      = a * 10 ^ l.length + l.foldl (fun acc c => acc * 10 + (digitValue c).getD 0) 0
  | [], a => by simp
  | c :: rest, a => by
    show rest.foldl _ (a * 10 + (digitValue c).getD 0) = _
    rw [portFold_acc rest (a * 10 + (digitValue c).getD 0)]
    show _ = a * 10 ^ (rest.length + 1) + rest.foldl _ (0 * 10 + (digitValue c).getD 0)
    rw [portFold_acc rest (0 * 10 + (digitValue c).getD 0)]
    rw [Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm 10 (10 ^ rest.length), ← Nat.mul_assoc]
    omega

/-- 連結した 10 進の値。 -/
theorem portValue_append (l1 l2 : List Char) :
    portValue (l1 ++ l2) = portValue l1 * 10 ^ l2.length + portValue l2 := by
  unfold portValue
  rw [List.foldl_append, portFold_acc l2 (l1.foldl _ 0)]

/-- `digitChar` の逆。 -/
theorem digitValue_digitChar : ∀ (d : Nat), d < 10 → digitValue (Nat.digitChar d) = some d
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

/-- `Nat.toDigitsCore` が積む桁の値。 -/
theorem portValue_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char), n < fuel →
    portValue (Nat.toDigitsCore 10 fuel n ds) = n * 10 ^ ds.length + portValue ds := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; exact absurd h (by omega)
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    have hd : digitValue (Nat.digitChar (n % 10)) = some (n % 10) :=
      digitValue_digitChar _ (by omega)
    have hcons : portValue (Nat.digitChar (n % 10) :: ds)
        = (n % 10) * 10 ^ ds.length + portValue ds := by
      rw [show (Nat.digitChar (n % 10) :: ds) = [Nat.digitChar (n % 10)] ++ ds from rfl,
        portValue_append]
      simp [portValue, hd]
    split
    · next hz =>
      have h10 : n % 10 = n := by omega
      rw [hcons, h10]
    · next hz =>
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega)]
      rw [hcons]
      simp only [List.length_cons, Nat.pow_succ]
      have hn : n / 10 * (10 ^ ds.length * 10) = (n / 10 * 10) * 10 ^ ds.length := by
        rw [Nat.mul_comm (10 ^ ds.length) 10, ← Nat.mul_assoc]
      rw [hn, ← Nat.add_assoc, ← Nat.add_mul]
      have : n / 10 * 10 + n % 10 = n := by omega
      rw [this]

/-- **10 進で書いた数は、読み直すと元に戻る。** -/
theorem portValue_toString (n : Nat) : portValue (toString n).toList = n := by
  show portValue (Nat.repr n).toList = n
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, portValue_toDigitsCore (n + 1) n [] (by omega)]
  simp [portValue]

/-- `digitChar` が返すのは ASCII digit である。 -/
theorem isAsciiDigit_digitChar : ∀ (d : Nat), d < 10 → isAsciiDigit (Nat.digitChar d) = true
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

/-- `Nat.toDigitsCore` が積むのは digit だけである。 -/
theorem toDigitsCore_digits : ∀ (fuel n : Nat) (ds : List Char),
    (∀ c ∈ ds, isAsciiDigit c = true) →
    ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, isAsciiDigit c = true := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; simpa [Nat.toDigitsCore] using h
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    have hd : isAsciiDigit (Nat.digitChar (n % 10)) = true :=
      isAsciiDigit_digitChar _ (by omega)
    split
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact h c hc
    · refine ih (n / 10) (Nat.digitChar (n % 10) :: ds) ?_
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hd
      · exact h c hc

/-- `Nat.toDigitsCore` は積むだけなので、空にはならない。 -/
theorem toDigitsCore_ne_nil : ∀ (fuel n : Nat) (ds : List Char), ds ≠ [] →
    Nat.toDigitsCore 10 fuel n ds ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro n ds h; simpa [Nat.toDigitsCore] using h
  | succ f ih =>
    intro n ds h
    rw [Nat.toDigitsCore]
    split
    · simp
    · exact ih (n / 10) _ (by simp)

/-- 10 進で書いた数は空でない。 -/
theorem toString_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  show (Nat.repr n).toList ≠ []
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, Nat.toDigitsCore]
  split
  · simp
  · exact toDigitsCore_ne_nil _ _ _ (by simp)

/-- **10 進で書いた数は digit だけからなる。** -/
theorem toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, isAsciiDigit c = true := by
  show ∀ c ∈ (Nat.repr n).toList, isAsciiDigit c = true
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList]
  exact toDigitsCore_digits (n + 1) n [] (by simp)

/-- host state の `:`。host を確定させて port state へ移る。 -/
theorem run_host_port (base : Option Url) (sp : Bool) (rest : List Char) (ctx : PCtx) (hst : Host)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp) (hib : ctx.insideBrackets = false)
    (hne : ctx.buffer ≠ [])
    (hp : hostParser ctx.toAscii ctx.buffer (!sp) = some hst) :
    run base .host (':' :: rest) ctx
      = run base .port rest
          { ctx with url := { ctx.url with host := some hst }, buffer := [] } := by
  rw [run, step]
  rw [if_neg (by simp [hov])]
  rw [if_pos (by simp [hib])]
  rw [if_neg (by simpa using hne)]
  rw [if_neg (by simp [hov])]
  simp only [hsp, hp]

/-- port state が digit を読み切る。 -/
theorem run_port_chunk (base : Option Url) (sp : Bool) : ∀ (l tail : List Char) (ctx : PCtx),
    ctx.url.isSpecial = sp → (∀ c ∈ l, isAsciiDigit c = true) →
    run base .port (l ++ tail) ctx
      = run base .port tail { ctx with buffer := ctx.buffer ++ l } := by
  intro l
  induction l with
  | nil => intro tail ctx _ _; simp
  | cons c l' ih =>
    intro tail ctx hsp h
    simp only [List.cons_append]
    rw [run, step, if_pos (h c (by simp))]
    rw [ih tail { ctx with buffer := ctx.buffer ++ [c] } hsp (fun x hx => h x (by simp [hx]))]
    simp

/-- port state の区切り。buffer を 10 進として読んで path start state へ移る。 -/
theorem run_port_pathStart (base : Option Url) (sp : Bool) (tail : List Char) (ctx : PCtx)
    (hov : ctx.over = none) (hsp : ctx.url.isSpecial = sp)
    (hne : ctx.buffer ≠ []) (hle : portValue ctx.buffer ≤ 65535)
    (ht : ∀ c ∈ tail.head?, isTerminator sp (some c) = true) :
    run base .port tail ctx
      = run base .pathStart tail
          (portSet ctx (portOf ctx.url.scheme (portValue ctx.buffer))) := by
  cases tail with
  | nil =>
    rw [run, step]
    rw [portDone_digits hne hle]
    simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]
  | cons t ts =>
    have htt := ht t rfl
    rw [run, step]
    rw [if_neg (by
      intro hd
      have ht2 : isTerminator sp (some t) = true := htt
      simp only [isTerminator, Bool.or_eq_true, beq_iff_eq] at ht2
      rcases ht2 with ((h | h) | h) | h
      · rw [h] at hd; revert hd; decide
      · rw [h] at hd; revert hd; decide
      · rw [h] at hd; revert hd; decide
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2] at hd; revert hd; decide)]
    rw [if_pos (by simp [hsp, htt])]
    rw [portDone_digits hne hle]
    simp only [hov, Option.isSome_none, Bool.false_eq_true, if_false]

end Url
