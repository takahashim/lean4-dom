import Url.Punycode
import Url.Host

/-!
# UTS #46 の ToASCII

URL Standard §3.2 の domain parser が委ねている Unicode の ToASCII。

## 表は持たない

UTS #46 の振る舞いは **写像表という規定データ**で決まっていて、規則から導けない。
そこで表そのものは持たず、**表が満たすべき性質だけ**を `IdnaTable` として述べ、
アルゴリズムをそれに対して相対的に定義する。実際の表は実行時に外から与える
（`test/url/uts46-table.json`)。

証明は表のデータに依存しない。「どんな表に対しても」の形になる。

## 扱わない部分は拒む

NFC 正規化・CheckBidi・CheckJoiners は、さらに別の表
（結合クラス・Bidi_Class・Joining_Type・NFC_QC）が要る。
この model はそれらを扱わないので、**効きうる code point が入っていたら拒む**。
黙って飛ばすと間違った答えを返すことになる。

`Dom/Basic/Utf16.lean` の `outsideModel` と同じ考え方で、
「仕様が禁じている」ではなく「model の対象外である」という印である。
-/

namespace Url

open Infra

/-- UTS #46 の写像表が code point に与える状態。 -/
inductive IdnaStatus where
  /-- そのまま使える。 -/
  | valid
  /-- 落とす。 -/
  | ignored
  /-- 別の列に写す。 -/
  | mapped
  /-- domain に使えない。 -/
  | disallowed
deriving DecidableEq, Repr, Inhabited

/--
写像表の interface。

`deviation` は `Transitional_Processing = false` で valid になるので `valid` に畳んである
（URL Standard がそう呼ぶ）。`disallowed_STD3_*` も `UseSTD3ASCIIRules = false` で
valid / mapped になるので畳んである。forbidden domain code point の検査は
domain parser の側にあって、ToASCII の後に走る。
-/
structure IdnaTable where
  status : Char → IdnaStatus
  mapped : Char → List Char
  /-- NFC・CheckBidi・CheckJoiners が効きうる code point。この model の対象外。 -/
  outOfModel : Char → Bool

/--
表が満たすべき性質。**写像先は valid な code point だけからなる。**

UTS #46 の表が保証している性質で、**一度写せば終わる**ことがここから出る。
構造体に埋めずに述語として置いてあるのは、実行時に読んだ表にも
そのまま定理を当てられるようにするためである（実行時はこの性質を検査する）。
-/
def IdnaTable.Resolved (t : IdnaTable) : Prop :=
  ∀ c, t.status c = .mapped → ∀ d ∈ t.mapped c, t.status d = .valid

/-- UTS #46 の写像段。`disallowed` があれば失敗、`ignored` は落とす。 -/
def mapAll (t : IdnaTable) : List Char → Option (List Char)
  | [] => some []
  | c :: rest =>
    match t.status c with
    | .disallowed => none
    | .ignored => mapAll t rest
    | .mapped => (mapAll t rest).map (t.mapped c ++ ·)
    | .valid => (mapAll t rest).map (c :: ·)

/-- 写像の結果に現れる code point はすべて valid である。 -/
theorem mapAll_valid (t : IdnaTable) (hres : t.Resolved) :
    ∀ (l l' : List Char), mapAll t l = some l' → ∀ c ∈ l', t.status c = .valid
  | [], l', h, c, hc => by rw [← Option.some.inj h] at hc; simp at hc
  | x :: rest, l', h, c, hc => by
    rw [mapAll] at h
    split at h
    · simp at h
    · exact mapAll_valid t hres rest l' h c hc
    · next hst =>
      cases hm : mapAll t rest with
      | none => rw [hm] at h; simp at h
      | some w =>
        rw [hm] at h
        simp only [Option.map_some] at h
        rw [← Option.some.inj h] at hc
        rcases List.mem_append.mp hc with hx | hx
        · exact hres x hst c hx
        · exact mapAll_valid t hres rest w hm c hx
    · next hst =>
      cases hm : mapAll t rest with
      | none => rw [hm] at h; simp at h
      | some w =>
        rw [hm] at h
        simp only [Option.map_some] at h
        rw [← Option.some.inj h] at hc
        rcases List.mem_cons.mp hc with hx | hx
        · rw [hx]; exact hst
        · exact mapAll_valid t hres rest w hm c hx

/-- **写像は一度で終わる。** 写した結果をもう一度写しても変わらない。 -/
theorem mapAll_idempotent (t : IdnaTable) (hres : t.Resolved) :
    ∀ (l l' : List Char), mapAll t l = some l' → mapAll t l' = some l' := by
  intro l l' h
  have hv := mapAll_valid t hres l l' h
  clear h
  induction l' with
  | nil => rfl
  | cons c rest ih =>
    rw [mapAll, hv c List.mem_cons_self, ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))]
    rfl

/-- label 一つを ASCII に直す。 -/
def labelToASCII (t : IdnaTable) (label : List Char) : Option (List Char) :=
  if label.all (fun c => c.toNat < 0x80) then
    -- 既に ASCII。`xn--` なら中身を復号して確かめる。
    match label with
    | 'x' :: 'n' :: '-' :: '-' :: rest =>
      match Punycode.decode rest with
      | none => none
      | some decoded => if decoded.any t.outOfModel then none else some label
    | _ => some label
  else some ("xn--".toList ++ Punycode.encode label)

/--
UTS #46 の ToASCII。この model の対象外なら `none`。

`CheckHyphens = false`、`VerifyDnsLength = false`（URL Standard が beStrict = false で呼ぶ）。
長さの検査と forbidden domain code point の検査は domain parser の側にある。
-/
def toASCII (t : IdnaTable) (domain : List Char) : Option String :=
  if domain.any t.outOfModel then none
  else
    match mapAll t domain with
    | none => none
    | some m =>
      if m.any t.outOfModel then none
      else
        match (strictSplit m '.').mapM (labelToASCII t) with
        | none => none
        | some ls =>
          -- domain parser の step 4-5。空と forbidden domain code point を弾く。
          -- 仕様ではこれは ToASCII の外（domain parser）の仕事だが、
          -- `asciiDomainToASCII` も同じ検査を持っているので、hook の約束として揃えてある。
          -- 同じ関数を呼ぶことで、二つの実装が同じ約束を果たすことが形から分かる。
          asciiDomainToASCII.asciiDomainCheck
            (String.intercalate "." (ls.map String.ofList))

/-! ## 性質 -/

theorem labelToASCII_ascii (t : IdnaTable) : ∀ (label l : List Char),
    labelToASCII t label = some l → ∀ c ∈ l, c.toNat < 0x80 := by
  intro label l h c hc
  unfold labelToASCII at h
  split at h
  · next hall =>
    split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rw [← Option.some.inj h] at hc
          exact of_decide_eq_true (List.all_eq_true.mp hall c hc)
    · rw [← Option.some.inj h] at hc
      exact of_decide_eq_true (List.all_eq_true.mp hall c hc)
  · rw [← Option.some.inj h] at hc
    rcases List.mem_append.mp hc with hx | hx
    · have hm : c = 'x' ∨ c = 'n' ∨ c = '-' ∨ c = '-' := by simpa using hx
      rcases hm with h | h | h | h <;> subst h <;> decide
    · exact Punycode.encode_ascii label c hx

theorem asciiDomainCheck_ne_empty {r s : String}
    (h : asciiDomainToASCII.asciiDomainCheck r = some s) : s.isEmpty = false := by
  unfold asciiDomainToASCII.asciiDomainCheck at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next he _ => rw [← Option.some.inj h]; simpa using he

theorem asciiDomainCheck_no_forbidden {r s : String}
    (h : asciiDomainToASCII.asciiDomainCheck r = some s) : s.any isForbiddenDomain = false := by
  unfold asciiDomainToASCII.asciiDomainCheck at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next _ hf => rw [← Option.some.inj h]; simpa using hf

/--
`toASCII` の結果は空でない。`asciiDomainToASCII_ne_empty` と同じ約束である。
-/
theorem toASCII_ne_empty (t : IdnaTable) {domain : List Char} {s : String}
    (h : toASCII t domain = some s) : s.isEmpty = false := by
  unfold toASCII at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact asciiDomainCheck_ne_empty h

/--
`toASCII` の結果に forbidden domain code point は無い。
`asciiDomainToASCII_no_forbidden` と同じ約束である。
-/
theorem toASCII_no_forbidden (t : IdnaTable) {domain : List Char} {s : String}
    (h : toASCII t domain = some s) : s.any isForbiddenDomain = false := by
  unfold toASCII at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact asciiDomainCheck_no_forbidden h

/-! ## 実行時に読む表 -/

/-- JSON から読んだ一区間。 -/
structure IdnaRange where
  lo : Nat
  hi : Nat
  status : IdnaStatus
  oom : Bool
  mapping : List Nat
deriving Repr, Inhabited

/-- 区間を二分探索で引く。区間は昇順で重なりがない前提。 -/
def findRange (rs : Array IdnaRange) (n : Nat) : Option IdnaRange :=
  go 0 rs.size
where
  go (lo hi : Nat) : Option IdnaRange :=
    if _h : lo < hi then
      let mid := (lo + hi) / 2
      match rs[mid]? with
      | none => none
      | some r =>
        if n < r.lo then go lo mid
        else if r.hi < n then go (mid + 1) hi
        else some r
    else none
  termination_by hi - lo
  decreasing_by
    · omega
    · omega

/-- 区間の列から表を作る。引けない code point は disallowed かつ対象外とする。 -/
def tableOfRanges (rs : Array IdnaRange) : IdnaTable where
  status := fun c => match findRange rs c.toNat with | some r => r.status | none => .disallowed
  mapped := fun c =>
    match findRange rs c.toNat with | some r => r.mapping.map Char.ofNat | none => []
  outOfModel := fun c => match findRange rs c.toNat with | some r => r.oom | none => true

/--
`Resolved` を区間の上で検査する。

写像先の code point がすべて valid かを見る。`Resolved` は `Char` 全体についての
命題だが、写像先は有限個なのでこれで足りる。
-/
def checkResolved (rs : Array IdnaRange) : Bool :=
  rs.all fun r =>
    r.status != .mapped || r.mapping.all fun d =>
      match findRange rs d with | some r' => r'.status == .valid | none => false

end Url
