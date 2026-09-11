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

/--
復号した A-label の中身を検査する。UTS #46 §4.1 の validity criteria のうち、
この model が持っている分である。

* どの code point も `valid` であること。**`mapped` や `ignored` や `disallowed`
  では駄目である。** A-label は写像を済ませた後の形でなければならない。
* 対象外の印が付いていないこと（正規化・Bidi・joiner が要る code point）。

空の label（`xn--` そのもの）は criteria の対象外なので素通りする。
非正規な綴りは拒否しない。Processing は label を復号した形に置き換え、
ToASCII が符号化し直すので、出力は自然に正準形になる。
-/
def validALabel (t : IdnaTable) (decoded : List Char) : Bool :=
  decoded.all (fun c => t.status c == .valid) && !decoded.any t.outOfModel

/-- label 一つを ASCII に直す。 -/
def labelToASCII (t : IdnaTable) (label : List Char) : Option (List Char) :=
  if label.all (fun c => c.toNat < 0x80) then
    -- 既に ASCII。`xn--` なら中身を復号して確かめる。
    match label with
    | 'x' :: 'n' :: '-' :: '-' :: rest =>
      match Punycode.decode rest with
      | none => none
      | some decoded =>
        if validALabel t decoded then
          -- 復号した形で criteria を満たしたので、符号化し直した正準形を返す。
          if decoded.isEmpty then some label
          else some ("xn--".toList ++ Punycode.encode decoded)
        else none
    | _ => some label
  else some ("xn--".toList ++ Punycode.encode label)

/--
UTS #46 の ToASCII。この model の対象外なら `none`。

`CheckHyphens = false`、`VerifyDnsLength = false`（URL Standard が beStrict = false で呼ぶ）。
長さの検査と forbidden domain code point の検査は domain parser の側にある。
-/
def toASCII (t : IdnaTable) (domain : List Char) : Option String :=
  -- URL Standard の domain parser step 2。
  -- **ASCII だけの domain は Unicode ToASCII の結果によらず lowercase して返す。**
  -- 仕様が web 互換のためにそう決めていて、`xn--8i7caa` を例に挙げている
  -- （`ｗｗｗ` に復号され、その code point の status は `mapped` である）。
  -- ここを通さないと、表を渡したときだけ ASCII の domain の扱いが変わってしまう。
  if domain.all (fun c => c.toNat < 0x80) then asciiDomainToASCII domain
  else if domain.any t.outOfModel then none
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
  -- `xn--` を付けた出力が ASCII であることは二箇所で要る。
  have hpfx : ∀ (d : List Char), (∀ x ∈ Punycode.encode d, x.toNat < 0x80) →
      c ∈ "xn--".toList ++ Punycode.encode d → c.toNat < 0x80 := by
    intro d hd hx
    rcases List.mem_append.mp hx with hx | hx
    · have hm : c = 'x' ∨ c = 'n' ∨ c = '-' ∨ c = '-' := by simpa using hx
      rcases hm with h | h | h | h <;> subst h <;> decide
    · exact hd c hx
  unfold labelToASCII at h
  split at h
  · next hall =>
    split at h
    · split at h
      · simp at h
      · next decoded _ =>
        split at h
        · split at h
          · rw [← Option.some.inj h] at hc
            exact of_decide_eq_true (List.all_eq_true.mp hall c hc)
          · rw [← Option.some.inj h] at hc
            exact hpfx decoded (Punycode.encode_ascii decoded) hc
        · simp at h
    · rw [← Option.some.inj h] at hc
      exact of_decide_eq_true (List.all_eq_true.mp hall c hc)
  · rw [← Option.some.inj h] at hc
    exact hpfx label (Punycode.encode_ascii label) hc

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
  · -- ASCII だけの domain は `asciiDomainToASCII` に委ねている。
    exact asciiDomainToASCII_ne_empty h
  · split at h
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
  · -- ASCII だけの domain は `asciiDomainToASCII` に委ねている。
    exact asciiDomainToASCII_no_forbidden h
  · split at h
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
      decide (Nat.isValidChar d) &&
        match findRange rs d with | some r' => r'.status == .valid | none => false

/-! ### 実行時の検査が仮定を落とすこと

`mapAll_valid` などは `IdnaTable.Resolved` を仮定して証明してある。
その仮定を実行時の `checkResolved` が落とすことを、ここで証明する。
これが無いと「仮定は実行時検査によって discharge される」という主張が
文書の上だけのものになる。
-/

/-- 二分探索が返す区間は、引いた配列の要素である。 -/
theorem findRange_go_mem (rs : Array IdnaRange) (n : Nat) :
    ∀ lo hi, ∀ r, findRange.go rs n lo hi = some r → ∃ i, ∃ hlt : i < rs.size, rs[i] = r := by
  intro lo hi
  -- `mid` は let 束縛なので、場合分けの仮説を展開した形で言い直してから simp に渡す。
  induction lo, hi using findRange.go.induct rs n with
  | case1 lo hi hlo mid hnone =>
    intro r h
    have hn : rs[(lo + hi) / 2]? = none := hnone
    rw [findRange.go] at h; simp [hlo, hn] at h
  | case2 lo hi hlo mid r' hsome hlt ih =>
    intro r h
    have hs : rs[(lo + hi) / 2]? = some r' := hsome
    rw [findRange.go] at h; simp only [hlo, hs, hlt, dif_pos, if_true] at h
    exact ih r h
  | case3 lo hi hlo mid r' hsome hge hhi ih =>
    intro r h
    have hs : rs[(lo + hi) / 2]? = some r' := hsome
    rw [findRange.go] at h
    simp only [hlo, hs, hge, hhi, dif_pos, if_false, if_true] at h
    exact ih r h
  | case4 lo hi hlo mid r' hsome hge hhi =>
    intro r h
    have hs : rs[(lo + hi) / 2]? = some r' := hsome
    rw [findRange.go] at h
    simp only [hlo, hs, hge, hhi, dif_pos, if_false] at h
    refine ⟨(lo + hi) / 2, (Array.getElem?_eq_some_iff.mp hs).1, ?_⟩
    rw [(Array.getElem?_eq_some_iff.mp hs).2]
    exact Option.some.inj h
  | case5 lo hi hlo =>
    intro r h; rw [findRange.go] at h; simp [hlo] at h

/-- `findRange` が返す区間は、引いた配列の要素である。 -/
theorem findRange_mem {rs : Array IdnaRange} {n : Nat} {r : IdnaRange}
    (h : findRange rs n = some r) : ∃ i, ∃ hlt : i < rs.size, rs[i] = r :=
  findRange_go_mem rs n 0 rs.size r h

/-- 妥当な scalar value なら、番号から `Char` を作って戻すと同じ番号になる。 -/
theorem toNat_ofNat_of_valid {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

/--
**`checkResolved` が通れば `Resolved` が成り立つ。**

`mapAll_valid` / `mapAll_idempotent` が置いている仮定は、これで
読み込み時の検査に還元される。表そのものは証明に現れないままである。
-/
theorem checkResolved_sound {rs : Array IdnaRange} (h : checkResolved rs = true) :
    (tableOfRanges rs).Resolved := by
  intro c hc d hd
  -- status が mapped なので、`findRange` は c を含む区間を返している。
  simp only [tableOfRanges] at hc hd ⊢
  split at hc
  · next r hr =>
    -- その区間は配列の要素なので、checker の述語が使える。
    obtain ⟨i, hlt, hi⟩ := findRange_mem hr
    have hall := Array.all_eq_true.mp h i hlt
    rw [hi] at hall
    simp only [hc, bne_self_eq_false, Bool.false_or] at hall
    -- d は写像先の番号 m から作った Char である。
    simp only [hr] at hd
    obtain ⟨m, hm, hdm⟩ := List.mem_map.mp hd
    have hmall := List.all_eq_true.mp hall m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmall
    obtain ⟨hvalid, hfind⟩ := hmall
    subst hdm
    rw [toNat_ofNat_of_valid hvalid]
    -- goal と `hfind` は同じ `findRange rs m` を見ているので、まとめて場合分けする。
    revert hfind
    split
    · intro hf; exact of_decide_eq_true hf
    · intro hf; simp at hf
  · simp at hc

end Url
