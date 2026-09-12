import Url.Strict

/-!
# `ValidUrl` の境界

`ValidUrl` が §4.1 の何を捕らえ、何を捕らえていないかを例で固定する。
文章だけだと、後から条件を足したり落としたりしたときに追随し損ねる。

ここに並ぶ record はどれも parser も setter も作れない。仕様が禁じているからで、
その根拠は parser の guard と protocol setter の四つの guard にある。
`checkStrictUrl` が WPT と setter の全 case で実行時に確かめている。
-/

namespace Url

/-! ## `ValidUrl` が捕らえるもの -/

/-- opaque path に host は付けられない。この条件が無いと `username` setter の保存が破れる。 -/
example : ¬ ValidUrl { scheme := "sc", path := .opaque "x", host := some (.domain "a") } := by
  intro h
  exact absurd (h.opaqueNoHost rfl) (by simp)

/-- port は 16 bit に収まる。 -/
example : ¬ ValidUrl { scheme := "http", host := some (.domain "a"), port := some 999999 } := by
  intro h
  exact absurd (h.portRange 999999 rfl) (by decide)

/-- host が null なら credentials は持てない。 -/
example : ¬ ValidUrl { scheme := "sc", username := "user" } := by
  intro h
  exact absurd (h.nullHostNoCredentials rfl) (by simp [Url.includesCredentials])

/-! ## `ValidUrl` が捕らえないもの

どれも仕様 §4.1 が禁じている record だが、`ValidUrl` は通してしまう。
`checkStrictUrl` はどれも弾く。
-/

/-- scheme が `file` なら credentials は持てない（§4.1）。 -/
example : ValidUrl { scheme := "file", username := "user", host := some (.domain "a") } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

example : checkStrictUrl
    { scheme := "file", username := "user", host := some (.domain "a") } = false := by decide

/-- host が空なら port は持てない（§4.1）。 -/
example : ValidUrl { scheme := "sc", host := some .empty, port := some 80 } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

example : checkStrictUrl { scheme := "sc", host := some .empty, port := some 80 } = false := by
  decide

/-- special な scheme に opaque host は付かない（§4.1 の表）。 -/
example : ValidUrl { scheme := "https", host := some (.opaque "x") } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

example : checkStrictUrl { scheme := "https", host := some (.opaque "x") } = false := by decide

/-- special な URL の host は null でない（§4.1 の表）。これは終端でしか成り立たない。 -/
example : ValidUrl { scheme := "https" } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

example : checkStrictUrl { scheme := "https" } = false := by decide

/--
path segment に `/` は含まれない（§4.1）。**serializer の正しさがこれに依存する。**

この record を serialize すると `sc://x` になり、parse し直すと
opaque host `x` を持つ別の record になる。`parse ∘ serialize` が壊れる。
-/
example : ValidUrl { scheme := "sc", path := .list ["/x"] } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Url.isSpecial, Url.hasOpaquePath, Path.isOpaque, Url.includesCredentials,
      isSpecialScheme, defaultPort]

example : checkStrictUrl { scheme := "sc", path := .list ["/x"] } = false := by decide

example : urlSerializer { scheme := "sc", path := .list ["/x"] } = "sc://x" := by rfl

end Url
