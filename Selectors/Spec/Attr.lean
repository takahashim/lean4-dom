import Selectors.Parser

/-!
# attribute selector の構文の関係仕様（Selectors §6.3 / CSS Syntax §6.3.2）

`Selectors/Parser.lean` の `parseAttrBlock` が `[ ... ]` の中身から作る `Simple` を、
実行関数を呼ばずに**関係**として書く。`Dom/Spec/Selector.lean` の
`attrTestHolds_iff`（照合側）と対になる。

誤りやすいのは、空白を置ける位置と、六つの演算子・`i`/`s` flag の写像である。
関係は `attrFlag` / `attrValue` / `attrTail` / `parseAttrBlock` の段に対応させてある。
-/

namespace Selectors.Spec

open Selectors
open Infra

/-! ## flag（`i` / `s` / 無し） -/

/-- §6.3.3 の flag。前後の空白は許すが、識別子の後ろは空白だけ。 -/
inductive AttrFlagSyntax : List Component → AttrCase → Prop where
  /-- flag 無し。後ろは空白だけ。 -/
  | none {rest : List Component} (h : dropWs rest = []) : AttrFlagSyntax rest .byDocument
  /-- `i`。 -/
  | insensitive {rest : List Component} {f : String} {tail : List Component}
      (hd : dropWs rest = .tok (.ident f) :: tail) (he : dropWs tail = [])
      (hf : asciiLowercase f == "i") :
      AttrFlagSyntax rest .insensitive
  /-- `s`。 -/
  | sensitive {rest : List Component} {f : String} {tail : List Component}
      (hd : dropWs rest = .tok (.ident f) :: tail) (he : dropWs tail = [])
      (hf : asciiLowercase f == "s") :
      AttrFlagSyntax rest .sensitive

/-! ## 値と flag -/

/-- `attrValue` が読む値。string か ident のどちらかで、後ろは flag。 -/
inductive AttrValueSyntax : List Component → AttrOp → AttrTest → Prop where
  | str {l : List Component} {v : String} {rest : List Component} {c : AttrCase} {op : AttrOp}
      (hd : dropWs l = .tok (.string v) :: rest) (hc : AttrFlagSyntax rest c) :
      AttrValueSyntax l op ⟨op, v, c⟩
  | ident {l : List Component} {v : String} {rest : List Component} {c : AttrCase} {op : AttrOp}
      (hd : dropWs l = .tok (.ident v) :: rest) (hc : AttrFlagSyntax rest c) :
      AttrValueSyntax l op ⟨op, v, c⟩

/-! ## `[name ...]` の中身（演算子を inline する） -/

/-- `attrTail`。`[name]` か `[name op value flag]`。 -/
inductive AttrTailSyntax (name : String) (anyNs : Bool) : List Component → Simple → Prop where
  | plain {l : List Component} (h : dropWs l = []) :
      AttrTailSyntax name anyNs l (.attr name anyNs none)
  | exact {l : List Component} {d : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: rest) (h : (d == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .exact t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))
  | includes {l : List Component} {d e : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: .tok (.delim e) :: rest)
      (hd1 : (d == CH_TILDE) = true) (he : (e == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .includes t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))
  | dashMatch {l : List Component} {d e : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: .tok (.delim e) :: rest)
      (hd1 : (d == CH_PIPE) = true) (he : (e == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .dashMatch t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))
  | prefixMatch {l : List Component} {d e : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: .tok (.delim e) :: rest)
      (hd1 : (d == CH_CARET) = true) (he : (e == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .prefixMatch t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))
  | suffixMatch {l : List Component} {d e : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: .tok (.delim e) :: rest)
      (hd1 : (d == CH_DOLLAR) = true) (he : (e == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .suffixMatch t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))
  | substring {l : List Component} {d e : Char} {rest : List Component} {t : AttrTest}
      (hd : dropWs l = .tok (.delim d) :: .tok (.delim e) :: rest)
      (hd1 : (d == CH_STAR) = true) (he : (e == CH_EQUALS) = true)
      (hv : AttrValueSyntax rest .substring t) :
      AttrTailSyntax name anyNs l (.attr name anyNs (some t))

/-! ## `[*|name ...]` / `[name ...]` -/

/-- `parseAttrBlock`。 -/
inductive AttrBlockSyntax : List Component → Simple → Prop where
  | plain {items : List Component} {name : String} {rest : List Component} {s : Simple}
      (hd : dropWs items = .tok (.ident name) :: rest) (ht : AttrTailSyntax name false rest s) :
      AttrBlockSyntax items s
  | anyNs {items : List Component} {name : String} {rest : List Component} {s : Simple}
      (hd : dropWs items = .tok (.delim CH_STAR) :: .tok (.delim CH_PIPE) :: .tok (.ident name) :: rest)
      (ht : AttrTailSyntax name true rest s) :
      AttrBlockSyntax items s

end Selectors.Spec
