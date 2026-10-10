# 参照する仕様の版

本 model が対応する仕様は次のとおり。

| 仕様 | 版 | commit |
| --- | --- | --- |
| WHATWG DOM Standard | Living Standard, 2026-08-25 | `a2331a45360129e8645ef7e0a04740241b6e3726` |
| WHATWG Web IDL Standard | Living Standard, 2026-10-06 | `8c65329114411ebd3af025106c2267f5bc00faeb` |
| ECMA-262（ECMAScript Language Specification） | draft, 2026-10-09 | `5345883164f463e87f8b40aca4956157ecba8783` |

* 本文：https://dom.spec.whatwg.org/
* source：https://github.com/whatwg/dom/blob/main/dom.bs
* Web IDL の本文：https://webidl.spec.whatwg.org/（source は whatwg/webidl の `index.bs`）。
  method を呼ぶ層（`Dom/Exec/Invoke.lean`・`Dom/Exec/Eval.lean`）と、JavaScript の値から IDL の値への変換
  （`Dom/Idl/`）がこの版に従う。step と Lean の定義の対応表は `Trace/Webidl.lean` にある。
* ECMA-262 の本文：https://tc39.es/ecma262/（source は tc39/ecma262 の `spec.html`）。
  Web IDL の変換が呼ぶ抽象操作（ToBoolean、ToNumber、StringToNumber、ToString、Number::toString、ToPrimitive）と
  `Array.prototype.join`（`Dom/Idl/`）がこの版に従う。対応表は `Trace/Ecma.lean` にある。

上記 commit は `dom.bs` に対する 2026-08-25 時点の最新 commit である。
Phase 3 の algorithm はこの版の本文から step を写している。

各定義の doc comment には、対応する節番号と algorithm 名、および仕様の step 番号を記す。
仕様が改訂されたときは、この表の commit を更新したうえで step 番号の差分を追う。

## この版で確認した、計画時点との差分

* **`ensure pre-insert validity` は `childrenToExclude` を引数に取る。**
  `pre-insert` は « »、`replace` は « child » を渡す。
  以前の版で `replace` が inline に持っていた例外条件がこの引数にまとめられている。
* **`move` algorithm と `ParentNode.moveBefore()` が本文に入っている。**
  詳細は `docs/status.md` の Phase 3 の節に記す。

## step との対応の機械検査

各 algorithm のどの step をどの Lean の定義が実装しているかは、DOM は `Trace/Dom/`、Web IDL は `Trace/Webidl.lean` の
対応表に書く。表は散文ではなく Lean の値なので、存在しない定義名を書くと build が失敗する。
道具は仕様の名前（`dom`・`webidl`・`ecma262`、`spec-trace/specs.rb`）を `--spec` で受け、既定は `dom` である。
ECMA-262 の表は `Trace/Ecma.lean` にある。

| ファイル | 役割 |
| --- | --- |
| `spec-trace/extract.rb` | `dom.bs` から algorithm（描画された仕様の anchor を鍵とする）と番号付き step を抜き出す。step は `<ol>` で書かれている |
| `spec-trace/extract_md.rb` | Web IDL の `index.bs` から同じ形で抜き出す。step は `<div algorithm>` の中の markdown の番号付きリストで書かれている |
| `spec-trace/extract_ecma.rb` | ECMA-262 の `spec.html`（ecmarkup）から、model が使う節（型変換 §7.1、Number::toString、`Array.prototype.join`）の部分木だけを同じ形で抜き出す。鍵は節の id で、一つの節に algorithm が複数あれば `<id>/<k>` |
| `spec-trace/dom.json`・`webidl.json`・`ecma262.json` | 上の commit の source から抜き出したもの。step ごとに本文の hash を持つ |
| `Trace/Dom/*.lean`・`Trace/Webidl.lean`・`Trace/Ecma.lean` | 対応表。step を「実装」「近似（違いを書く）」「除外（理由を書く）」に分ける |
| `spec-trace/check.rb` | 表と snapshot を突き合わせ、`docs/spec-coverage.md`（`-webidl.md`・`-ecma262.md`）と `spec-trace/map.json`（`webidl-map.json`・`ecma262-map.json`）を作る |
| `spec-trace/drift.rb` | 上の commit と仕様の repository の新しい版を比べ、表が引き受けている step の変化を挙げる |

CI（`ci.yml`）は、DOM、Web IDL、ECMA-262 のそれぞれについて次を検査する（ECMA-262 は抜き出した節の中で）。

* source の algorithm はどれも、表に載るか、理由付きで対象外とされる。
* 表に載せた algorithm の step はどれも、実装・近似・除外のどれかに入る。
* snapshot は上の commit の source から作り直したものと一致し、その commit は
  この文書と `test/pinned-versions.json` の commit と一致する。

週次の `spec-drift.yml` は whatwg/dom、whatwg/webidl、tc39/ecma262 の main と比べ、表が引き受けている step の本文が変わるか、
分類されていない algorithm が現れたときに失敗する。

Web IDL の表に載せたのは、JavaScript の値から IDL の値への変換のうち model の操作の引数に要るもの
（boolean、`unsigned short`・`unsigned long` と ConvertToInt、DOMString、interface 型、dictionary、nullable、
sequence、union）と、operation の関数（this の検査、引数の変換、method steps を呼ぶ順）である。
それらの変換が呼ぶ ECMAScript の抽象操作（ToBoolean、ToNumber、StringToNumber と StringNumericValue、RoundMVResult、
ToString、Number::toString、ToPrimitive、OrdinaryToPrimitive）と `Array.prototype.join` は、ECMA-262 の表に載せた。

Lean のコメントにある step 番号は、表とは別に人が書いたものである。2026-10 の時点で、
固定版より前の番号のまま残っているものが数十ある（例：`remove` の「step 20」は固定版の step 15。
2025-03 の `moveBefore` の導入で live range の調整が "live range pre-remove steps" にまとめられ、
後ろの step が繰り上がった）。step 番号の正は表のほうである。

## 版を上げる手順

1. `ruby spec-trace/drift.rb --ref <commit>` で、表が引き受けている step のうち本文が変わったもの・
   改番だけのもの・新しい algorithm を確かめる。
2. 「変更」と「追加」の step は、model の読み直しが要る。実行関数と `Dom/Spec/` の関係を直す。
3. `ruby spec-trace/extract.rb --fetch <commit> > spec-trace/dom.json`（Web IDL は
   `ruby spec-trace/extract.rb --spec webidl --fetch <commit> > spec-trace/webidl.json`）で snapshot を作り直し、
   この文書と `test/pinned-versions.json` の commit を書き換える。
4. `lake build` のあと `ruby spec-trace/check.rb` が出すエラー（無くなった step、引き受け漏れの step、
   分類されていない algorithm）を表で直し、`ruby spec-trace/check.rb --write` で生成物を作り直す。
5. 固定 scenario と生成 scenario の差分テストを通す。
