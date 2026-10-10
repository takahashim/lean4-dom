# 参照する仕様の版

本 model が対応する仕様は次のとおり。

| 仕様 | 版 | commit |
| --- | --- | --- |
| WHATWG DOM Standard | Living Standard, 2026-08-25 | `a2331a45360129e8645ef7e0a04740241b6e3726` |
| WHATWG Web IDL Standard | Living Standard, 2026-10-06 | `8c65329114411ebd3af025106c2267f5bc00faeb` |

* 本文：https://dom.spec.whatwg.org/
* source：https://github.com/whatwg/dom/blob/main/dom.bs
* Web IDL の本文：https://webidl.spec.whatwg.org/（source は whatwg/webidl の `index.bs`）。
  method を呼ぶ層（`Dom/Exec/Invoke.lean`）と整数型の変換（`Dom/Idl/Number.lean`）がこの版に従う。
  step と Lean の定義の対応表（`Trace/`）はまだ DOM だけを対象にしている。

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

各 algorithm のどの step をどの Lean の定義が実装しているかは、`Trace/Dom/` の対応表に書く。
表は散文ではなく Lean の値なので、存在しない定義名を書くと build が失敗する。

| ファイル | 役割 |
| --- | --- |
| `spec-trace/extract.rb` | `dom.bs` から algorithm（描画された仕様の anchor を鍵とする）と番号付き step を抜き出す |
| `spec-trace/dom.json` | 上の commit の `dom.bs` から抜き出したもの。step ごとに本文の hash を持つ |
| `Trace/Dom/*.lean` | 節ごとの対応表。step を「実装」「近似（違いを書く）」「除外（理由を書く）」に分ける |
| `spec-trace/check.rb` | 表と `spec-trace/dom.json` を突き合わせ、`docs/spec-coverage.md` と `spec-trace/map.json` を作る |
| `spec-trace/drift.rb` | 上の commit と whatwg/dom の新しい版を比べ、表が引き受けている step の変化を挙げる |

CI（`ci.yml`）は次を検査する。

* `dom.bs` の algorithm はどれも、表に載るか、理由付きで対象外とされる。
* 表に載せた algorithm の step はどれも、実装・近似・除外のどれかに入る。
* `spec-trace/dom.json` は上の commit の `dom.bs` から作り直したものと一致し、その commit は
  この文書と `test/pinned-versions.json` の commit と一致する。

週次の `spec-drift.yml` は whatwg/dom の main と比べ、表が引き受けている step の本文が変わるか、
分類されていない algorithm が現れたときに失敗する。

Lean のコメントにある step 番号は、表とは別に人が書いたものである。2026-10 の時点で、
固定版より前の番号のまま残っているものが数十ある（例：`remove` の「step 20」は固定版の step 15。
2025-03 の `moveBefore` の導入で live range の調整が "live range pre-remove steps" にまとめられ、
後ろの step が繰り上がった）。step 番号の正は表のほうである。

## 版を上げる手順

1. `ruby spec-trace/drift.rb --ref <commit>` で、表が引き受けている step のうち本文が変わったもの・
   改番だけのもの・新しい algorithm を確かめる。
2. 「変更」と「追加」の step は、model の読み直しが要る。実行関数と `Dom/Spec/` の関係を直す。
3. `ruby spec-trace/extract.rb --fetch <commit> > spec-trace/dom.json` で snapshot を作り直し、
   この文書と `test/pinned-versions.json` の commit を書き換える。
4. `lake build` のあと `ruby spec-trace/check.rb` が出すエラー（無くなった step、引き受け漏れの step、
   分類されていない algorithm）を表で直し、`ruby spec-trace/check.rb --write` で生成物を作り直す。
5. 固定 scenario と生成 scenario の差分テストを通す。
