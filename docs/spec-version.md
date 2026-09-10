# 参照する仕様の版

本 model が対応する仕様は次のとおり。

| 仕様 | 版 | commit |
| --- | --- | --- |
| WHATWG DOM Standard | Living Standard, 2026-08-25 | `a2331a45360129e8645ef7e0a04740241b6e3726` |

* 本文：https://dom.spec.whatwg.org/
* source：https://github.com/whatwg/dom/blob/main/dom.bs

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
