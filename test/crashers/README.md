# 実装を落とす scenario

差分テストが見つけた、**実装の process ごと落ちる** scenario を置く。
仕様との不一致ではないので `test/scenarios/` には入れない
（固定 scenario に入れると、毎回 batch が途中で死んで走行が遅くなる）。

`test/difftest.rb` は batch の後で足りない出力を一本ずつ回し直すので、
生成 scenario がこれを踏んでも、落ちた一本だけが ERROR になる。

| file | 症状 |
| --- | --- |
| `dommy-text-content-after-range-insert-node.json` | `Range.insertNode` で ProcessingInstruction を入れたあと `textContent` を読むと、Dommy（makiri）が `element.rb:1401` の `@__node__.text` で segfault する |
