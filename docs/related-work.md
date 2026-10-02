# 関連研究

DOM を定理証明系で形式化した研究はすでにある。
この文書は、主な先行研究との違いを整理し、この形式化が何を新しく扱っているかを示す。

## Isabelle/HOL の Core DOM

最も近い先行研究は、Brucker と Herzberg による Isabelle/HOL での DOM の形式化である。
論文と、それを拡張した一連の Archive of Formal Proofs（AFP）のエントリーからなる。

- **論文**：A. D. Brucker, M. Herzberg, *A Formal Semantics of the Core DOM in Isabelle/HOL*, Companion Proceedings of The Web Conference 2018. <https://doi.org/10.1145/3184558.3185980>
- **Core_DOM**（AFP、2018 年）：DOM の中核である node tree の形式化。<https://www.isa-afp.org/entries/Core_DOM.html>
- **Shadow_DOM**（AFP、2020 年）：Core_DOM に shadow root を加えたもの。<https://www.isa-afp.org/entries/Shadow_DOM.html>
- **DOM_Components** と **Shadow_SC_DOM**（AFP）：Shadow_DOM の上に Web Components と、安全に合成できる DOM を形式化したもの。

### Core DOM が扱うもの

Core DOM は、型付きのポインタと型付きのオブジェクト指向ヒープで DOM の状態を表す。
その上で、木、属性、node の生成、検索、木の mutation を定義している。
証明の対象は、well-formed なヒープの保存にとどまらない。
操作が純粋か、どの領域を読み書きするか、どの条件で正常に終了するかも体系的に示している。
locale と型の多項式による拡張の仕組みを持ち、Shadow DOM や Web Components への拡張はこの仕組みの上で行われている。
形式化は実行可能で、生成したコードを仕様準拠の確認に使っている。

### この形式化との違い

両者は対象範囲が重なりつつ、狙いが異なる。

| 観点 | Isabelle/HOL の Core DOM | lean4-dom |
| --- | --- | --- |
| 状態の表現 | 型付きのオブジェクト指向ヒープ。locale で拡張できる | `NodeId` から node のデータへの有限写像。node の種類は閉じた列挙で持つ |
| 参照する仕様 | 2018 年前後の DOM | 特定の commit に固定した現行の WHATWG DOM Standard（`docs/spec-version.md`） |
| mutation algorithm | 木の mutation の中核 | §4.2.3 の algorithm 一式（pre-insert、insert、remove、replace、replace all、adopt、`moveBefore` の move） |
| live object | 扱わない | live Range、NodeIterator、TreeWalker。mutation に伴う調整まで含む |
| 他の状態 | 属性、生成、検索 | 属性（`Attr` を node として扱う）、生成、clone と import、検索、MutationObserver の record と配送、event の配送、Selectors の照合、quirks mode、UTF-16 の offset |
| Shadow DOM と Web Components | 扱う（Shadow_DOM、DOM_Components） | 扱わない |
| 証明の形 | ヒープの well-formedness、純粋性、読み書きする領域、正常終了 | 状態の admissibility が全操作と有限の操作列で保たれること、中心となる algorithm の契約（成功、例外、効果、frame）、実行関数と関係意味論の一致 |
| 実装との関係 | 生成したコードで仕様準拠を確かめる | 同じ操作列を実在する実装に流し、観測を突き合わせる差分テストの oracle として使う |
| 公開の形 | 査読論文と AFP | このリポジトリ |

違いの中心は二つある。

一つ目は、mutation に追随して状態が変わる live object を同じ状態遷移系に入れていることである。
一つの `remove` が木、Range、NodeIterator、MutationObserver の registration をまとめて遷移させ、その全体で妥当性が保たれることを示している。
Core DOM は木とヒープの性質に焦点を置いており、こうした live object は対象に入っていない。

二つ目は、形式化を実在する DOM 実装の検証に使っていることである。
Ruby の DOM 実装 Dommy に加え、jsdom、happy-dom、Chromium、Firefox、WebKit に同じ scenario を流している。
その結果、実装の不一致を 56 件見つけた（`docs/status.md`）。
仕様についての知見も得た。
たとえば、`insert` は live range の「start が end より前にある」という順序を保たないことを、反例として定理にした（`docs/theorems.md` の 9）。

逆に、Core DOM のほうが優れている点もある。
拡張の仕組みを最初から設計に組み込んでいること、Shadow DOM と Web Components まで扱っていること、査読と AFP による公開を経ていることである。
この形式化の node の種類は閉じた列挙であり、shadow tree を加えるには木の定義と well-formedness から広げる必要がある。

### 目標とする成熟度

この形式化は、Core DOM より広い DOM の形式化を目指してはいない。
目指すのは、異なる、意図的に絞った対象範囲において、比較に耐える研究成果物として成熟することである。
具体的には、次を貢献とする。

- 現行の WHATWG の mutation algorithm を、機械で検査できる意味論として書いたこと
- live Range と NodeIterator を含む、一つの状態遷移系を作ったこと
- 任意の有限の操作列について、状態の妥当性が保たれることを示したこと
- 共通の観測モデルを定め、生成した操作列の上で実装と観測を突き合わせる差分テストを行っていること
- 形式化の過程で仕様の性質についての反例を見つけたこと
- Dommy などの実装で、準拠していない箇所を見つけ、修正につなげたこと

Shadow DOM や Web Components を含まなくても、この範囲でモデル、証明、実行、評価、再現性が閉じていれば、独立した研究基盤としての価値を持つ。

## その他の関連研究

Gardner、Smith、Wheelhouse、Zarfaty の *Local Hoare Reasoning about DOM*（PODS 2008）は、DOM Core Level 1 の木の更新を形式化した。
DOM を操作するプログラムの性質を、局所的な Hoare 論理で推論するためのものである。
この形式化は、プログラムの検証ではなく、DOM の操作そのものの意味論と実装の検証を対象にしている。
