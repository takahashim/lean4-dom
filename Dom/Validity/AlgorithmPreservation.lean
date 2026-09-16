import Dom.Validity.PreserveCharacterData

/-!
# §4.2.3 の algorithm による admissibility の保存

`docs/status.md` の「Phase A：admissibility」の完了条件
「全対象 operation の `preserves_admissible`」に向けて、
木に関する三つの層（`StructurallyValid` / `NodeDocumentsValid` /
`DocumentTreesValid`）を algorithm ごとに積み上げる。

一つの file が 2,400 行を超えていたので operation 別に切り分けた。
ここは再 export だけで、中身は次の file にある。

| file | 内容 |
| --- | --- |
| `Dom/Validity/PreserveShared.lean` | 共有の補題、木の形を変えない操作、validity 検査が確立する kind の事実 |
| `Dom/Validity/PreserveRemove.lean` | `remove` / `removeEach` |
| `Dom/Validity/PreserveInsertAt.lean` | `insertAt` が Document の children 制約に与える効果 |
| `Dom/Validity/PreserveMove.lean` | `move` / `moveBefore` |
| `Dom/Validity/PreserveAdopt.lean` | `adopt` |
| `Dom/Validity/PreserveInsertEach.lean` | `insertEach` |
| `Dom/Validity/PreserveInsert.lean` | `insert` |
| `Dom/Validity/PreserveInsertDocument.lean` | `insert` が Document の children 制約を保つこと |
| `Dom/Validity/PreserveReplace.lean` | `replace` |
| `Dom/Validity/PreserveReplaceDocument.lean` | `replace` が Document の children 制約を保つこと |
| `Dom/Validity/PreserveReplaceAll.lean` | `replace all` |
| `Dom/Validity/PreserveCharacterData.lean` | `replaceData` |
-/
