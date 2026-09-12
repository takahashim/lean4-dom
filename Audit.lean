import Lean
import Dom
import Url
import Dom.Exec.Invariant

/-!
# 公開主定理の axiom audit

`notes/research-foundation-roadmap.md` §11.1。

公開する主定理が、許容した三つの axiom
（`propext` / `Classical.choice` / `Quot.sound`）以外に依存していないことを検査する。
`sorryAx` や意図しない独自 axiom が入ったら、この file の elaboration が失敗する。

CI からは次で走らせる。

```sh
lake env lean Audit.lean
```

この file は `lake build` の対象外なので、`Dom` library の依存関係は増やさない。
-/

namespace Dom.Audit

open Lean Elab Command

/--
許容する axiom。

* `propext` — 命題の外延性。`Prop` の等式を扱う補題が使う。
* `Classical.choice` — 古典論理。`by_cases` と `Decidable` の古典 instance が使う。
* `Quot.sound` — 商型。`List` などの core の定義が使う。

`sorryAx` は当然ここに入れない。
-/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 指定した定数が許容外の axiom に依存していないことを検査する。 -/
syntax (name := auditAxioms) "#audit_axioms" ident+ : command

@[command_elab auditAxioms]
def elabAuditAxioms : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms c
    for a in axs do
      unless allowedAxioms.contains a do
        throwErrorAt id "{c} が許容外の axiom {a} に依存している"
    logInfo m!"{c}: {axs.toList}"

end Dom.Audit

open Dom.Audit

/-! ## 主定理 -/

-- §7 操作列に対する主定理
#audit_axioms
  Dom.Exec.admissible_applyOperation
  Dom.Exec.run_preserves_admissibility
  Dom.Exec.reachable_admissible
  Dom.Exec.runOperations_no_violation

-- §8 `BoundaryLE` の negative result
#audit_axioms
  Dom.exists_insert_breaking_boundaryLE
  Dom.boundaryLE_not_preserved_by_insert

-- §4.2.3 の algorithm の admissibility 保存
#audit_axioms
  Dom.admissible_remove
  Dom.admissible_insert
  Dom.admissible_replace
  Dom.admissible_replaceAll
  Dom.admissible_move
  Dom.admissible_moveBefore
  Dom.admissible_replaceData

-- public API の admissibility 保存
#audit_axioms
  Dom.admissible_appendChild
  Dom.admissible_insertBefore
  Dom.admissible_replaceChild
  Dom.admissible_removeChild
  Dom.admissible_replaceChildren
  Dom.admissible_before
  Dom.admissible_after
  Dom.admissible_replaceWith
  Dom.admissible_nodeRemove
  Dom.admissible_appendData
  Dom.admissible_insertData
  Dom.admissible_deleteData
  Dom.admissible_setData

-- §16 の live object をまとめた形
#audit_axioms
  Dom.remove_preserves_live_objects
  Dom.insert_preserves_endpoints
  Dom.move_matches_remove_insert_observation
  Dom.replaceData_preserves_live_object_validity

-- MutationObserver の配送
#audit_axioms
  Dom.admissible_observe
  Dom.admissible_disconnect
  Dom.admissible_takeRecords
  Dom.admissible_notifyMutationObservers

-- §4.9 attribute の admissibility 保存
#audit_axioms
  Dom.admissible_setAttribute
  Dom.admissible_setAttributeNS
  Dom.admissible_removeAttribute
  Dom.admissible_removeAttributeNS
  Dom.admissible_toggleAttribute

-- 契約
#audit_axioms
  Dom.remove_succeeds_iff
  Dom.remove_error_iff
  Dom.replace_cycle_precedes_notFound
  Dom.insertBefore_cycle_precedes_notFound
  Dom.moveValidity_step1
  Dom.moveValidity_step2
  Dom.moveValidity_step3
  Dom.moveValidity_step4
  Dom.length_spliceData?
  Dom.setAttribute_getAttribute
  Dom.removeAttribute_erases
  Dom.validateAndExtractAttribute_ok

-- URL Standard §3.3 IPv4
#audit_axioms
  Url.ipv4Parser_lt
  Url.foldl_base256_lt

-- URL Standard §5 application/x-www-form-urlencoded
#audit_axioms
  Url.urlencodedEncode_no_separator
  Url.percentEncodeByte_alnum
  Url.hexDigitChar_alnum

-- URL Standard §4.1 URL record の妥当性
#audit_axioms
  Url.checkValidUrl_iff
  Url.pathFold_append
  Url.pathSerializer_cons
  Url.urlSerializer_split
  Url.isSpecialScheme_of_defaultPort

-- URL Standard §6.1 URL の IDL 属性（setter）
#audit_axioms
  Url.setUsername_cannot
  Url.setPassword_cannot
  Url.setPort_cannot
  Url.setHost_opaque
  Url.setHostname_opaque
  Url.setPathname_opaque
  Url.not_opaque_of_canHaveCredentials
  Url.setUsername_valid
  Url.setPassword_valid
  Url.setPort_empty_valid
  Url.run_fragment_shape
  Url.run_query_shape
  Url.basicUrlParseOverride_fragment
  Url.basicUrlParseOverride_query
  Url.validUrl_setOpaque
  Url.stripTrailingSpaces_valid
  Url.setHash_valid
  Url.setSearch_valid
  Url.fail_over
  Url.run_port_valid
  Url.run_fileHost_valid
  Url.run_host_valid
  Url.run_scheme_valid
  Url.run_schemeStart_valid
  Url.run_path_valid
  Url.run_pathStart_valid
  Url.schemeOverride_valid
  Url.setProtocol_valid
  Url.setHost_valid
  Url.setHostname_valid
  Url.setPort_valid
  Url.setPathname_valid
  Url.setAttr_valid

-- URL Standard §4.4 parser が `ValidUrl` を保つこと
#audit_axioms
  Url.shortenPath_spec
  Url.appendSegment_spec
  Url.appendOpaque_spec
  Url.portDone_spec
  Url.userinfoFold_spec
  Url.PInv.notOpaque
  Url.PInv.valid
  Url.valid_of_inv
  Url.PInv_empty
  Url.PInv.portStep
  Url.basicUrlParse_valid_of_step
  Url.step_schemeStart_valid
  Url.step_scheme_valid
  Url.step_noScheme_valid
  Url.step_specialRelativeOrAuthority_valid
  Url.step_pathOrAuthority_valid
  Url.step_relative_valid
  Url.step_relativeSlash_valid
  Url.step_specialAuthoritySlashes_valid
  Url.step_specialAuthorityIgnoreSlashes_valid
  Url.step_authority_valid
  Url.step_host_valid
  Url.step_port_valid
  Url.step_file_valid
  Url.step_fileSlash_valid
  Url.step_fileHost_valid
  Url.step_pathStart_valid
  Url.step_path_valid
  Url.step_opaquePath_valid
  Url.step_query_valid
  Url.step_fragment_valid
  Url.step_valid
  Url.run_valid
  Url.basicUrlParse_valid
  Url.parseUrl_valid

-- RFC 3492 Punycode
#audit_axioms
  Url.Punycode.threshold_pos
  Url.Punycode.threshold_le
  Url.Punycode.toNat_ofNat_ascii
  Url.Punycode.digitChar_ascii
  Url.Punycode.encodeDigits_ascii
  Url.Punycode.decodeDigits_length
  Url.Punycode.encode_ascii
  Url.Punycode.digitValue_digitChar
  Url.Punycode.decodeDigits_encodeDigits
  Url.Punycode.digitChar_ne_delim
  Url.Punycode.encodeDigits_no_delim
  Url.Punycode.encodeExt_no_delim
  Url.Punycode.span_loop_all
  Url.Punycode.span_loop_split
  Url.Punycode.splitLastDelim_no_delim
  Url.Punycode.splitLastDelim_append
  Url.Punycode.splitLastDelim_encode
  Url.Punycode.scanOne_eq
  Url.Punycode.scanFold_eq
  Url.Punycode.encodeLoop_eq
  Url.Punycode.scanOne_lt
  Url.Punycode.scanOne_gt
  Url.Punycode.scanOne_hit
  Url.Punycode.scanFold_no_hit
  Url.Punycode.partialAt_zero
  Url.Punycode.insertIdx_append
  Url.Punycode.encodeDigits_ne_nil
  Url.Punycode.decode_emit
  Url.Punycode.decode_scan
  Url.Punycode.split_first_hit
  Url.Punycode.passRun_inv
  Url.Punycode.scanFold_passRun
  Url.Punycode.passRun_n
  Url.Punycode.passRun_A
  Url.Punycode.filter_lt_eq
  Url.Punycode.decode_outer
  Url.Punycode.mem_insertSorted
  Url.Punycode.mem_sortedDistinct
  Url.Punycode.strictSorted_insertSorted
  Url.Punycode.strictSorted_sortedDistinct
  Url.Punycode.char_valid
  Url.Punycode.decode_encode

-- UTS #46 ToASCII（表は仮定 `IdnaTable.Resolved` に押し込んである）
#audit_axioms
  Url.mapAll_valid
  Url.mapAll_idempotent
  Url.labelToASCII_ascii
  Url.asciiDomainCheck_ne_empty
  Url.asciiDomainCheck_no_forbidden
  Url.toASCII_ne_empty
  Url.toASCII_no_forbidden
  Url.validALabel
  Url.findRange_go_mem
  Url.findRange_mem
  Url.findRange_go_contains
  Url.findRange_contains
  Url.sorted_step
  Url.range_le
  Url.sorted_lt
  Url.findRange_go_complete
  Url.findRange_complete
  Url.toNat_ofNat_of_valid
  Url.checkResolved_sound

-- UTF-8 の往復（Infra）
#audit_axioms
  Infra.lor_add
  Infra.lor_low
  Infra.lor3
  Infra.lor4
  Infra.charOfScalar_toNat
  Infra.continuationBits_ofNat
  Infra.utf8Decode_encodeChar
  Infra.utf8Decode_encode
  Infra.utf8DecodeString_encode

-- URL Standard §5 の往復
#audit_axioms
  Url.utf8Encode_ofList_ascii
  Url.percentDecodeBytes_cons_ne
  Url.hexValue_hexDigitChar
  Url.charOfByte_ascii
  Url.percentDecode_encodeByte
  Url.percentDecode_encodeBytes
  Url.plusToSpace_encodeBytes
  Url.not_set_bounds
  Url.decode_encodeChar
  Url.decode_encodeList
  Url.decodeComponent
  Url.splitAmp_intercalate
  Url.splitFirstEq_append
  Url.urlencodedEncode_ascii
  Url.parse_partBytes
  Url.filterMap_parts
  Url.parse_serialize

-- URL Standard §6.2 `URLSearchParams`
#audit_axioms
  Infra.lexLt_self
  Infra.strLt_self
  Infra.ne_of_strLt
  Url.Params.get_eq_head
  Url.Params.has_eq
  Url.Params.getAll_delete
  Url.Params.getAll_snoc
  Url.Params.getAll_append
  Url.Params.getAll_setFirst
  Url.Params.getAll_set
  Url.Params.length_insert
  Url.Params.length_sort
  Url.Params.getAll_swap
  Url.Params.getAll_insert
  Url.Params.getAll_sort

-- URL Standard §3.2 host / §1.3 percent-encoding
#audit_axioms
  Url.opaqueHostParser_no_forbidden
  Url.asciiDomainToASCII_no_forbidden
  Url.asciiDomainToASCII_ne_empty
  Url.utf8PercentEncode_id

-- boolean checker と Prop の対応
#audit_axioms
  Dom.checkAdmissibleDOMState_iff
  Dom.checkWellFormed_iff
  Dom.checkStructurallyValid_iff
  Dom.checkNodeDocumentsValid_iff
  Dom.checkDocumentTreesValid_iff
  Dom.checkRangeEndpointsValid_iff
  Dom.checkIteratorsValid_iff
  Dom.checkAttributesValid_iff
