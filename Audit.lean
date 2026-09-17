import Lean
import Dom
import Url
import Selectors
import Dom.Exec.Invariant

/-!
# 公開主定理の axiom audit

`docs/theorems.md` の「axiom 依存」。

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
  Dom.admissible_normalize
  Dom.admissible_rangeSetStart
  Dom.admissible_rangeSetEnd
  Dom.admissible_rangeSetStartSibling
  Dom.admissible_rangeSetEndSibling
  Dom.admissible_rangeCollapse
  Dom.admissible_rangeSelectNode
  Dom.admissible_rangeSelectNodeContents
  Dom.admissible_rangeDeleteContents
  Dom.admissible_rangeInsertNode
  Dom.admissible_walkerStep
  Dom.walkersValid_walkerStep
  Dom.compareDocumentPosition_disconnected_consistent
  Dom.admissible_dispatchEvent
  Dom.listenersOnly_dispatchEvent
  Dom.admissible_addEventListener
  Dom.admissible_removeEventListener

-- 関係意味論（§4.2.3 remove）
#audit_axioms
  Dom.freshId_get?_eq_none
  Dom.admissible_createsNode
  Dom.createElement_creates
  Dom.createElementNS_creates
  Dom.createTextNode_creates
  Dom.createComment_creates
  Dom.createDocumentFragment_creates
  Dom.admissible_cloneNode
  Dom.cloneNode_cloneOf
  Dom.cloneNode_ne
  Dom.cloneNode_fresh
  Dom.cloneNode_keep
  Dom.cloneNode_ranges
  Dom.cloneNodeIn_shallow_spec
  Dom.cloneNodeIn_ownerDocument
  Dom.admissible_adopt
  Dom.admissible_importNode
  Dom.importNode_ne
  Dom.importNode_cloneOf
  Dom.importNode_ownerDocument
  Dom.importNode_keep
  Dom.importNode_ranges
  Dom.admissible_adoptNode
  Dom.adoptNode_id
  Dom.adoptNode_ownerDocument
  Dom.adoptNode_detached
  Dom.adoptNode_shape
  Dom.cloneNode_isOk
  Dom.cloneNodeIn_isOk
  Dom.importNode_isOk
  Dom.adopt_isOk
  Dom.adoptNode_isOk
  Dom.liveRangePreRemoveBP_comm
  Dom.liveRangePreRemoveBP_eq
  Dom.rangeShiftAfterRemove_node
  Dom.insert_cases
  Dom.insert_of_not_fragment
  Dom.replace_cases
  Dom.replace_of_validity_error
  Dom.replaceReferenceChild_eq
  Dom.replaceNodes_eq
  Dom.insertEachAt_cases
  Dom.insertEachAt_of_get?
  Dom.insertNodesAt_cases
  Dom.insertNodesAt_isOk
  Dom.insertPrevSibling_some
  Dom.insertPrevSibling_none
  Dom.parentOf_eq
  Dom.parentOf_of_get?
  Dom.parentOf_congr
  Dom.detachWithLiveAdjust_cases
  Dom.detachWithLiveAdjust_of_detach
  Dom.adopt_cases
  Dom.adopt_of_steps
  Dom.ensurePreInsertionValidity_ok_steps
  Dom.replaceAll_cases
  Dom.preRemove_cases
  Dom.preRemove_of_parent
  Dom.nodeRemove_cases
  Dom.nodeRemove_of_parent
  Dom.doctypeFollows_of_splitAt?
  Dom.doctypeFollows_congr
  Url.opaqueHostParser_cases
  Url.opaqueHostParser_of_no_forbidden
  Dom.nodeEqualsFuel_eq_of_le
  Dom.nodeEqualsFuel_eq_nodeEquals
  Dom.remove_cases
  Dom.remove_of_detach
  Dom.remove_of_no_parent
  Dom.preInsert_cases
  Dom.preInsert_of_validity
  Dom.preInsert_of_validity_error
  Dom.preInsertReferenceChild_eq
  Dom.kindOf_eq
  Dom.kindOf_of_get?
  Dom.ownerDocumentOf_eq
  Dom.ownerDocumentOf_of_get?
  Dom.childrenOf_congr
  Dom.childrenOf_congr_children
  Dom.rangeMoveOutOfSubtree_pos
  Dom.rangeMoveOutOfSubtree_neg
  Dom.rangeShiftAfterRemove_pos
  Dom.rangeShiftAfterRemove_neg
  Dom.liveRangePreRemoveBP_pos
  Dom.liveRangePreRemoveBP_neg
  Dom.isInclusiveAncestorOf_self
  Dom.childHasParent_some_iff
  Dom.nodeContains_iff
  Dom.nodeContains_getRootNode
  Dom.compareDocumentPosition_self
  Dom.compareDocumentPosition_of_contains
  Dom.nodeEquals_refl
  Dom.getTextContent_eq_getNodeValue_of_characterData
  Dom.isDefaultNamespace_iff
  Dom.lookupNamespaceURI_xml
  Dom.parentElement_eq_some_iff
  Dom.documentElement_spec
  Dom.kindOf_of_mem_elementChain
  Dom.mem_nodesToRemove_iff
  Dom.nodesToRemove_nodup
  Dom.parentOf_not_mem_nodesToRemove
  Dom.rangeDeleteContents_of_collapsed
  Dom.isValidNamespacePrefix_of_isValidAttributeLocalName
  Dom.findAttr_owner
  Dom.findAttr_detached
  Dom.checkValidWalker_iff
  Dom.checkWalkersValid_iff
  Url.Params.hasValue_eq
  Url.Params.getAll_deleteValue
  Url.Params.hasValue_deleteValue
  Url.Params.searchParams_withParams
  Url.getAttr_isSome_iff
  Url.setAttr_isSome_iff_getAttr_isSome
  Url.origin_eq_none_of_other
  Url.origin_eq_none_of_host_none
  Url.origin_of_special
  Url.startsWithWindowsDrive_of_isNormalized
  Url.getAttr_protocol
  Url.protocol_eq
  Dom.walkerAccepts_eq
  Dom.walkerAccepts_eq_false_of_get?_eq_none
  Dom.walkerBase_of_inclusiveAncestor
  Dom.mem_splitWs_iff
  Dom.Spec.wordIn_append_ws
  Dom.Spec.wordIn_of_no_ws
  Dom.Spec.selectorAttr_isSome_iff
  Dom.Spec.plainAttr_isSome_iff
  Dom.Spec.any_isAsciiWhitespace_caseFold
  Infra.isAsciiWhitespace_asciiLowerChar
  Selectors.scan_has_in_has
  Selectors.scan_has_empty
  Selectors.scan_nth_of_type_no_of
  Selectors.scan_star_subclass
  Selectors.scan_forgiving_drop
  Selectors.scan_strict_fails
  Dom.runAction_stopImmediate
  Dom.runAction_preventDefault_cancelable
  Dom.runAction_preventDefault_not_cancelable
  Dom.invokeOne_once
  Dom.innerInvoke_skip
  Dom.innerInvoke_log_prefix
  Dom.runPass_log_prefix
  Dom.runPass_stopPropagation
  Dom.runPass_no_bubbles
  Dom.dispatchEvent_not_cancelable
  Dom.dispatchEvent_not_found
  Dom.InsertFacts.congr
  Dom.InsertFacts.tail
  Dom.InsertFacts.singleton
  Dom.Spec.insert_of_empty_fragment
  Dom.Spec.insert_complete_of_nil
  Dom.Spec.adopt_parentOf_none
  Dom.Spec.insertEach_complete
  Dom.Spec.removeEach_complete
  Dom.Spec.insertEachAt_complete
  Dom.Spec.insertNodesAt_isOk_of_spec
  Dom.Spec.insert_isOk_of_spec
  Dom.Spec.insert_complete
  Dom.replaceDataAdjustBP_at_start
  Dom.admissible_createAttribute
  Dom.admissible_createAttributeNS
  Dom.admissible_setAttributeNode
  Dom.admissible_removeAttributeNode
  Dom.admissible_removeNamedItem
  Dom.Spec.remove_sound
  Dom.Spec.remove_sound_range
  Dom.Spec.remove_sound_iterator
  Dom.Spec.remove_sound_tree
  Dom.Spec.remove_sound_transient
  Dom.Spec.remove_sound_record
  Dom.Spec.removeSpec_deterministic
  Dom.Spec.removeSpec_transport
  Dom.Spec.removeSpec_congr
  Dom.Spec.removeEachSpec_congr
  Dom.Spec.adoptSpec_congr
  Dom.Spec.adoptSpec_deterministic
  Dom.Spec.insertSpec_congr
  Dom.Spec.insertSpec_deterministic
  Dom.Spec.remove_complete
  Dom.Spec.adopt_complete
  Dom.Spec.insert_no_extra_models
  Dom.Spec.replace_no_extra_models
  Dom.Spec.insert_isOk_of_spec_obs
  Dom.Spec.nodesToInsertAcyc_step9
  Dom.Spec.replace_isOk_of_spec
  Dom.Spec.replace_complete
  Dom.Spec.adopt_sound
  Dom.Spec.insert_sound
  Dom.Spec.insertEach_sound
  Dom.Spec.removeEach_sound
  Dom.Spec.replace_sound
  Dom.Spec.replaceSpec_congr
  Dom.Spec.replaceSpec_deterministic
  Dom.Spec.move_sound
  Dom.Spec.moveSpec_congr
  Dom.Spec.moveSpec_deterministic
  Dom.Spec.replaceData_sound
  Dom.Spec.replaceDataSpec_deterministic
  Dom.Spec.replaceData_isOk_of_spec
  Dom.Spec.replaceData_complete
  Dom.Spec.spliceData?_of_dataSpliced
  Dom.Spec.characterDataRecordQueued_unique
  Dom.Utf16.splitAt?_of_split
  Dom.Spec.characterDataRecordQueued_of_queue
  Dom.Spec.treeRecordQueued_of_queue

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

-- URL Standard §3.3 IPv6
#audit_axioms
  Url.takeHex_len
  Url.takeHex_lt
  Url.takeHex4_lt
  Url.set_lt
  Url.getD_set_self
  Url.getD_set_other
  Url.ipv4InIpv6_length
  Url.ipv6Loop_inv
  Url.ipv6Expand_length
  Url.ipv6Finish_length
  Url.ipv6Parser_length
  Url.ipv6Zero_getD
  Url.getD_set_lt
  Url.ipv4InIpv6_step
  Url.ipv4InIpv6_lt
  Url.ipv6Loop_lt
  Url.ipv6Expand_lt
  Url.ipv6Finish_lt
  Url.ipv6Parser_lt

-- URL Standard §3.3 IPv4
#audit_axioms
  Url.ipv4Parser_lt
  Url.foldl_base256_lt

-- URL Standard §5 application/x-www-form-urlencoded
#audit_axioms
  Url.urlencodedEncode_no_separator
  Url.urlencodedSet_eq
  Url.percentEncodeByte_alnum
  Url.hexDigitChar_alnum

-- URL Standard §4.1 URL record の妥当性
#audit_axioms
  Url.checkValidUrl_iff
  Url.hostKindOkOf_none
  Url.hostKindOkOf_file_empty
  Url.hostKindOkOf_congr
  Url.hostParser_hostKind
  Url.hostParser_empty
  Url.host_ne_empty
  Url.empty_host_port
  Url.noSlash_mem
  Url.noSlash_of_mem
  Url.encChar_no_slash
  Url.pathSegsOk_appendOpaque
  Url.pathSegsOk_shortenPath
  Url.pathSegsOk_appendSegment
  Url.driveFix_no_slash
  Url.windowsDriveBuffer_no_slash
  Url.pathSegsOk_pathStepUrl
  Url.noSlash_of_normalizedDrive
  Url.pathSegsOk_fileBasePath
  Url.pathSegsOk_fileSlashDrive
  Infra.toNat_ofNat_ascii
  Infra.asciiLowerChar_ne
  Url.utf8PercentEncode_avoid
  Url.empty_kind
  Url.fileHost_kind
  Url.pathFold_append
  Url.pathSerializer_cons
  Url.urlSerializer_split
  Url.isSpecialScheme_of_defaultPort

-- URL Standard §6.1 URL の IDL 属性（setter）
#audit_axioms
  Url.setUsername_cannot
  Url.setPassword_cannot
  Url.setPort_cannot
  Url.setUsername_spec
  Url.setPassword_spec
  Url.setPort_empty_spec
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
  Url.stripTrailingSpaces_fragment
  Url.stripTrailingSpaces_query
  Url.setHash_empty_hash
  Url.setSearch_empty_search
  Url.run_fragment_spec
  Url.run_fragment_ok
  Url.setHash_spec
  Url.run_query_spec
  Url.run_query_ok
  Url.setSearch_spec
  Url.stripTabNewline_eq_self
  Url.stripTabNewline_digits
  Url.portDone_digits
  Url.run_port_spec
  Url.run_port_ok
  Url.setPort_spec
  Url.run_schemeStart_step
  Url.run_scheme_eq
  Url.schemeOverride_ok
  Url.schemeOverride_spec
  Url.setProtocol_spec
  Url.run_path_seg
  Url.run_pathStart_step
  Url.setPathname_spec
  Url.plainHostChar_spec
  Url.run_host_seg
  Url.stripTabNewline_host
  Url.setHostname_spec
  Url.setHost_spec
  Url.setAttr_valid

-- parse ∘ serialize
#audit_axioms
  Url.dropWhile_of_head
  Url.preprocess_eq_self
  Url.schemeChar_ne_tab
  Url.reverse_head_mid
  Url.run_scheme_prefix
  Url.run_scheme_opaque
  Url.encFold_id
  Url.run_fragment_plain
  Url.run_query_plain
  Url.run_query_chunk
  Url.run_query_eof
  Url.run_query_hash
  Url.run_opaquePath_question
  Url.run_opaquePath_hash
  Url.run_opaquePath_eof
  Url.queryOf_encoded
  Url.run_opaquePath_qf
  Url.ne_tab_of_c0Set
  Url.ne_c0_of_c0Set
  Url.c0Set_of_querySet
  Url.c0Set_of_fragmentSet
  Url.run_opaquePath_chunk
  Url.getLast?_mid
  Url.roundtrip_opaque
  Url.run_path_chunk
  Url.run_path_slash
  Url.run_path_eof
  Url.pathStepUrl_append
  Url.run_path_segs
  Url.pathSerializer_intercal
  Url.intercal_mem
  Url.intercal_head_ne_slash
  Url.c0Set_of_pathSet
  Url.run_scheme_pathOrAuthority
  Url.run_pathOrAuthority_path
  Url.dropLast_getLast?
  Url.ne_c0_of_schemeChar
  Url.roundtrip_path
  Url.run_pathOrAuthority_authority
  Url.run_authority_host
  Url.run_authority_chunk
  Url.run_authority_at
  Url.run_host_chunk
  Url.run_host_pathStart
  Url.run_pathStart_slash
  Url.run_pathStart_eof
  Url.run_pathStart_slash_any
  Url.hostParser_opaque_no_forbidden
  Url.not_forbidden_host
  Url.not_userinfoSet
  Url.pathSerializer_pathChars
  Url.isTerminator_false
  Url.run_scheme_specialAuthoritySlashes
  Url.run_specialAuthoritySlashes
  Url.run_specialAuthorityIgnoreSlashes
  Url.run_pathStart_slash_special
  Url.run_pathStart_eof_special
  Url.run_scheme_authority
  Url.userinfoFold_user
  Url.userinfoFold_pass
  Url.userinfoFold_split
  Url.credChars_head
  Url.credChars_mem
  Url.ne_c0_of_userinfoSet
  Url.serializerTail_authority
  Url.run_authority_hostpath
  Url.run_authority_full
  Url.run_path_full
  Url.run_path_dot
  Url.run_pathStart_path
  Url.portFold_acc
  Url.portValue_append
  Url.digitValue_digitChar
  Url.portValue_toDigitsCore
  Url.portValue_toString
  Url.isAsciiDigit_digitChar
  Url.toDigitsCore_digits
  Url.toDigitsCore_ne_nil
  Url.toString_ne_nil
  Url.toString_digits
  Url.run_host_port
  Url.run_port_chunk
  Url.run_port_pathStart
  Url.run_query_full
  Url.run_fragment_full
  Url.run_path_question
  Url.run_path_hash
  Url.run_pathStart_question
  Url.run_pathStart_hash
  Url.run_pathStart_qf
  Url.qfList_c0
  Url.url_qf_eta
  Url.toHexString_chars
  Url.ipv6Serializer_chars
  Url.run_host_inside
  Url.run_host_bracket
  Url.hostReadable_auth
  Url.run_host_serialized
  Url.hostReadable_ipv6
  Url.ipv6_no_c0
  Url.roundtrip_host
  Url.windowsDriveBuffer_of_not_file
  Url.windowsDriveBuffer_of_path_ne
  Url.windowsDriveBuffer_of_normalized
  Url.windowsDriveBuffer_of_not_drive
  Url.fileHost_terminator
  Url.run_scheme_file
  Url.run_file_slash
  Url.run_fileSlash_slash
  Url.run_fileHost_chunk
  Url.run_fileHost_empty
  Url.run_fileHost_pathStart
  Url.roundtrip_file
  Url.asciiLowerChar_of_schemeChar
  Url.schemeChar_of_canonical
  Url.canonicalScheme_shape
  Url.encodedWith_mem
  Url.hostParser_nil_opaque
  Url.not_drive_of_hostReadable
  Url.ne_qh_of_pathSet
  Url.utf8PercentEncode_out
  Url.ipv4Serializer_chars
  Url.not_forbidden_of_digit
  Url.hostParser_opaque_eq
  Url.hostParser_domain_eq
  Url.ne_c0_of_isC0Control
  Url.c0Set_of_alnum
  Url.hostReadable_of_canonical
  Url.roundtrip_canonical

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

-- URL Standard §3.3 / §3.5 IPv4 の往復
#audit_axioms
  Url.radixDigit_ten
  Url.foldOpt_digits
  Url.parseRadix_ten
  Url.digitChar_ne_zero
  Url.toDigitsCore_head
  Url.toString_head_ne_zero
  Url.ipv4NumberParser_toString
  Url.strictSplit_go_nodot
  Url.strictSplit_go_append
  Url.toString_no_dot
  Url.ipv4Parts_serializer
  Url.ipv4Parser_serializer

-- URL Standard §3.2 / §3.5 host の往復
#audit_axioms
  Url.percentDecodeBytes_ascii_id
  Url.percentDecodeToString_ascii
  Infra.asciiLowercase_id
  Url.asciiDomainToASCII_id
  Url.ipv4Serializer_char_facts
  Url.ipv4Serializer_ne_nil
  Url.endsInANumber_serializer
  Url.hostParser_ipv4
  Url.hostParser_opaque_id
  Url.hostParser_domain_id
  Url.hostParser_ipv6
  Infra.asciiLowerChar_idem
  Infra.asciiLowerChar_ascii
  Url.asciiDomainToASCII_out
  Url.hostParser_ipv6_eq
  Url.hostParser_ipv4_eq
  Url.hostParser_domain_eq'
  Url.utf8PercentEncode_mem
  Url.not_forbidden_of_alnum
  Url.utf8PercentEncode_ne_nil
  Url.hostParser_idem

-- URL Standard §3.3 / §3.5 IPv6 の往復（圧縮しない場合）
#audit_axioms
  Url.hexFold_acc
  Url.hexValueOf_append
  Url.hexValue_hexChar
  Url.hexValueOf_toHexStringGo
  Url.hexValueOf_toHexString
  Url.toHexStringGo_hex
  Url.toHexString_hex
  Url.toHexStringGo_length
  Url.toHexString_length
  Url.takeHex_append
  Url.takeHex_toHexString
  Url.toHexStringGo_ne_nil
  Url.toHexString_ne_nil
  Url.toHexString_head
  Url.ipv6Loop_piece
  Url.ipv6Loop_last
  Url.ipv6Serializer_go_nocompress
  Url.ipv6Parser_serializer_nocompress
  Url.ipv6CompressIndex_run
  Url.ipv6Serializer_go_seg
  Url.ipv6Serializer_go_at
  Url.ipv6Serializer_go_skip
  Url.ipv6Serializer_go_resume
  Url.ipv6Loop_pieces
  Url.ipv6Loop_nil
  Url.ipv6Loop_colon
  Url.ipv6Loop_last'
  Url.set_append_length
  Url.setPieces_append
  Url.takeWhile_zero_replicate
  Url.head_dropWhile_zero
  Url.ipv6_run_decompose
  Url.piecesChars_sep
  Url.piecesChars_snoc
  Url.zipIdx_snd_range
  Url.zipIdx_replicate_zero
  Url.ipv6Serializer_go_tail
  Url.ipv6Serializer_compress_shape
  Url.ipv6Parser_colon_colon
  Url.ipv6Parser_no_colon
  Url.setPieces_snoc
  Url.ipv6Loop_post
  Url.setPieces_zero_shape
  Url.ipv6Parser_serializer_compress
  Url.ipv6Parser_serializer

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

-- URL Standard §4.4 の関係意味論（失敗条件・相対解決・遷移の優先順）
#audit_axioms
  Url.Spec.run_scheme_startOver
  Url.Spec.run_noScheme_none
  Url.Spec.run_noScheme_opaque
  Url.Spec.run_schemeStart_cases
  Url.Spec.basicUrlParse_eq_none_of_not_hasScheme
  Url.Spec.hasScheme_of_basicUrlParse
  Url.Spec.basicUrlParse_eq_none_of_opaque_base
  Url.Spec.decimalOf_eq_portValue
  Url.Spec.run_port_overflow
  Url.Spec.run_port_overflow_failure
  Url.Spec.not_hasScheme_of_no_colon
  Url.Spec.setPort_of_overflow
  Url.Spec.run_fragment
  Url.Spec.run_query
  Url.Spec.credentials_empty
  Url.Spec.run_noScheme_fragment
  Url.Spec.run_noScheme_query
  Url.Spec.run_noScheme_empty
  Url.Spec.basicUrlParse_fragment
  Url.Spec.basicUrlParse_query
  Url.Spec.basicUrlParse_empty
  Url.Spec.scheme_file_before_special
  Url.Spec.host_colon_inside_brackets
  Url.Spec.host_empty_special_fails
  Url.Spec.port_rejects_other
  Url.Spec.path_override_keeps_query_char
  Url.Spec.fileHost_drive_before_host
  Url.Spec.pathStart_backslash_special
  Url.Spec.pathStart_backslash_not_special

-- 定理が空虚でないことの証人
#audit_axioms
  Dom.Witness.state_admissible

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

-- CSS Syntax Level 3 §4 tokenizer の停止性を支える補題
#audit_axioms
  Selectors.consumeEscape_le
  Selectors.consumeIdentSeq_le
  Selectors.consumeIdentSeq_le_of_start
  Selectors.consumeNumber_le
  Selectors.consumeNumber_le_of_start
  Selectors.skipComments_le
  Selectors.tokenAt_le
  Selectors.nextToken_lt

-- selector の parser の停止性を支える補題
#audit_axioms
  Selectors.splitBlock_size
  Selectors.splitBlock_inside_le
  Selectors.splitBlock_after_le
  Selectors.dropToComma_size
  Selectors.splitAtOf_size

-- selector の照合の停止性を支える補題
#audit_axioms
  Dom.sSize_lt_cpSize
  Dom.cxSize_lt_lSize

-- selector の照合の関係意味論（部分）
#audit_axioms
  Dom.Spec.anbMatches_iff
  Dom.Spec.anbMatches_neg_one
  Dom.Spec.anbMatches_odd
  Dom.Spec.anbMatches_even
  Dom.Spec.mem_combCandidates_descendant
  Dom.Spec.mem_combCandidates_child
  Dom.Spec.mem_combCandidates_subsequentSibling
  Dom.Spec.mem_combCandidates_nextSibling
  Dom.Spec.hasPrefixL_iff
  Dom.Spec.hasSuffixL_iff
  Dom.Spec.hasInfixL_iff
  Dom.Spec.attrTestHolds_iff
  Dom.Spec.includes_empty_never
  Dom.Spec.includes_whitespace_never
  Dom.Spec.mem_elementSiblings_iff
  Dom.Spec.sameTypeAs_iff
  Dom.Spec.indexOfNode_of_split
  Dom.Spec.indexOfNode_eq_some
  Dom.Spec.indexOfNode_eq_none
  Dom.Spec.nth_index_iff
  Dom.Spec.mem_nthPoolOf_iff
  Dom.Spec.matchSimple_nth_iff
  Dom.Spec.typeHolds_iff
  Dom.Spec.matchSimple_root_iff
  Dom.Spec.emptyOk_iff
  Dom.Spec.matchSimple_empty_iff
  Dom.Spec.get?_root
  Dom.Spec.matchSimple_has_iff
  Dom.Spec.attrNameInSelector_spec
  Dom.Spec.selectorAttr_some
  Dom.Spec.selectorAttr_none
  Dom.Spec.plainAttr_some
  Dom.Spec.plainAttr_none

-- selector の API が満たすこと
#audit_axioms
  Dom.querySelector_eq_head
  Dom.querySelectorAll_eq_matchTree
  Dom.matchTree_sublist
  Dom.matchTree_nodup
  Dom.mem_matchTree_iff
  Dom.isElement_of_mem_matchTree
  Dom.mem_inclusiveAncestorElements_iff
  Dom.closest_spec
  Dom.closest_first
  Dom.closest_eq_none_iff
  Dom.closest_self
  Dom.scope_irrelevant
  Dom.matchSelList_scope_irrelevant
  Dom.matchesSelector_eq
  Dom.mem_matchTree_iff_matches
