(* Conservative recipes over the frozen full-binding V2 targets. Requires
   frozen loaded-witness V3 (helpers-attempt4 / witness-proofs-attempt3) and
   state-v4.ml. No axiom, ISA change, loader execution or target invariant. *)

let FB_REFERENCE_SATISFIES = prove
 (fb_reference_satisfies_statement,
  REWRITE_TAC[fb_full_image]);;

let FB_IMAGE_PRESERVATION = prove
 (fb_image_preservation_statement,
  MESON_TAC[fb_full_image; LW_PRESERVES_IMAGE]);;

let FB_CODE_CORRESPONDENCE = prove
 (fb_code_correspondence_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[lw_reference_code] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `file_bytes(0x241840+i) = EL i crypto_memcmp_mc`
    ASSUME_TAC THENL
   [MP_TAC(SPEC `i:num` (REWRITE_RULE[fb_file_code]
      (ASSUME `fb_file_code (file_bytes:num->byte)`))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `fb_immutable (0x10241840+i)` ASSUME_TAC THENL
   [REWRITE_TAC[fb_immutable] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `word(0x10241840+i):int64` (REWRITE_RULE[fb_full_image]
    (ASSUME `fb_full_image file_bytes initial_rw padding (image:int64->byte)`))) THEN
  ASM_SIMP_TAC[LW_CODE_VALUE; LW_CODE_IN_IMAGE; fb_reference_image;
    ARITH_RULE `(0x10241840+(i:num))-0x10000000 = 0x241840+i`]);;

let FB_FULL_IMAGE_EXISTS = prove
 (fb_full_image_exists_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `fb_reference_image file_bytes initial_rw padding` THEN
  ASM_MESON_TAC[FB_REFERENCE_SATISFIES; FB_CODE_CORRESPONDENCE]);;

let FB_VALID_ABI = prove
 (fb_valid_abi_statement,
  REWRITE_TAC[fb_abi_initial_fields; fb_initial_abi;
    abi_omitted_state_COMPONENTS; fb_tls_page; assurance_canonical48] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let FB_MACHINE_MEMORY = prove
 (`!image p q n different.
    read memory (lw_state image p q n different) =
      lw_memory image p q n different`,
  REWRITE_TAC[lw_state; x86state_COMPONENTS]);;

let FB_TLS_ENVIRONMENT = prove
 (`!p q n a. fb_tls_page a ==> fb_read p q n a /\ fb_ordinary p q n a`,
  REWRITE_TAC[fb_read; fb_ordinary] THEN MESON_TAC[]);;

let FB_SCALAR_PRE_LIFT = prove
 (`!image p q n different.
    lw_pre image p q n different
    ==> bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (fb_read p q n) lw_execute
      (fb_ordinary p q n) (lw_state image p q n different)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lw_pre; bp_e2_crypto_pre] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[fb_read; fb_ordinary; assurance_span_ok] THEN
  ASM_MESON_TAC[assurance_span_ok]);;

let FB_PRE_LIFT = prove
 (fb_pre_lift_statement,
  REWRITE_TAC[fb_pre; fb_machine; FST; SND; FB_MACHINE_MEMORY] THEN
  MESON_TAC[FB_IMAGE_PRESERVATION; FB_SCALAR_PRE_LIFT;
            FB_VALID_ABI; FB_TLS_ENVIRONMENT]);;

let FB_EMPTY_FAMILY = prove
 (fb_empty_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_EMPTY_FAMILY; LW_LAYOUT_EMPTY]);;

let FB_EQUAL_MISALIGNED_FAMILY = prove
 (fb_equal_misaligned_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_EQUAL_MISALIGNED_FAMILY; LW_CASE_LAYOUT]);;

let FB_UNEQUAL_FAMILY = prove
 (fb_unequal_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_UNEQUAL_FAMILY; LW_CASE_LAYOUT]);;

let FB_IDENTICAL_FAMILY = prove
 (fb_identical_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_IDENTICAL_FAMILY; LW_CASE_LAYOUT]);;

let FB_OVERLAP_FAMILY = prove
 (fb_overlap_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_OVERLAP_FAMILY; LW_CASE_LAYOUT]);;

let FB_FASTPATH_FAMILY = prove
 (fb_fastpath_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_FASTPATH_FAMILY; LW_CASE_LAYOUT]);;

let FB_LOW_CANONICAL_EDGE_FAMILY = prove
 (fb_low_canonical_edge_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_LOW_CANONICAL_EDGE_FAMILY; LW_CASE_LAYOUT]);;

let FB_TOP_EDGE_FAMILY = prove
 (fb_top_edge_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_TOP_EDGE_FAMILY; LW_CASE_LAYOUT]);;

let FB_USER_PAGE_BOUNDARY_FAMILY = prove
 (fb_page_boundary_statement,
  MESON_TAC[FB_CODE_CORRESPONDENCE; FB_PRE_LIFT;
            LW_USER_PAGE_BOUNDARY_FAMILY; LW_CASE_LAYOUT]);;

let FB_MACHINE_WITNESS_EXISTS = prove
 (fb_machine_witness_exists_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `fb_reference_image file_bytes initial_rw padding` THEN
  ASM_SIMP_TAC[FB_REFERENCE_SATISFIES; FB_EMPTY_FAMILY;
    FB_EQUAL_MISALIGNED_FAMILY; FB_UNEQUAL_FAMILY; FB_IDENTICAL_FAMILY;
    FB_OVERLAP_FAMILY; FB_FASTPATH_FAMILY; FB_LOW_CANONICAL_EDGE_FAMILY;
    FB_TOP_EDGE_FAMILY; FB_USER_PAGE_BOUNDARY_FAMILY]);;
