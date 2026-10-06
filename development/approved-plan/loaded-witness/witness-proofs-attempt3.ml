(* Attempt3 imports helpers-attempt4.ml; earlier helper/proof recipes retained. *)
(* Recipe over the identical scalar E2 Pre. Conditional reference families
   are never relabeled acquired concrete full-image witnesses. *)

let LW_PRE_TAC =
  REWRITE_TAC[lw_pre; bp_e2_crypto_pre] THEN
  ASM_SIMP_TAC[LW_CODE_LOADED; LW_LAYOUT_EMPTY; LW_CASE_LAYOUT; LW_ZERO_SPAN] THEN
  REWRITE_TAC[lw_state; C_ARGUMENTS; RSP; RDI; RSI; RDX; DF;
    READ_COMPONENT_COMPOSE; READ_ELEMENT; x86state_COMPONENTS;
    LW_RETURN_SLOT; lw_read; lw_execute; lw_ordinary; lw_image_read;
    lw_image_domain; lw_image_execute; lw_overlay_domain; lw_pagecover;
    assurance_span_ok; assurance_canonical48; assurance_region; READ_BITELEMENT] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN ARITH_TAC;;

let LW_IMAGE_TAC =
  MATCH_MP_TAC LW_PRESERVES_IMAGE THEN
  REWRITE_TAC[LW_LAYOUT_EMPTY; LW_CASE_LAYOUT];;

let LW_EMPTY_FAMILY = prove
 (lw_empty_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_EQUAL_MISALIGNED_FAMILY = prove
 (lw_equal_misaligned_statement,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [LW_PRE_TAC;
    LW_IMAGE_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[lw_memory; lw_overlay_domain; lw_pagecover;
      GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT;
      ARITH_RULE `i<17 ==> 2097153+i<18446744073709551616`;
      ARITH_RULE `i<17 ==> 2097217+i<18446744073709551616`] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LW_UNEQUAL_FAMILY = prove
 (lw_unequal_statement,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [LW_PRE_TAC;
    LW_IMAGE_TAC;
    REWRITE_TAC[lw_memory; lw_overlay_domain; lw_pagecover] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[lw_memory; lw_overlay_domain; lw_pagecover] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV]);;

let LW_IDENTICAL_FAMILY = prove
 (lw_identical_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_OVERLAP_FAMILY = prove
 (lw_overlap_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_FASTPATH_FAMILY = prove
 (lw_fastpath_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_LOW_CANONICAL_EDGE_FAMILY = prove
 (lw_low_canonical_edge_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_TOP_EDGE_FAMILY = prove
 (lw_top_edge_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;

let LW_USER_PAGE_BOUNDARY_FAMILY = prove
 (lw_page_boundary_statement,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [LW_PRE_TAC; LW_IMAGE_TAC]);;
