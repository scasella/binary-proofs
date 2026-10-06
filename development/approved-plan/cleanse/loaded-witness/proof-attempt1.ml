(* First candidate witness recipes; exact statements frozen independently. *)
let CLW_PRE_TAC =
  REWRITE_TAC[clw_scalar_pre;bp_e2_cleanse_pre] THEN
  ASM_SIMP_TAC[CLW_CODE_LOADED;CLW_LAYOUT_EMPTY;CLW_CASE_LAYOUT;LW_ZERO_SPAN] THEN
  REWRITE_TAC[clw_state;C_ARGUMENTS;RSP;RDI;RSI;DF;
    READ_COMPONENT_COMPOSE;READ_ELEMENT;x86state_COMPONENTS;
    CLW_RETURN_SLOT;clw_read;clw_write;clw_ordinary;fb_read;fb_ordinary;
    fb_tls_page;lw_read;lw_ordinary;lw_execute;lw_image_read;lw_image_write;
    lw_image_domain;lw_image_execute;lw_overlay_domain;lw_pagecover;
    assurance_span_ok;assurance_canonical48;assurance_region;READ_BITELEMENT] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN ARITH_TAC;;
let CLW_EMPTY_FAMILY = prove
 (clw_empty_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `clw_reference_code image` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLW_CODE_CORRESPONDENCE];ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLW_FULL_PRE_LIFT THEN
    ASM_REWRITE_TAC[CLW_LAYOUT_EMPTY] THEN CLW_PRE_TAC;
    REWRITE_TAC[lw_pagecover]]);;
let CLW_BYTE_ONE_FAMILY = prove
 (clw_byte_one_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `clw_reference_code image` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLW_CODE_CORRESPONDENCE];ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLW_FULL_PRE_LIFT THEN
    ASM_REWRITE_TAC[CLW_CASE_LAYOUT] THEN CLW_PRE_TAC;
    REWRITE_TAC[clw_memory;lw_memory;lw_overlay_domain;lw_pagecover] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV]);;
