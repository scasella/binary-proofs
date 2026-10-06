(* New helper literals separately frozen in supplement-freeze-v2.json. *)
let CW_INDEX_VALUE = prove
 (cw_index_value_statement,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i<2 EXP 64 /\ val(p:int64)+i<2 EXP 64`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT]);;
let CW_EXTERNAL_POINT = prove
 (cw_external_point_statement,
  REWRITE_TAC[cw_external;fb_immutable;c1_immutable;
    assurance_region;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let CW_EXTERNAL_PERMISSIONS = prove
 (cw_external_permissions_statement,
  REWRITE_TAC[cw_external;cw_read;cw_write;cw_ordinary;
    lw_image_domain;c1_image_domain] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;
let CW_LAYOUT_POINT = prove
 (cw_layout_point_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[cw_layout;assurance_span_ok]
    (ASSUME `cw_layout (p:int64) q n k different`)) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `val(word_add (p:int64) (word i))=val p+i /\
    val(word_add (q:int64) (word i))=val q+i`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CW_INDEX_VALUE THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
