(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)
(* New helper literals separately frozen in supplement-freeze-v2.json. *)
let C2W_INDEX_VALUE = prove
 (c2w_index_value_statement,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i<2 EXP 64 /\ val(p:int64)+i<2 EXP 64`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT]);;
let C2W_EXTERNAL_POINT = prove
 (c2w_external_point_statement,
  REWRITE_TAC[c2w_external;fb_immutable;c2_immutable;
    assurance_region;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2W_EXTERNAL_PERMISSIONS = prove
 (c2w_external_permissions_statement,
  REWRITE_TAC[c2w_external;c2w_read;c2w_write;c2w_ordinary;
    lw_image_domain;c2_image_domain] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;
let C2W_LAYOUT_POINT = prove
 (c2w_layout_point_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[c2w_layout;assurance_span_ok]
    (ASSUME `c2w_layout (p:int64) q n k different`)) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `val(word_add (p:int64) (word i))=val p+i /\
    val(word_add (q:int64) (word i))=val q+i`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC C2W_INDEX_VALUE THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
