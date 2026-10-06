(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)
let C2W_IMAGE_PERMISSIONS = prove
 (c2w_image_permissions_statement,
  REWRITE_TAC[c2w_read;c2w_write;c2w_execute;c2w_ordinary;
    assurance_canonical48;lw_image_domain;lw_image_write;lw_execute;
    lw_image_execute;c2_image_domain;
    c2_image_write;c2_image_execute] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC ORELSE GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;
let C2W_FIXED_SPANS = prove
 (c2w_fixed_spans_statement,
  REWRITE_TAC[assurance_span_ok;c2w_read;c2w_write;c2w_execute;c2w_ordinary;
    assurance_canonical48;lw_image_domain;lw_image_write;lw_execute;
    lw_image_execute;c2_image_domain;
    c2_image_write;c2_image_execute] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC ORELSE GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let C2W_LAYOUT_PERMISSIONS = prove
 (c2w_layout_permissions_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c2w_layout;assurance_span_ok]) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[assurance_span_ok] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[C2W_EXTERNAL_PERMISSIONS];
    REWRITE_TAC[assurance_span_ok] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[C2W_EXTERNAL_PERMISSIONS];
    REWRITE_TAC[assurance_span_ok] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[C2W_EXTERNAL_PERMISSIONS];
    REWRITE_TAC[assurance_region;c2_scratch;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `addr-val(p:int64)`
      (ASSUME `!j:num. j<n ==> assurance_canonical48(val(p:int64)+j) /\
        c2w_external(val(p:int64)+j)`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `p<=a ==> p+(a-p)=a`] THEN
    REWRITE_TAC[c2w_external] THEN STRIP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[assurance_region;c2_scratch;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `addr-val(q:int64)`
      (ASSUME `!j:num. j<n ==> assurance_canonical48(val(q:int64)+j) /\
        c2w_external(val(q:int64)+j)`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `p<=a ==> p+(a-p)=a`] THEN
    REWRITE_TAC[c2w_external] THEN STRIP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[assurance_region;c2_scratch;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `addr-val(p:int64)`
      (ASSUME `!j:num. j<n ==> assurance_canonical48(val(p:int64)+j) /\
        c2w_external(val(p:int64)+j)`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `p<=a ==> p+(a-p)=a`] THEN
    REWRITE_TAC[c2w_external] THEN STRIP_TAC THEN ASM_ARITH_TAC]);;
let C2W_EIGHT_LAYOUTS = prove
 (c2w_eight_layouts_statement,
  REWRITE_TAC[c2w_layout;assurance_span_ok;c2w_external;
    assurance_canonical48;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ;VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
   ARITH_RULE `i<17 ==> i<18446744073709551616`;
   ARITH_RULE `i<15 ==> i<18446744073709551616`;
   ARITH_RULE `i<1 ==> i<18446744073709551616`;
   ARITH_RULE `i<17 ==> 1610612741+i<18446744073709551616`;
   ARITH_RULE `i<17 ==> 1342177284+i<18446744073709551616`;
   ARITH_RULE `i<15 ==> 1610616831+i<18446744073709551616`;
   ARITH_RULE `i<1 ==> 18446603336221196288+i<18446744073709551616`] THEN
  ASM_ARITH_TAC);;
