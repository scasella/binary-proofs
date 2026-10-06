let CW_IMAGE_PERMISSIONS = prove
 (cw_image_permissions_statement,
  REWRITE_TAC[cw_read;cw_write;cw_execute;cw_ordinary;
    assurance_canonical48;lw_image_domain;lw_image_write;lw_execute;
    lw_image_execute;c1_image_domain;
    c1_image_write;c1_image_execute] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC ORELSE GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;
let CW_FIXED_SPANS = prove
 (cw_fixed_spans_statement,
  REWRITE_TAC[assurance_span_ok;cw_read;cw_write;cw_execute;cw_ordinary;
    assurance_canonical48;lw_image_domain;lw_image_write;lw_execute;
    lw_image_execute;c1_image_domain;
    c1_image_write;c1_image_execute] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONJ_TAC ORELSE GEN_TAC ORELSE DISCH_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let CW_LAYOUT_PERMISSIONS = prove
 (cw_layout_permissions_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[cw_layout;assurance_span_ok]) THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[assurance_span_ok] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CW_EXTERNAL_PERMISSIONS];
    REWRITE_TAC[assurance_span_ok] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CW_EXTERNAL_PERMISSIONS];
    REWRITE_TAC[assurance_region;c1_call_slot;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_MESON_TAC[cw_external;
     ARITH_RULE `!(base:num) a n. base<=a /\ a<base+n ==> a-base<n /\ base+(a-base)=a`;
     ARITH_RULE `!a:num. 0x50000000<=a ==> ~(a<0x300000)`];
    REWRITE_TAC[assurance_region;c1_call_slot;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_MESON_TAC[cw_external;
     ARITH_RULE `!(base:num) a n. base<=a /\ a<base+n ==> a-base<n /\ base+(a-base)=a`;
     ARITH_RULE `!a:num. 0x50000000<=a ==> ~(a<0x300000)`]]);;
let CW_SEVEN_LAYOUTS = prove
 (cw_seven_layouts_statement,
  REWRITE_TAC[cw_layout;assurance_span_ok;cw_external;
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
   ARITH_RULE `i<15 ==> 1610616831+i<18446744073709551616`;
   ARITH_RULE `i<1 ==> 18446603336221196288+i<18446744073709551616`] THEN
  ASM_ARITH_TAC);;
