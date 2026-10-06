needs "/work/development/approved-plan/cleanse/access/imports-v1.ml";;
let CLEANSE_ACCESS_CODE_OFFSET_VALUE = prove
 (`!pc off. pc+97<=2 EXP 64 /\ off<97
    ==> val(word(pc+off):int64)=pc+off`,
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let CLEANSE_ACCESS_CODE_BASE_VALUE = prove
 (`!pc. pc+97<=2 EXP 64 ==> val(word pc:int64)=pc`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`pc:num`;`0`] CLEANSE_ACCESS_CODE_OFFSET_VALUE) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES;ARITH_RULE `0<97`]);;
let CLEANSE_ACCESS_SPAN_HEAD = prove
 (`!wp p n width. assurance_span_ok wp (val(p:int64)) n /\ width<=n
    ==> assurance_span_ok wp (val p) width`,
  MESON_TAC[ASSURANCE_SPAN_PREFIX]);;
let CLEANSE_ACCESS_SPAN_TAIL = prove
 (`!wp p n off. assurance_span_ok wp (val(p:int64)) n /\ off<=n
    ==> assurance_span_ok wp (val(word_add p (word off))) (n-off)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `(off:num)=(n:num)` THENL
   [ASM_REWRITE_TAC[SUB_REFL;assurance_span_ok;ADD_CLAUSES;LT] THEN
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_ACCEPT_TAC VAL_BOUND_64;
    SUBGOAL_THEN `off<2 EXP 64 /\ val(p:int64)+off<2 EXP 64` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[assurance_span_ok]) THEN ASM_ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add (p:int64) (word off))=val p+off` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
    MATCH_MP_TAC ASSURANCE_SPAN_SUBRANGE THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
let CLEANSE_ACCESS_NONOVERLAP_TAIL = prove
 (`!base width p n off count.
    nonoverlapping (base:int64,width) (p,n) /\ off+count<=n
    ==> nonoverlapping (base,width) (word_add p (word off),count)`,
  REPEAT STRIP_TAC THEN NONOVERLAPPING_TAC);;
print_endline "CLEANSE_ACCESS_ALGEBRA_ATTEMPT3_COMPLETE";;
