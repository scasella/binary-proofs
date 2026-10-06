needs "/work/development/approved-plan/crypto-loop/trace/control/scalar-statements.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/safety-algebra.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/run-scalar.ml";;
let CRYPTO_CONTROL_LOOP_SCALAR = prove
 (crypto_control_loop_scalar_statement,
  INDUCT_TAC THENL [REWRITE_TAC[LT];ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `word_sub(word(SUC n))(word 1):int64=word n` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(ARITH_RULE `SUC n-1=n`)] THEN
    SIMP_TAC[WORD_SUB;ARITH_RULE `1<=SUC n`];ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64)=0 <=> n=0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
  SUBGOAL_THEN `assurance_span_ok rp (val(p:int64)) 1 /\
                assurance_span_ok rp (val(q:int64)) 1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CRYPTO_CONTROL_SPAN_HEAD THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `n=0` THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_CONTROL_RUN_SCALAR_STEP_TAC `SUC n` offset ASSURANCE_CRYPTO_EXEC sname)
   [64,"c1";67,"c2";71,"c3";74,"c4";78,"c5";81,"c6";84,"c7"] THEN
  REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(7*SUC n+3)-7=7*n+3`] THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY(fun(offset,sname)->CRYPTO_CONTROL_RUN_SCALAR_STEP_TAC `SUC n` offset ASSURANCE_CRYPTO_EXEC sname)
     [86,"c8";89,"c9";93,"c10"] THEN
    REWRITE_TAC[assurance_checked_run;ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[assurance_checked_run];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `word_add (p:int64) (word 1)` THEN EXISTS_TAC `word_add (q:int64) (word 1)` THEN
    ASM_SIMP_TAC[ARITH_RULE `0<n <=> ~(n=0)`;CRYPTO_CONTROL_SPAN_TAIL]]);;
print_endline "CRYPTO_CONTROL_LOOP_SCALAR_COMPLETE";;
