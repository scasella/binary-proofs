needs "/work/development/approved-plan/crypto-loop/trace/control/body-statements.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/body-policy.ml";;
let CRYPTO_CONTROL_BODY7 = prove
 (crypto_control_body7_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub(word count)(word 1):int64=word(count-1)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB;ARITH_RULE `0<count ==> 1<=count`];ALL_TAC] THEN
  SUBGOAL_THEN `count-1<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `val(word(count-1):int64)=0 <=> count=1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `count=1` THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_CONTROL_STEP_TAC offset ASSURANCE_CRYPTO_EXEC sname)
   [64,"b1";67,"b2";71,"b3";74,"b4";78,"b5";81,"b6";84,"b7"] THEN
  REWRITE_TAC[assurance_checked_run] THEN ASM_REWRITE_TAC[APPEND]);;
print_endline "CRYPTO_CONTROL_BODY7_COMPLETE";;
