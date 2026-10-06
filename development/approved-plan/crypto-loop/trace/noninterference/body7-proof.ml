needs "/work/development/approved-plan/contract/crypto-pre-v2.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/exec-rule.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/step-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/statements.ml";;
let CRYPTO_OBSERVATION_BODY7 = prove
 (crypto_observation_body7_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub(word count)(word 1):int64=word(count-1)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB;ARITH_RULE `0<count ==> 1<=count`];ALL_TAC] THEN
  SUBGOAL_THEN `count-1<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `val(word(count-1):int64)=0 <=> count=1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `count=1` THEN REWRITE_TAC[crypto_public_body7] THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `count:num` offset CRYPTO_MEMCMP_EXEC sname)
   [64,"o1";67,"o2";71,"o3";74,"o4";78,"o5";81,"o6";84,"o7"] THEN
  REWRITE_TAC[crypto_observed_run] THEN ASM_REWRITE_TAC[]);;
print_endline "CRYPTO_OBSERVATION_BODY7_COMPLETE";;
