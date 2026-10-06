needs "/work/development/approved-plan/crypto-loop/trace/noninterference/body7-proof.ml";;
let CRYPTO_OBSERVATION_LOOP = prove
 (crypto_observation_loop_statement,
  INDUCT_TAC THENL [REWRITE_TAC[LT];ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `word_sub(word(SUC n))(word 1):int64=word n` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(ARITH_RULE `SUC n-1=n`)] THEN
    SIMP_TAC[WORD_SUB;ARITH_RULE `1<=SUC n`];ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64)=0 <=> n=0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
  ASM_CASES_TAC `n=0` THEN
  REWRITE_TAC[crypto_public_loop;crypto_public_body7;APPEND] THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `SUC n` offset CRYPTO_MEMCMP_EXEC sname)
   [64,"l1";67,"l2";71,"l3";74,"l4";78,"l5";81,"l6";84,"l7"] THENL
   [ASM_REWRITE_TAC[crypto_public_loop;crypto_public_exit] THEN
    MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `SUC n` offset CRYPTO_MEMCMP_EXEC sname)
     [86,"l8";89,"l9";93,"l10"] THEN
    REWRITE_TAC[crypto_observed_run] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `0<n <=> ~(n=0)`]]);;
print_endline "CRYPTO_OBSERVATION_LOOP_COMPLETE";;
