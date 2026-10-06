needs "/work/development/approved-plan/crypto-loop/generic-return-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/callable-statements.ml";;
needs "/work/development/approved-plan/byte-contract/fastpath_attempt3.ml";;
let CRYPTO_MEMCMP_ALL_LENGTH_MODELED_RETURN = prove
 (crypto_dev_callable_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n=0` THENL
   [GHOST_INTRO_TAC `e:uarch_event list` `read events` THEN
    MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
      `p:int64`;`q:int64`;`e:uarch_event list`] CRYPTO_MEMCMP_ZERO_RETURN) THEN
    ASM_REWRITE_TAC[LT;SOME_FLAGS] THEN
    ENSURES_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst CRYPTO_MEMCMP_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n=16` THENL
   [GHOST_INTRO_TAC `e:uarch_event list` `read events` THEN
    MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
      `p:int64`;`q:int64`;`m:int64->byte`;`e:uarch_event list`]
      BP_CRYPTO_MEMCMP_16_BYTES_RETURN) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `0<n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
    `p:int64`;`q:int64`;`n:num`;`m:int64->byte`] CRYPTO_MEMCMP_GENERIC_MODELED_RETURN) THEN
  ASM_REWRITE_TAC[]);;
print_endline "CRYPTO_DEV_CALLABLE_COMPLETE";;
