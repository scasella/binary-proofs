needs "/work/development/approved-plan/crypto-loop/trace/noninterference/loop-proof.ml";;
let CRYPTO_OBSERVATION_CALLABLE = prove
 (crypto_observation_callable_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n=0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[crypto_public_call;crypto_public_entry5;APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `0` offset CRYPTO_MEMCMP_EXEC sname)
     [0,"z1";4,"z2";7,"z3";10,"z4";14,"z5";93,"z6"] THEN
    REWRITE_TAC[crypto_observed_run] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n=16` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[crypto_public_call;crypto_public_entry7;crypto_public_entry5;APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `16` offset CRYPTO_MEMCMP_EXEC sname)
     [0,"f1";4,"f2";7,"f3";10,"f4";14,"f5";16,"f6";20,"f7";
      22,"f8";25,"f9";29,"f10";36,"f11";39,"f12";43,"f13";46,"f14";50,"f15"] THEN
    REWRITE_TAC[crypto_observed_run] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0<n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~((word n:int64)=word 0) /\ ~((word n:int64)=word 16)`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VAL_EQ;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_sub(word n)(word 0):int64)=0) /\
                ~(val(word_sub(word n)(word 16):int64)=0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0;WORD_SUB_EQ_0];ALL_TAC] THEN
  ASM_REWRITE_TAC[crypto_public_call;crypto_public_entry7;crypto_public_entry5;APPEND] THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_OBS_STEP_TAC `n:num` offset CRYPTO_MEMCMP_EXEC sname)
   [0,"g1";4,"g2";7,"g3";10,"g4";14,"g5";16,"g6";20,"g7"] THEN
  MATCH_MP_TAC(ISPECL [`n:num`;`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
    `p:int64`;`q:int64`;`m:int64->byte`;`g7:x86state`] CRYPTO_OBSERVATION_LOOP) THEN
  ASM_REWRITE_TAC[]);;
print_endline "CRYPTO_OBSERVATION_CALLABLE_COMPLETE";;
