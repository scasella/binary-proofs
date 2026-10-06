needs "/work/development/approved-plan/crypto-loop/trace/control/loop-scalar-proof.ml";;
let CRYPTO_CONTROL_GENERIC_SCALAR = prove
 (crypto_control_generic_scalar_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n=0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~((word n:int64)=word 0) /\ ~((word n:int64)=word 16)`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VAL_EQ;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word_sub(word n)(word 0):int64)=0) /\
                ~(val(word_sub(word n)(word 16):int64)=0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0;WORD_SUB_EQ_0];ALL_TAC] THEN
  MAP_EVERY(fun(offset,sname)->CRYPTO_CONTROL_RUN_SCALAR_STEP_TAC `n:num`
    offset ASSURANCE_CRYPTO_EXEC sname)
   [0,"g1";4,"g2";7,"g3";10,"g4";14,"g5";16,"g6";20,"g7"] THEN
  REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(7*n+10)-7=7*n+3`] THEN
  MATCH_MP_TAC(ISPECL [`n:num`;`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
    `p:int64`;`q:int64`;`m:int64->byte`;`rp:num->bool`;`xp:num->bool`;`g7:x86state`]
    CRYPTO_CONTROL_LOOP_SCALAR) THEN ASM_REWRITE_TAC[]);;
print_endline "CRYPTO_CONTROL_GENERIC_SCALAR_COMPLETE";;
