(* Universal single-iteration helper for production CRYPTO_memcmp bytes. *)
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/statements.ml";;
needs "/work/proofs/implementations/crypto_register_helpers.ml";;
let CRYPTO_BOUNDED_ITERATION = prove
 (crypto_bounded_iteration_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub(word k)(word 1):int64=word(k-1)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB;ARITH_RULE `0<k ==> 1<=k`];ALL_TAC] THEN
  SUBGOAL_THEN `k-1<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst CRYPTO_MEMCMP_EXEC] THEN
  GHOST_INTRO_TAC `r10init:int64` `read R10` THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `val(r10init:int64)<256` ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  X86_VSTEPS_TAC CRYPTO_MEMCMP_EXEC (1--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[APPEND] THEN
  ASM_SIMP_TAC[CRYPTO_HIGH8_56_ZERO;CRYPTO_JOIN_ZERO56_BYTE;
    CRYPTO_ZX_BYTE_HIGH_ZERO;CRYPTO_ZX_BYTE_LOW;CRYPTO_ZX_BYTE_BOUND] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[VAL_EQ_0;WORD_SUB_EQ_0;GSYM VAL_EQ;VAL_WORD;
    DIMINDEX_64;MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WORD_SUB;ARITH_RULE `0<k ==> 1<=k`;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  POP_ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC
   (filter(fun th -> vfree_in `k:num` (concl th) &&
     not(exists(fun v -> type_of v = `:x86state`) (frees(concl th)))) ths)) THEN
  ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC);;
