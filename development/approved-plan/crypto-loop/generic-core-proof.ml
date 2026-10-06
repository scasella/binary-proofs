needs "/work/development/approved-plan/crypto-loop/loop-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/callable-statements.ml";;
let CRYPTO_MEMCMP_GENERIC_CORE_CORRECT = prove
 (crypto_dev_generic_core_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((word n:int64)=word 0) /\ ~((word n:int64)=word 16)`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VAL_EQ;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
   `~(val(word_sub (word n) (word 0):int64)=0) /\
    ~(val(word_sub (word n) (word 16):int64)=0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0;WORD_SUB_EQ_0];ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst CRYPTO_MEMCMP_EXEC] THEN
  ENSURES_SEQUENCE_TAC `pc+64`
   `\s. read RDI s=p /\ read RSI s=q /\ read RDX s=word n /\
         read RAX s=word 0 /\ read R10 s=word 0 /\ read memory s=m` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC CRYPTO_MEMCMP_EXEC (1--7) THEN
    ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT;WORD_EQ;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL [`pc:num`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
      CRYPTO_MEMCMP_BYTE_LOOP_CORRECT) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst CRYPTO_MEMCMP_EXEC;CONJ_ASSOC]]);;
print_endline "CRYPTO_DEV_GENERIC_CORE_COMPLETE";;
