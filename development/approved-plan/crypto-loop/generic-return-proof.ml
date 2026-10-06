needs "/work/development/approved-plan/crypto-loop/generic-core-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/generic-return-statement.ml";;
let CRYPTO_MEMCMP_GENERIC_MODELED_RETURN = prove
 (crypto_dev_generic_return_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst CRYPTO_MEMCMP_EXEC] THEN
  ENSURES_SEQUENCE_TAC `pc+93`
   `\s. read RSP s=stackpointer /\
         read (memory :> bytes64 stackpointer) s=returnaddress /\
         read memory s=m /\ read RAX s=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                     then word 0 else word 1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
      CRYPTO_MEMCMP_GENERIC_CORE_CORRECT) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
    ENSURES_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst CRYPTO_MEMCMP_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[];
    X86_SIM_TAC CRYPTO_MEMCMP_EXEC [1]]);;
print_endline "CRYPTO_DEV_GENERIC_RETURN_COMPLETE";;
