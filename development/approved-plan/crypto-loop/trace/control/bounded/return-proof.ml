needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/core-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/statements.ml";;
let CRYPTO_BOUNDED_GENERIC_RETURN = prove
 (crypto_bounded_generic_return_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst CRYPTO_MEMCMP_EXEC] THEN
  ENSURES_N_SEQUENCE_TAC `pc+93`
   `\s. read RSP s=stackpointer /\
         read (memory :> bytes64 stackpointer) s=returnaddress /\
         read memory s=m /\ read RAX s=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                     then word 0 else word 1) /\
         read events s=APPEND (crypto_trace_prefix pc p q n n)
          (APPEND [EventJump(word(pc+22),word(pc+64));EventJump(word(pc+16),word(pc+16))] e)` `7*n+9` `1` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`e:uarch_event list`]
      CRYPTO_BOUNDED_GENERIC_CORE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
    CRYPTO_ENSURES_N_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst CRYPTO_MEMCMP_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[];
    X86_SIM_TAC CRYPTO_MEMCMP_EXEC [1] THEN
    ASM_SIMP_TAC[crypto_trace_call;ARITH_RULE `0<n ==> ~(n=0)`;APPEND_ASSOC;APPEND];ARITH_TAC]);;
print_endline "CRYPTO_DEV_GENERIC_RETURN_COMPLETE";;
