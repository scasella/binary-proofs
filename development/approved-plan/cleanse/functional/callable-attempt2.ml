needs "/work/development/approved-plan/cleanse/functional/core-attempt6.ml";;
let OPENSSL_CLEANSE_FUNCTIONAL_CALLABLE = prove
 (cleanse_functional_callable_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst OPENSSL_CLEANSE_EXEC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC
   `\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
        read RSP s=stackpointer /\ read(memory :> bytes64 stackpointer)s=ra /\
        (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
        read(memory :> bytes(p,n))s=0` THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;ALL_TAC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`p:int64`;`n:num`] OPENSSL_CLEANSE_FUNCTIONAL_CORE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
    ENSURES_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst OPENSSL_CLEANSE_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    DISJ_CASES_TAC(ASSUME `read RIP s0=word(pc+31) \/ read RIP s0=word(pc+95)`) THEN
    X86_STEPS_TAC OPENSSL_CLEANSE_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;
print_endline "CLEANSE_FUNCTIONAL_CALLABLE_ATTEMPT2_COMPLETE";;
