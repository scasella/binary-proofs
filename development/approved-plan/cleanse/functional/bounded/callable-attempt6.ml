needs "/work/development/approved-plan/cleanse/functional/bounded/core-attempt6.ml";;
let OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CALLABLE = prove
 (cleanse_functional_bounded_callable_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `0<cleanse_functional_steps (p:int64) n` ASSUME_TAC THENL
   [REWRITE_TAC[cleanse_functional_steps;LET_DEF;LET_END_DEF] THEN COND_CASES_TAC THEN ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `cleanse_functional_steps (p:int64) n=(cleanse_functional_steps p n-1)+1` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV)
   [ASSUME `cleanse_functional_steps (p:int64) n=(cleanse_functional_steps p n-1)+1`] THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS;fst OPENSSL_CLEANSE_EXEC] THEN
  MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN
  EXISTS_TAC
   `\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
        read RSP s=stackpointer /\ read(memory :> bytes64 stackpointer)s=ra /\
        (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
        read(memory :> bytes(p,n))s=0` THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;ALL_TAC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`p:int64`;`n:num`] OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CORE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
    CLEANSE_ENSURES_N_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst OPENSSL_CLEANSE_EXEC)) "s0" "s1" THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    DISJ_CASES_TAC(ASSUME `read RIP s0=word(pc+31) \/ read RIP s0=word(pc+95)`) THEN
    X86_STEPS_TAC OPENSSL_CLEANSE_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;
print_endline "CLEANSE_FUNCTIONAL_BOUNDED_CALLABLE_ATTEMPT6_COMPLETE";;
