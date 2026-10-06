needs "/work/development/approved-plan/cleanse/functional/bounded/byte-attempt1.ml";;
needs "/work/development/approved-plan/cleanse/functional/bounded/bulk-attempt1.ml";;
needs "/work/development/approved-plan/cleanse/functional/bounded/sublemma-tactic-v1.ml";;
needs "/work/development/approved-plan/cleanse/functional/composition-algebra-attempt1.ml";;
let OPENSSL_CLEANSE_BOUNDED_BULK_TAIL = prove
 (cleanse_functional_bounded_bulk_tail_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (word pc:int64,97) (p,8*k)` ASSUME_TAC THENL
   [NONOVERLAPPING_TAC;ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS;fst OPENSSL_CLEANSE_EXEC] THEN
  ENSURES_N_SEQUENCE_TAC `pc+89`
   `\s. read RDI s=word_add p (word(8*k)) /\ read RSI s=word r /\
         read RAX s=word 0 /\ read(memory :> bytes(p,8*k))s=0` `5*k` `4*r+2` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`p:int64`;`k:num`;`r:num`] OPENSSL_CLEANSE_BOUNDED_BULK_LOOP) THEN
    ASM_REWRITE_TAC[SOME_FLAGS] THEN
    MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;ALL_TAC] THEN
    REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE;SEQ_ID;GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM;LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN NONSELFMODIFYING_STATE_UPDATE_TAC
      (MATCH_MP bytes_loaded_update (fst OPENSSL_CLEANSE_EXEC)) THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `r=0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      X86_SIM_TAC OPENSSL_CLEANSE_EXEC (1--2) THEN ASM_REWRITE_TAC[ADD_0];ALL_TAC] THEN
    SUBGOAL_THEN `0<r /\ r<2 EXP 64 /\
      nonoverlapping (word pc:int64,97) (word_add p (word(8*k)),r)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN NONOVERLAPPING_TAC;ALL_TAC] THEN
    ENSURES_N_SEQUENCE_TAC `pc+19`
     `\s. read RDI s=word_add p (word(8*k)) /\ read RSI s=word r /\
           read RAX s=word 0 /\ read(memory :> bytes(p,8*k))s=0` `2` `4*r` THEN
    REPEAT CONJ_TAC THENL
     [X86_SIM_TAC OPENSSL_CLEANSE_EXEC (1--2) THEN
      ASM_SIMP_TAC[VAL_WORD_0;VAL_WORD;DIMINDEX_64;MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`pc:num`;`word_add p (word(8*k)):int64`;`r:num`]
        OPENSSL_CLEANSE_BOUNDED_BYTE_LOOP) THEN ASM_REWRITE_TAC[SOME_FLAGS] THEN
      CLEANSE_ENSURES_N_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst OPENSSL_CLEANSE_EXEC)) "s0" "s1" THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC;GSYM WORD_ADD] THEN
      MATCH_MP_TAC CLEANSE_FUNCTIONAL_CONCAT_ZERO THEN ASM_REWRITE_TAC[];
      ARITH_TAC];
    ARITH_TAC]);;
print_endline "CLEANSE_FUNCTIONAL_BOUNDED_BULK_TAIL_ATTEMPT1_COMPLETE";;
