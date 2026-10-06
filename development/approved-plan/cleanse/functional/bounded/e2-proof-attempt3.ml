needs "/work/development/approved-plan/cleanse/functional/bounded/callable-attempt6.ml";;
needs "/work/development/approved-plan/cleanse/functional/bounded/e2-statements-v1.ml";;
needs "/work/development/approved-plan/cleanse/functional/frame-proof-attempt3.ml";;
let BP_E2_CLEANSE_BOUNDED_FUNCTIONAL_RETURN = prove
 (cleanse_functional_e2_bounded_statement,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[bp_e2_cleanse_pre] THEN GLOBALIZE_PRECONDITION_TAC THEN
  SUBGOAL_THEN `val(p:int64)+n<=2 EXP 64` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(REWRITE_RULE[assurance_span_ok]
      (ASSUME `assurance_span_ok (\a. (wp:num->bool) a /\ (ordinary:num->bool) a) (val(p:int64)) n`))) THEN SIMP_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `pc<2 EXP 64 /\ val(word pc:int64)=pc` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `pc+97<=b ==> pc<b`) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      MATCH_MP_TAC(ARITH_RULE `pc+97<=b ==> pc<b`) THEN ASM_REWRITE_TAC[]];ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (word pc:int64,97) (p,n)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
    MATCH_MP_TAC CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (stackpointer:int64,8) (p,n)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
    MATCH_MP_TAC CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `x+8<b ==> x+8<=b`) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`]
    OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CALLABLE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [SIMP_TAC[];ALL_TAC] THEN CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[ASSURANCE_STACK_ADVANCE_NONWRAP] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `read(memory :> bytes(p,n))s'=0` THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE;CLEANSE_READ_BYTES_ZERO];
    X_GEN_TAC `a:int64` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:int64`;`n:num`;`s:x86state`;`s':x86state`;`a:int64`]
      CLEANSE_FUNCTIONAL_FRAME_OUTSIDE) THEN ASM_REWRITE_TAC[]]);;
let BP_E2_CLEANSE_FUNCTIONAL_RETURN = prove
 (bp_e2_cleanse_functional_statement,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ENSURES_N_ENSURES THEN
  EXISTS_TAC `\s:x86state. cleanse_functional_steps p n` THEN
  MATCH_ACCEPT_TAC(SPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`]
    BP_E2_CLEANSE_BOUNDED_FUNCTIONAL_RETURN));;
print_endline "CLEANSE_FUNCTIONAL_E2_ATTEMPT3_COMPLETE";;
