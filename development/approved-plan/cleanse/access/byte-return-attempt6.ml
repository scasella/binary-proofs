needs "/work/development/approved-plan/cleanse/access/algebra-attempt3.ml";;
needs "/work/development/approved-plan/cleanse/access/step-tactics-v3.ml";;
let CLEANSE_ACCESS_BYTE_RETURN = prove
 (cleanse_access_byte_return_statement,
  INDUCT_TAC THENL [REWRITE_TAC[LT];ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_loop_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `n<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `word_sub(word(SUC n))(word 1):int64=word n` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(ARITH_RULE `SUC n-1=n`)] THEN
    SIMP_TAC[WORD_SUB;ARITH_RULE `1<=SUC n`];ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64)=0 <=> n=0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
  SUBGOAL_THEN `assurance_span_ok wp (val(p:int64)) 1` ASSUME_TAC THENL
   [MATCH_MP_TAC CLEANSE_ACCESS_SPAN_HEAD THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
  ASM_CASES_TAC `n=0` THEN
  MAP_EVERY(fun(offset,sname)->
    (fun g->print_endline("CLEANSE_ACCESS_RUN_STEP "^string_of_int offset);ALL_TAC g) THEN
    CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
   [19,"cab1";21,"cab2";25,"cab3";29,"cab4"] THEN
  (fun g->print_endline "CLEANSE_ACCESS_AFTER_BODY";ALL_TAC g) THEN
  REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(4*SUC n+1)-4=4*n+1`] THENL
   [(fun g->print_endline "CLEANSE_ACCESS_BYTE_LAST";ALL_TAC g) THEN
    ASM_REWRITE_TAC[] THEN CLEANSE_ACCESS_STEP_TAC 31 OPENSSL_CLEANSE_EXEC "cab5" THEN
    REWRITE_TAC[assurance_checked_run;cleanse_access_return_post] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    (fun g->print_endline "CLEANSE_ACCESS_BYTE_RECURSE";ALL_TAC g) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    (fun g->print_endline "CLEANSE_ACCESS_BYTE_IH_MATCHED";ALL_TAC g) THEN
    EXISTS_TAC `word_add (p:int64) (word 1)` THEN
    ASM_REWRITE_TAC[cleanse_access_loop_pre] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `0<n <=> ~(n=0)`];
      MP_TAC(ISPECL [`wp:num->bool`;`p:int64`;`SUC n`;`1`] CLEANSE_ACCESS_SPAN_TAIL) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC n-1=n`;ARITH_RULE `1<=SUC n`];
      NONOVERLAPPING_TAC;
      NONOVERLAPPING_TAC]]);;
print_endline "CLEANSE_ACCESS_BYTE_RETURN_ATTEMPT6_COMPLETE";;
