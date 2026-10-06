needs "/work/development/approved-plan/cleanse/access/tail-return-attempt6.ml";;
needs "/work/development/approved-plan/cleanse/functional/bulk-algebra-attempt2.ml";;
let CLEANSE_ACCESS_BULK_RETURN = prove
 (cleanse_access_bulk_return_statement,
  INDUCT_TAC THENL [REWRITE_TAC[LT];ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_loop_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `8*k+r<2 EXP 64 /\ 8<=8*SUC k+r` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word(8*SUC k+r)) (word 18446744073709551608):int64=word(8*k+r)`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551608:int64=word_neg(word 8)` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV;ALL_TAC] THEN
    REWRITE_TAC[WORD_RULE `word_add (x:int64) (word_neg y)=word_sub x y`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(ARITH_RULE `(8*SUC k+r)-8=8*k+r`)] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB];ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_and (word(8*k+r)) (word 18446744073709551608):int64)=0 <=> k=0`
   ASSUME_TAC THENL [ASM_SIMP_TAC[CLEANSE_FUNCTIONAL_BULK_MASK;ARITH_RULE `r<8 ==> (8*k+r<8 <=> k=0)`];ALL_TAC] THEN
  SUBGOAL_THEN `assurance_span_ok wp (val(p:int64)) 8` ASSUME_TAC THENL
   [MATCH_MP_TAC CLEANSE_ACCESS_SPAN_HEAD THEN EXISTS_TAC `8*SUC k+r` THEN
    ASM_REWRITE_TAC[];ALL_TAC] THEN
  ASM_CASES_TAC `k=0` THEN
  TRY(UNDISCH_THEN `(k:num)=0` SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES;ADD_CLAUSES;ARITH_RULE `8*SUC 0+r=8+r`])) THEN
  MAP_EVERY(fun(offset,sname)->
    (fun g->print_endline("CLEANSE_ACCESS_BULK_STEP "^string_of_int offset);ALL_TAC g) THEN
    CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
   [69,"caq1";72,"caq2";76,"caq3";83,"caq4";87,"caq5"] THEN
  REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(5*SUC k+4*r+3)-5=5*k+4*r+3`;
    ARITH_RULE `(5+4*r+3)-5=4*r+3`] THENL
   [(fun g->print_endline "CLEANSE_ACCESS_BULK_LAST";ALL_TAC g) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES] THEN
    MATCH_MP_TAC(ISPECL [`r:num`;`pc:num`;`stackpointer:int64`;`ra:int64`;
      `word_add (p:int64) (word 8)`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
      `caq5:x86state`] CLEANSE_ACCESS_TAIL_RETURN) THEN
    ASM_REWRITE_TAC[cleanse_access_loop_pre] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`wp:num->bool`;`p:int64`;`8+r`;`8`] CLEANSE_ACCESS_SPAN_TAIL) THEN
      ASM_REWRITE_TAC[ARITH_RULE `(8+r)-8=r`;ARITH_RULE `8<=8+r`];
      NONOVERLAPPING_TAC;NONOVERLAPPING_TAC];
    (fun g->print_endline "CLEANSE_ACCESS_BULK_RECURSE";ALL_TAC g) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `word_add (p:int64) (word 8)` THEN
    ASM_REWRITE_TAC[cleanse_access_loop_pre] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `0<k <=> ~(k=0)`];
      MP_TAC(ISPECL [`wp:num->bool`;`p:int64`;`8*SUC k+r`;`8`] CLEANSE_ACCESS_SPAN_TAIL) THEN
      ASM_REWRITE_TAC[ARITH_RULE `(8*SUC k+r)-8=8*k+r`;ARITH_RULE `8<=8*SUC k+r`];
      NONOVERLAPPING_TAC;NONOVERLAPPING_TAC]]);;
print_endline "CLEANSE_ACCESS_BULK_RETURN_ATTEMPT11_COMPLETE";;
