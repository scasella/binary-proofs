needs "/work/development/approved-plan/cleanse/access/byte-return-attempt6.ml";;
needs "/work/development/approved-plan/cleanse/access/step-tactics-v4.ml";;
let CLEANSE_ACCESS_TAIL_RETURN = prove
 (cleanse_access_tail_return_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_loop_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word r:int64)=0 <=> r=0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
  ASM_CASES_TAC `r=0` THEN
  MAP_EVERY(fun(offset,sname)->CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
   [89,"cat1";93,"cat2"] THEN
  REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(4*r+3)-2=4*r+1`] THENL
   [ASM_REWRITE_TAC[] THEN CLEANSE_ACCESS_STEP_TAC 95 OPENSSL_CLEANSE_EXEC "cat3" THEN
    (fun g->print_endline "CLEANSE_ACCESS_TAIL_ZERO_POST";ALL_TAC g) THEN
    REWRITE_TAC[assurance_checked_run;cleanse_access_return_post] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    (fun g->print_endline "CLEANSE_ACCESS_TAIL_POSITIVE";ALL_TAC g) THEN
    MATCH_MP_TAC(ISPECL [`r:num`;`pc:num`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`cat2:x86state`]
      CLEANSE_ACCESS_BYTE_RETURN) THEN
    ASM_REWRITE_TAC[cleanse_access_loop_pre;ARITH_RULE `0<r <=> ~(r=0)`;WORD_SUB_0]]);;
print_endline "CLEANSE_ACCESS_TAIL_RETURN_ATTEMPT6_COMPLETE";;
