needs "/work/development/approved-plan/cleanse/access/bulk-return-attempt11.ml";;
needs "/work/development/approved-plan/cleanse/functional/alignment-algebra-attempt2.ml";;
let CLEANSE_ACCESS_ALIGNMENT_RETURN = prove
 (cleanse_access_alignment_return_statement,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_loop_pre;MULT_CLAUSES;ADD_CLAUSES] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `val(word_and p (word 7):int64)=0` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP (REWRITE_RULE[ADD_0;WORD_ADD_0]
        (ISPECL [`p:int64`;`0`] CLEANSE_FUNCTIONAL_LOW3))
        (SPEC `p:int64` VAL_BOUND_64)) THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
    MAP_EVERY(fun(offset,sname)->CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
     [48,"caa1";55,"caa2"] THEN
    REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `(5*k+4*r+5)-2=5*k+4*r+3`] THEN
    MATCH_MP_TAC(ISPECL [`k:num`;`r:num`;`pc:num`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`caa2:x86state`]
      CLEANSE_ACCESS_BULK_RETURN) THEN ASM_REWRITE_TAC[cleanse_access_loop_pre];
    REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_loop_pre] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((val(p:int64)) MOD 8=0)` ASSUME_TAC THENL
     [UNDISCH_TAC `!i. i<SUC a ==> ~((val(p:int64)+i) MOD 8=0)` THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ADD_0;ARITH_RULE `0<SUC a`];ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and p (word 7):int64)=0)` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP (REWRITE_RULE[ADD_0;WORD_ADD_0]
        (ISPECL [`p:int64`;`0`] CLEANSE_FUNCTIONAL_LOW3))
        (SPEC `p:int64` VAL_BOUND_64)) THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `val(word_add (p:int64) (word 1))=val p+1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word(SUC a+8*k+r)) (word 18446744073709551615):int64=word(a+8*k+r)`
     ASSUME_TAC THENL
     [SUBGOAL_THEN `word 18446744073709551615:int64=word_neg(word 1)` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV;ALL_TAC] THEN
      REWRITE_TAC[WORD_RULE `word_add (x:int64) (word_neg y)=word_sub x y`] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(ARITH_RULE `(SUC a+8*k+r)-1=a+8*k+r`)] THEN
      CONV_TAC SYM_CONV THEN SIMP_TAC[WORD_SUB;ARITH_RULE `1<=SUC a+8*k+r`];ALL_TAC] THEN
    SUBGOAL_THEN `assurance_span_ok wp (val(p:int64)) 1` ASSUME_TAC THENL
     [MATCH_MP_TAC CLEANSE_ACCESS_SPAN_HEAD THEN EXISTS_TAC `SUC a+8*k+r` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
    MAP_EVERY(fun(offset,sname)->CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
     [48,"caa1";55,"caa2";57,"caa3";59,"caa4";63,"caa5";67,"caa6"] THEN
    REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `(6*SUC a+5*k+4*r+5)-6=6*a+5*k+4*r+5`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `word_add (p:int64) (word 1)` THEN
    ASM_REWRITE_TAC[cleanse_access_loop_pre;ARITH_RULE `(a+1)+b=a+SUC b`] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `SUC a<8` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `!j. j<SUC a ==> ~((val(p:int64)+j) MOD 8=0)` THEN
      DISCH_THEN(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[LT_SUC];
      UNDISCH_TAC `SUC a+8*k+r<2 EXP 64` THEN ARITH_TAC;
      MP_TAC(ISPECL [`wp:num->bool`;`p:int64`;`SUC a+8*k+r`;`1`] CLEANSE_ACCESS_SPAN_TAIL) THEN
      ASM_REWRITE_TAC[ARITH_RULE `(SUC a+8*k+r)-1=a+8*k+r`;ARITH_RULE `1<=SUC a+8*k+r`];
      NONOVERLAPPING_TAC;NONOVERLAPPING_TAC]]);;
print_endline "CLEANSE_ACCESS_ALIGNMENT_RETURN_ATTEMPT11_COMPLETE";;
