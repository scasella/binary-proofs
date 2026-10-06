needs "/work/development/approved-plan/cleanse/access/alignment-return-attempt11.ml";;
needs "/work/development/approved-plan/cleanse/access/public-algebra-attempt8.ml";;
needs "/work/development/approved-plan/cleanse/access/decomposition-attempt1.ml";;
needs "/work/development/approved-plan/cleanse/access/step-tactics-v5.ml";;
let CLEANSE_ACCESS_ALL_LENGTH = prove
 (cleanse_access_all_length_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`s:x86state`] CLEANSE_ACCESS_PRE_PERMISSIONS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary (s:x86state)` THEN
  REWRITE_TAC[bp_e2_cleanse_pre;C_ARGUMENTS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64)=n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT];ALL_TAC] THEN
  ASM_CASES_TAC `n<15` THENL
   [ASM_REWRITE_TAC[cleanse_access_count] THEN ASM_CASES_TAC `n=0` THEN
    MAP_EVERY(fun(offset,sname)->CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
     [0,"cas1";4,"cas2";7,"cas3";11,"cas4";13,"cas5";17,"cas6"] THEN
    REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `(4*n+7)-6=4*n+1`] THENL
     [ASM_REWRITE_TAC[] THEN CLEANSE_ACCESS_STEP_TAC 31 OPENSSL_CLEANSE_EXEC "cas7" THEN
      REWRITE_TAC[assurance_checked_run;cleanse_access_return_post] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`n:num`;`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;
        `bp_e2_cleanse_allowed_read rp ordinary stackpointer`;
        `bp_e2_cleanse_allowed_write wp ordinary p n`;
        `bp_e2_cleanse_allowed_fetch xp ordinary pc`;`cas6:x86state`]
        CLEANSE_ACCESS_BYTE_RETURN) THEN
      ASM_REWRITE_TAC[cleanse_access_loop_pre;WORD_SUB_0;ARITH_RULE `0<n <=> ~(n=0)`]];
    SUBGOAL_THEN `15<=n` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `15<=n <=> ~(n<15)`];ALL_TAC] THEN
    ABBREV_TAC `a=(8-val(p:int64) MOD 8) MOD 8` THEN
    ABBREV_TAC `k=(n-a) DIV 8` THEN ABBREV_TAC `r=(n-a) MOD 8` THEN
    SUBGOAL_THEN
     `a<8 /\ a<n /\ 0<k /\ r<8 /\ n=a+8*k+r /\
      (val(p:int64)+a) MOD 8=0 /\ (!i. i<a ==> ~((val p+i) MOD 8=0))`
     STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN EXPAND_TAC "k" THEN EXPAND_TAC "a" THEN
      MP_TAC(SPECL [`val(p:int64)`;`n:num`] CLEANSE_ACCESS_LARGE_DECOMPOSITION) THEN
      ASM_REWRITE_TAC[LET_DEF;LET_END_DEF;ARITH_RULE `15<=n <=> ~(n<15)`];ALL_TAC] THEN
    SUBGOAL_THEN `val(p:int64)+a<2 EXP 64` ASSUME_TAC THENL
     [UNDISCH_TAC `assurance_span_ok (\x. wp x /\ ordinary x) (val(p:int64)) n` THEN
      REWRITE_TAC[assurance_span_ok] THEN STRIP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_REWRITE_TAC[cleanse_access_count;LET_DEF;LET_END_DEF] THEN
    UNDISCH_THEN `(n-a) DIV 8=k` (K ALL_TAC) THEN
    UNDISCH_THEN `(n-a) MOD 8=r` (K ALL_TAC) THEN
    UNDISCH_THEN `n=a+8*k+r` SUBST_ALL_TAC THEN
    MAP_EVERY(fun(offset,sname)->CLEANSE_ACCESS_STEP_TAC offset OPENSSL_CLEANSE_EXEC sname)
     [0,"cal1";4,"cal2";7,"cal3";11,"cal4"] THEN
    REWRITE_TAC[ARITH_RULE `(a-b)-c=a-(b+c)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `(9+6*a+5*k+4*r)-4=6*a+5*k+4*r+5`] THEN
    MATCH_MP_TAC(ISPECL [`a:num`;`k:num`;`r:num`;`pc:num`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`bp_e2_cleanse_allowed_read rp ordinary stackpointer`;
      `bp_e2_cleanse_allowed_write wp ordinary p n`;
      `bp_e2_cleanse_allowed_fetch xp ordinary pc`;`cal4:x86state`]
      CLEANSE_ACCESS_ALIGNMENT_RETURN) THEN ASM_REWRITE_TAC[cleanse_access_loop_pre] THEN
    ASM_SIMP_TAC[ARITH_RULE `(a+8*k+r)-a=8*k+r`;DIV_MULT_ADD;MOD_MULT_ADD;
      ARITH_RULE `~(8=0)`;DIV_LT;MOD_LT;ADD_CLAUSES]]);;
print_endline "CLEANSE_ACCESS_ALL_LENGTH_ATTEMPT8_COMPLETE";;
