needs "/work/development/approved-plan/crypto-loop/trace/control/synchronization-statements.ml";;
let CRYPTO_CONTROL_RUN_POST = prove
 (crypto_control_run_post_statement,
  INDUCT_TAC THENL
   [REWRITE_TAC[assurance_checked_run;EVENTUALLY_N_TRIVIAL];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN
    REWRITE_TAC[ARITH_RULE `SUC n=1+n`;EVENTUALLY_N_STEP] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
      SUBGOAL_THEN `C (1+n) s next /\ assurance_checked_run n P C next /\
        eventually_n x86 n Q next` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[];ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;
print_endline "CRYPTO_CONTROL_RUN_POST_COMPLETE";;
