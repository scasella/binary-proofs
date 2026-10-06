needs "/work/development/approved-plan/crypto-loop/trace/control/run-mono-statement.ml";;
let CRYPTO_CONTROL_RUN_MONO = prove
 (crypto_control_run_mono_statement,
  INDUCT_TAC THENL
   [REWRITE_TAC[assurance_checked_run] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]]);;
print_endline "CRYPTO_CONTROL_RUN_MONO_COMPLETE";;
