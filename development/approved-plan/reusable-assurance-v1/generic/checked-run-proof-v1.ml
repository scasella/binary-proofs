(* Exact generic proof phrases with binding names changed only. See source-provenance-v1.json. *)
let RA_CHECKED_RUN_APPEND = prove
 (ra_checked_run_append_statement,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES;assurance_checked_run];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ADD_CLAUSES;assurance_checked_run] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `t:x86state`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM
         (MATCH_MP_TAC o SPECL [`n:num`;`P:x86state->bool`;
                               `C:num->x86state->x86state->bool`;`t:x86state`]) THEN
        ASM_REWRITE_TAC[]]]]);;
let RA_CHECKED_RUN_POST_MONO = prove
 (ra_checked_run_post_mono_statement,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_checked_run] THENL
   [MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `t:x86state`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM
       (MATCH_MP_TAC o SPECL [`P:x86state->bool`;`Q:x86state->bool`;
                             `C:num->x86state->x86state->bool`;`t:x86state`]) THEN
      ASM_REWRITE_TAC[]]]);;
let RA_CHECKED_RUN_POLICY_MONO = prove
 (ra_checked_run_policy_mono_statement,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_checked_run] THENL
   [MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `t:x86state`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        FIRST_X_ASSUM
         (MATCH_MP_TAC o SPECL [`P:x86state->bool`;
           `C:num->x86state->x86state->bool`;
           `D:num->x86state->x86state->bool`;`t:x86state`]) THEN
        ASM_REWRITE_TAC[]]]]);;
