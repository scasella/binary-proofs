needs "/work/development/approved-plan/cleanse/interface/statement-loader-v1.ml";;
let CLEANSE_INTERFACE_COUNT_EQUAL = prove
 (cleanse_interface_count_equal_statement,
  REWRITE_TAC[cleanse_access_count;cleanse_functional_steps;LET_DEF;LET_END_DEF]);;
let CLEANSE_INTERFACE_RUN_POST = prove
 (cleanse_interface_run_post_statement,
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
let CLEANSE_INTERFACE_RUN_MONO = prove
 (cleanse_interface_run_mono_statement,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `C (SUC n) s next /\ assurance_checked_run n P C next`
       STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o
        ISPECL [`P:x86state->bool`;`Q:x86state->bool`;
          `C:num->x86state->x86state->bool`;`next:x86state`]) THEN
      ASM_REWRITE_TAC[]]]);;
let CLEANSE_INTERFACE_SLOT_PRESERVED = prove
 (cleanse_interface_slot_preserved_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES;VAL_READ_WBYTES;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[READ_BYTES_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SPEC `word_add stackpointer (word i):int64`
    (ASSUME `!a:int64. ~assurance_region p n (val a) ==> read memory t a=m a`)) THEN
  SUBGOAL_THEN `val(word_add stackpointer (word i):int64)=val stackpointer+i`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `(i:num)<2 EXP 64 /\ val(stackpointer:int64)+i<2 EXP 64`
      STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT];
    UNDISCH_TAC `!a. ~(assurance_region p n a /\ assurance_region stackpointer 8 a)` THEN
    REWRITE_TAC[assurance_region] THEN
    DISCH_THEN(MP_TAC o SPEC `val(stackpointer:int64)+i`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
print_endline "CLEANSE_INTERFACE_HELPER_ATTEMPT3_COMPLETE";;
