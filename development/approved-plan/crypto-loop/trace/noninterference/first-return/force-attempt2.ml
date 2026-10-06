needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/helpers-attempt2.ml";;
let CRYPTO_FIRST_RET_FORCE = prove
 (crypto_first_ret_force_statement,
  REWRITE_TAC[CRYPTO_FIRST_RET_EXECUTION_EQUIVALENT] THEN
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `other:(int64#num#instruction#uarch_event list)list` list_CASES) THEN
  REWRITE_TAC[crypto_observed_run;crypto_observed_execution;crypto_ret_shape;NOT_CONS_NIL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `assurance_observed_step s (h:int64#num#instruction#uarch_event list) next /\ crypto_observed_run t P next`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ASSURANCE_OBSERVED_PROJECTION]; ALL_TAC] THEN
  SUBGOAL_THEN `(h':int64#num#instruction#uarch_event list)=h` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[CRYPTO_OBSERVATION_UNIQUE]; ALL_TAC] THEN
  ASM_CASES_TAC `crypto_observation_is_ret(h:int64#num#instruction#uarch_event list)` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `crypto_observation_is_ret(h:int64#num#instruction#uarch_event list)`]) THEN
    ASM_MESON_TAC[crypto_observed_run;crypto_observed_execution];
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~crypto_observation_is_ret(h:int64#num#instruction#uarch_event list)`]) THEN
    ASM_MESON_TAC[]]);;
print_endline "CRYPTO_FIRST_RET_FORCE_ATTEMPT2_COMPLETE";;
