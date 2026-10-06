needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/statements-v1.ml";;
let E3_SCALAR_QUALIFIES_CALLER = prove
 (e3_scalar_qualifies_caller_statement,
  REWRITE_TAC[abi_all_decodes_scalar;abi_all_decodes_caller_scalar;
    abi_caller_scalar_instruction;abi_cleanse_scalar_instruction] THEN MESON_TAC[]);;
let E3_CLEANSE_QUALIFIES_CALLER = prove
 (e3_cleanse_qualifies_caller_statement,
  REWRITE_TAC[abi_all_decodes_cleanse_scalar;abi_all_decodes_caller_scalar;
    abi_caller_scalar_instruction] THEN MESON_TAC[]);;
let E3_RUN_MONO_STEP = prove
 (e3_run_mono_step_statement,
  INDUCT_TAC THENL
   [REWRITE_TAC[assurance_checked_run] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[assurance_checked_run] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    X_GEN_TAC `next:x86state` THEN DISCH_TAC THEN
    SUBGOAL_THEN `C (SUC n) s next /\ assurance_checked_run n P C next`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o ISPECL
      [`P:x86state->bool`;`C:num->x86state->x86state->bool`;
       `D:num->x86state->x86state->bool`;`next:x86state`]) THEN
    ASM_REWRITE_TAC[]]);;
print_endline "E3_CALLEE_HELPERS_ATTEMPT1_COMPLETE";;
