needs "/work/development/approved-plan/cleanse/interface/policy-proof-attempt1.ml";;
let BP_E2_CLEANSE_EXTENDED = prove
 (bp_e2_cleanse_extended_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`abi_cleanse_scalar_extended_step`;
    `\t:x86state#abi_omitted_state.
      bp_e2_cleanse_call_post pc stackpointer ra p n m s (FST t) /\ SND t=a`;
    `\t:x86state#abi_omitted_state.
      bp_e2_cleanse_call_post pc stackpointer ra p n m s (FST t) /\
      SND t=a /\ abi_required_controls_preserved a (SND t)`;
    `cleanse_functional_steps (p:int64) n`;`(s:x86state,a:abi_omitted_state)`]
    EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[abi_required_controls_preserved];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`cleanse_functional_steps (p:int64) n`;
      `bp_e2_cleanse_call_post pc stackpointer ra p n m s`;
      `cleanse_access_covered_step pc
        (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
        (bp_e2_cleanse_allowed_write wp ordinary p n)
        (bp_e2_cleanse_allowed_fetch xp ordinary pc)`;
      `s:x86state`;`a:abi_omitted_state`] ABI_CLEANSE_CHECKED_RUN_LIFT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC BP_E2_CLEANSE_POLICY_FRAME THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;
print_endline "CLEANSE_INTERFACE_PRODUCT_ATTEMPT2_COMPLETE";;
