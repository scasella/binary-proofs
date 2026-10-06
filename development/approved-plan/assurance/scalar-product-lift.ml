(* Instantiation of the generic product-state run lift. Whole-machine physical
   correspondence of the documented scalar effects remains an ISA trust item. *)
let ASSURANCE_SCALAR_POLICY_RUN_LIFT = prove
 (`!n P rp wp xp s a.
    assurance_checked_run n P (assurance_zero_scalar_step rp wp xp) s
    ==> eventually_n abi_scalar_extended_step n
          (\t. P(FST t) /\ SND t = a) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `P:x86state->bool`;
    `assurance_zero_step rp wp xp`; `s:x86state`; `a:abi_omitted_state`]
    ABI_CHECKED_RUN_LIFT) THEN
  ASM_REWRITE_TAC[GSYM assurance_zero_scalar_step; ETA_AX]);;

let ASSURANCE_SCALAR_POLICY_RUN_CONTROLS = prove
 (`!n P rp wp xp s a.
    assurance_checked_run n P (assurance_zero_scalar_step rp wp xp) s
    ==> eventually_n abi_scalar_extended_step n
          (\t. P(FST t) /\ abi_required_controls_preserved a (SND t)) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`abi_scalar_extended_step`;
    `\t:x86state#abi_omitted_state. P(FST t) /\ SND t = a`;
    `\t:x86state#abi_omitted_state. P(FST t) /\
       abi_required_controls_preserved a (SND t)`; `n:num`;
    `(s:x86state,a:abi_omitted_state)`]
    EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[abi_required_controls_preserved];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `P:x86state->bool`; `rp:num->bool`;
      `wp:num->bool`; `xp:num->bool`; `s:x86state`; `a:abi_omitted_state`]
      ASSURANCE_SCALAR_POLICY_RUN_LIFT) THEN ASM_REWRITE_TAC[]]);;
