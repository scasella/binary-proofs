(* Source attempt 1. Literals were frozen before this file was written.
   Explicit supplier dependency: BP_E3_CRYPTO_PUBLIC_CALLER_POLICY only. *)
let C1_APP_EVENT_POLICY_MONO = prove
 (c1_app_event_policy_mono_statement,
  REPEAT GEN_TAC THEN SPEC_TAC (`e:uarch_event`,`e:uarch_event`) THEN
  MATCH_MP_TAC uarch_event_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_event_policy] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[R1_SECRET_SPAN_MONO]);;
let C1_APP_ALL_POLICY_MONO = prove
 (c1_app_all_policy_mono_statement,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;
let C1_APP_STEP_POLICY_MONO = prove
 (c1_app_step_policy_mono_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_step_policy] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`len:num`;`inst:instruction`;`d:uarch_event list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[R1_SECRET_SPAN_MONO];
    SUBGOAL_THEN
     `!e:uarch_event. assurance_event_policy rp0 wp0 e ==>
                       assurance_event_policy rp wp e` ASSUME_TAC THENL
     [ASM_MESON_TAC[C1_APP_EVENT_POLICY_MONO];
      ASM_MESON_TAC[C1_APP_ALL_POLICY_MONO]]]);;
let C1_CRYPTO_READ_INCLUSION = prove
 (c1_crypto_read_inclusion_statement,
  REWRITE_TAC[bp_e2_crypto_allowed_read;c1_allowed_read;c1_call_slot] THEN
  MESON_TAC[]);;
let C1_CRYPTO_WRITE_INCLUSION = prove
 (c1_crypto_write_inclusion_statement,
  REWRITE_TAC[bp_e2_crypto_allowed_write] THEN MESON_TAC[]);;
let C1_CRYPTO_FETCH_INCLUSION = prove
 (c1_crypto_fetch_inclusion_statement,
  REWRITE_TAC[bp_e2_crypto_allowed_fetch;c1_allowed_fetch] THEN MESON_TAC[]);;
let C1_CRYPTO_INTERFACE_APPLICATION = prove
 (c1_crypto_interface_application_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_crypto_ready] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`lib_file:num->byte`;`read memory (entry:x86state)`;
    `read memory (entry:x86state)`;`word_sub (stackpointer:int64) (word 16)`;
    `word 0x21001119:int64`;`p:int64`;`q:int64`;`n:num`;
    `read memory (entry:x86state)`;`rp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]
   BP_E3_CRYPTO_PUBLIC_CALLER_POLICY) THEN ASM_REWRITE_TAC[]);;
let C1_CRYPTO_POLICY_WIDEN = prove
 (c1_crypto_policy_widen_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_zero_step;c1_segment_policy] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (ISPECL
   [`bp_e2_crypto_allowed_read rp ordinary p q n
       (word_sub (stackpointer:int64) (word 16))`;
    `bp_e2_crypto_allowed_write`;
    `bp_e2_crypto_allowed_fetch xp ordinary 0x10241840`;
    `c1_allowed_read rp ordinary stackpointer p q n`;
    `c1_allowed_write wp ordinary stackpointer`;
    `c1_allowed_fetch xp ordinary`;`source:x86state`;`target:x86state`]
   C1_APP_STEP_POLICY_MONO) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[C1_CRYPTO_READ_INCLUSION];
    MESON_TAC[C1_CRYPTO_WRITE_INCLUSION];
    MESON_TAC[C1_CRYPTO_FETCH_INCLUSION]]);;
let C1_CRYPTO_SEGMENT_APPLICATION = prove
 (c1_crypto_segment_application_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`bp_assurance_call_steps n`;
    `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 16))
       (word 0x21001119) p q n (read events (entry:x86state)) (read memory entry) entry`;
    `(\k source target. assurance_zero_step
       (bp_e2_crypto_allowed_read rp ordinary p q n
         (word_sub (stackpointer:int64) (word 16)))
       bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
       k source target /\ abi_all_decodes_caller_scalar source):
       num->x86state->x86state->bool`;
    `c1_segment_policy (stackpointer:int64) p q n rp wp xp ordinary:
       num->x86state->x86state->bool`;
    `entry:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC (ISPECL
     [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`rp:num->bool`;
      `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`k:num`;
      `source:x86state`;`target:x86state`] C1_CRYPTO_POLICY_WIDEN) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC (ISPECL
     [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
      `n:num`;`m:int64->byte`;`rp:num->bool`;`xp:num->bool`;
      `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
      `entry:x86state`] C1_CRYPTO_INTERFACE_APPLICATION) THEN ASM_REWRITE_TAC[]]);;
