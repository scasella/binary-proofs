(* Source attempt1: only public supplier policy applications and generic logic.
   First3 address-free helper propositions reconstructed from the inspected C1 recipe;
   source extraction/reconstruction is explicitly recorded as integration adaptation. *)
let C2_APP_EVENT_POLICY_MONO = prove
 (c2_app_event_policy_mono_statement,
  REPEAT GEN_TAC THEN SPEC_TAC (`e:uarch_event`,`e:uarch_event`) THEN
  MATCH_MP_TAC uarch_event_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_event_policy] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[R1_SECRET_SPAN_MONO]);;
let C2_APP_ALL_POLICY_MONO = prove
 (c2_app_all_policy_mono_statement,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;
let C2_APP_STEP_POLICY_MONO = prove
 (c2_app_step_policy_mono_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_step_policy] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`len:num`;`inst:instruction`;`d:uarch_event list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[R1_SECRET_SPAN_MONO];
    SUBGOAL_THEN
     `!e:uarch_event. assurance_event_policy rp0 wp0 e ==>
                       assurance_event_policy rp wp e` ASSUME_TAC THENL
     [ASM_MESON_TAC[C2_APP_EVENT_POLICY_MONO];
      ASM_MESON_TAC[C2_APP_ALL_POLICY_MONO]]]);;
let C2_CRYPTO_POLICY_WIDEN = prove
 (c2_crypto_policy_widen_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[assurance_zero_step;c2_segment_policy] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (ISPECL
   [`bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer (word 32))`;`bp_e2_crypto_allowed_write`;`bp_e2_crypto_allowed_fetch xp ordinary 0x10241840`;
    `c2_allowed_read rp ordinary stackpointer p q n`;
    `c2_allowed_write wp ordinary stackpointer p q n m`;
    `c2_allowed_fetch xp ordinary`;`source:x86state`;`target:x86state`]
   C2_APP_STEP_POLICY_MONO) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bp_e2_crypto_allowed_read;bp_e2_crypto_allowed_write;
    bp_e2_crypto_allowed_fetch;c2_allowed_read;c2_allowed_write;
    c2_allowed_fetch;c2_scratch;assurance_region] THEN
  ASM_MESON_TAC[ARITH_RULE `b<=a /\ a<b+8 ==> b<=a /\ a<b+32`]);;
let C2_CRYPTO_PUBLIC_POLICY_APPLICATION = prove
 (c2_crypto_public_policy_application_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`lib_file:num->byte`;`read memory (entry:x86state)`;`read memory (entry:x86state)`;
    `word_sub (stackpointer:int64) (word 32)`;`word 0x22001132:int64`;
    `p:int64`;`q:int64`;`n:num`;`read memory (entry:x86state)`;
    `rp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]
    BP_E3_CRYPTO_PUBLIC_CALLER_POLICY) THEN ASM_REWRITE_TAC[]);;
let C2_CRYPTO_INTERFACE_APPLICATION = prove
 (c2_crypto_interface_application_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`bp_assurance_call_steps n`;`bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32)) (word 0x22001132) p q n (read events entry) (read memory entry) entry`;
    `(\k source target. assurance_zero_step (bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer (word 32))) bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840) k source target /\ abi_all_decodes_caller_scalar source):num->x86state->x86state->bool`;
    `c2_segment_policy (stackpointer:int64) p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `entry:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC (ISPECL
     [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `k:num`;`source:x86state`;`target:x86state`] C2_CRYPTO_POLICY_WIDEN) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC (ISPECL
     [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `a:abi_omitted_state`;`entry:x86state`] C2_CRYPTO_PUBLIC_POLICY_APPLICATION) THEN
    ASM_REWRITE_TAC[]]);;
let C2_CLEANSE_POLICY_WIDEN = prove
 (c2_cleanse_policy_widen_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cleanse_access_covered_step;assurance_zero_step;c2_segment_policy] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (ISPECL
   [`bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer (word 32))`;`bp_e2_cleanse_allowed_write wp ordinary p n`;`bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0`;
    `c2_allowed_read rp ordinary stackpointer p q n`;
    `c2_allowed_write wp ordinary stackpointer p q n m`;
    `c2_allowed_fetch xp ordinary`;`source:x86state`;`target:x86state`]
   C2_APP_STEP_POLICY_MONO) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bp_e2_cleanse_allowed_read;bp_e2_cleanse_allowed_write;
    bp_e2_cleanse_allowed_fetch;c2_allowed_read;c2_allowed_write;
    c2_allowed_fetch;c2_scratch;assurance_region] THEN
  ASM_MESON_TAC[ARITH_RULE `b<=a /\ a<b+8 ==> b<=a /\ a<b+32`]);;
let C2_CLEANSE_PUBLIC_POLICY_APPLICATION = prove
 (c2_cleanse_public_policy_application_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`lib_file:num->byte`;`read memory (entry:x86state)`;`read memory (entry:x86state)`;
    `word_sub (stackpointer:int64) (word 32)`;`word 0x22001153:int64`;
    `p:int64`;`n:num`;`read memory (entry:x86state)`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]
    BP_E3_CLEANSE_PUBLIC_CALLER_POLICY) THEN ASM_REWRITE_TAC[]);;
let C2_CLEANSE_INTERFACE_APPLICATION = prove
 (c2_cleanse_interface_application_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`cleanse_functional_steps p n`;`bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer (word 32)) (word 0x22001153) p n (read memory entry) entry`;
    `(\k source target. cleanse_access_covered_step 0x102417d0 (bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer (word 32))) (bp_e2_cleanse_allowed_write wp ordinary p n) (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0) k source target /\ abi_all_decodes_caller_scalar source):num->x86state->x86state->bool`;
    `c2_segment_policy (stackpointer:int64) p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `entry:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC (ISPECL
     [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `k:num`;`source:x86state`;`target:x86state`] C2_CLEANSE_POLICY_WIDEN) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC (ISPECL
     [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
      `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
      `a:abi_omitted_state`;`entry:x86state`] C2_CLEANSE_PUBLIC_POLICY_APPLICATION) THEN
    ASM_REWRITE_TAC[]]);;
