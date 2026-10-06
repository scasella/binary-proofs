needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/helper-proof-attempt1.ml";;
let BP_E3_CRYPTO_PUBLIC_CALLER_POLICY = prove
 (bp_e3_crypto_public_caller_policy_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`bp_assurance_call_steps n`;
    `bp_assurance_call_post 0x10241840 stackpointer ra p q n (read events s) m s`;
    `assurance_zero_scalar_step
       (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
       bp_e2_crypto_allowed_write
       (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)`;
    `\k source target. assurance_zero_step
       (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
       bp_e2_crypto_allowed_write
       (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
       k source target /\ abi_all_decodes_caller_scalar source`;
    `s:x86state`] E3_RUN_MONO_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[assurance_zero_scalar_step] THEN
      MESON_TAC[E3_SCALAR_QUALIFIES_CALLER];
      MATCH_MP_TAC BP_E2_CRYPTO_PUBLIC_POLICY THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;
print_endline "E3_CRYPTO_CALLER_POLICY_ATTEMPT1_COMPLETE";;
let BP_E3_CRYPTO_PUBLIC_CALLER_INTERFACE = prove
 (bp_e3_crypto_public_caller_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `fb_full_image file_bytes initial_rw padding (m:int64->byte)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `bp_e2_crypto_public_pre file_bytes initial_rw padding
      stackpointer ra p q n m rp xp ordinary (s,a)` THEN
    REWRITE_TAC[bp_e2_crypto_public_pre] THEN MESON_TAC[];ALL_TAC] THEN
  MP_TAC(ISPECL [`abi_caller_scalar_extended_step`;
    `\t:x86state#abi_omitted_state.
       bp_assurance_call_post 0x10241840 stackpointer ra p q n
         (read events s) m s (FST t) /\ SND t=a`;
    `bp_e2_crypto_public_post file_bytes initial_rw padding
       stackpointer ra p q n (read events s) m s a`;
    `bp_assurance_call_steps n`;`(s:x86state,a:abi_omitted_state)`]
    EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BP_E2_CRYPTO_PUBLIC_IMAGE_POST THEN
    ASM_REWRITE_TAC[abi_required_controls_preserved];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`bp_assurance_call_steps n`;
      `bp_assurance_call_post 0x10241840 stackpointer ra p q n
         (read events s) m s`;
      `assurance_zero_step
         (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
         bp_e2_crypto_allowed_write
         (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)`;
      `s:x86state`;`a:abi_omitted_state`] ABI_CALLER_CHECKED_RUN_LIFT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC BP_E3_CRYPTO_PUBLIC_CALLER_POLICY THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;
print_endline "E3_CRYPTO_CALLER_INTERFACE_ATTEMPT1_COMPLETE";;
let BP_E3_CLEANSE_PUBLIC_CALLER_POLICY = prove
 (bp_e3_cleanse_public_caller_policy_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cleanse_functional_steps (p:int64) n`;
    `bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s`;
    `\k source target. cleanse_access_covered_step 0x102417d0
       (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
       (bp_e2_cleanse_allowed_write wp ordinary p n)
       (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
       k source target /\ abi_all_decodes_cleanse_scalar source`;
    `\k source target. cleanse_access_covered_step 0x102417d0
       (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
       (bp_e2_cleanse_allowed_write wp ordinary p n)
       (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
       k source target /\ abi_all_decodes_caller_scalar source`;
    `s:x86state`] E3_RUN_MONO_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[] THEN MESON_TAC[E3_CLEANSE_QUALIFIES_CALLER];
      MATCH_MP_TAC BP_E2_CLEANSE_PUBLIC_POLICY THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;
print_endline "E3_CLEANSE_CALLER_POLICY_ATTEMPT1_COMPLETE";;
let BP_E3_CLEANSE_PUBLIC_CALLER_INTERFACE = prove
 (bp_e3_cleanse_public_caller_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`abi_caller_scalar_extended_step`;
    `\t:x86state#abi_omitted_state.
       bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s (FST t) /\ SND t=a`;
    `bp_e2_cleanse_public_post stackpointer ra p n m s a`;
    `cleanse_functional_steps (p:int64) n`;`(s:x86state,a:abi_omitted_state)`]
    EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bp_e2_cleanse_public_post] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[abi_required_controls_preserved];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`cleanse_functional_steps (p:int64) n`;
      `bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s`;
      `cleanse_access_covered_step 0x102417d0
         (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
         (bp_e2_cleanse_allowed_write wp ordinary p n)
         (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)`;
      `s:x86state`;`a:abi_omitted_state`] ABI_CALLER_CHECKED_RUN_LIFT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC BP_E3_CLEANSE_PUBLIC_CALLER_POLICY THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]]]);;
print_endline "E3_CALLEE_PUBLIC_ATTEMPT1_COMPLETE";;
