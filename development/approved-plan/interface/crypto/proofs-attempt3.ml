(* Successor recipe: applies exactly frozen V1 public terms, without
   unfolding callee instruction semantics. The failed V1 recipe is preserved. *)
let BP_E2_CRYPTO_PUBLIC_POLICY = prove
 (bp_e2_crypto_public_policy_statement,
  REWRITE_TAC[bp_e2_crypto_public_pre] THEN
  MESON_TAC[ASSURANCE_E2_ALL_LENGTH_POLICY_FRAME]);;
let BP_E2_CRYPTO_PUBLIC_IMAGE_POST = prove
 (`!file_bytes initial_rw padding stackpointer ra p q n e m s a t.
    fb_full_image file_bytes initial_rw padding m /\
    bp_assurance_call_post 0x10241840 stackpointer ra p q n e m s (FST t) /\
    SND t = a /\ abi_required_controls_preserved a (SND t)
    ==> bp_e2_crypto_public_post file_bytes initial_rw padding
          stackpointer ra p q n e m s a t`,
  REWRITE_TAC[bp_e2_crypto_public_post;bp_assurance_call_post] THEN
  MESON_TAC[]);;
let BP_E2_CRYPTO_PUBLIC_INTERFACE = prove
 (bp_e2_crypto_public_interface_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_crypto_public_pre] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`abi_scalar_extended_step`;
    `\t:x86state#abi_omitted_state.
      bp_assurance_call_post 0x10241840 stackpointer ra p q n (read events s) m s (FST t) /\
      SND t = a /\ abi_required_controls_preserved a (SND t)`;
    `bp_e2_crypto_public_post file_bytes initial_rw padding
       stackpointer ra p q n (read events s) m s a`;
    `bp_assurance_call_steps n`; `(s:x86state,a:abi_omitted_state)`]
    EVENTUALLY_N_MONO) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[BP_E2_CRYPTO_PUBLIC_IMAGE_POST];
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`0x10241840`; `stackpointer:int64`; `ra:int64`;
      `p:int64`; `q:int64`; `n:num`; `m:int64->byte`;
      `rp:num->bool`; `xp:num->bool`; `ordinary:num->bool`;
      `s:x86state`; `a:abi_omitted_state`] ASSURANCE_E2_ALL_LENGTH_EXTENDED_ABI) THEN
    ASM_REWRITE_TAC[]]);;
let BP_E2_CRYPTO_PUBLIC_WITNESS_BRIDGE = prove
 (bp_e2_crypto_public_witness_bridge_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `fb_file_code (file_bytes:num->byte)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FB_PRE_FILE_CODE]; ALL_TAC] THEN
  UNDISCH_TAC `fb_pre file_bytes initial_rw padding image p q n different` THEN
  REWRITE_TAC[bp_e2_crypto_public_pre;fb_pre;fb_machine;FST;SND;
    FB_MACHINE_MEMORY;fb_read;fb_ordinary;lw_read;lw_ordinary;lw_image_read] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
