(* Recipes apply established interface ingredients; no callee instruction
   semantics are unfolded here. All target definitions/terms frozen V1. *)
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
  MATCH_MP_TAC EVENTUALLY_N_MONO THEN
  EXISTS_TAC `\t:x86state#abi_omitted_state.
    bp_assurance_call_post 0x10241840 stackpointer ra p q n (read events s) m s (FST t) /\
    SND t = a /\ abi_required_controls_preserved a (SND t)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[BP_E2_CRYPTO_PUBLIC_IMAGE_POST];
    ASM_MESON_TAC[ASSURANCE_E2_ALL_LENGTH_EXTENDED_ABI]]);;
(* Witness bridge awaits frozen FB_PRE_FILE_CODE lemma to bind acquisition. *)
