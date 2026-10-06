let ASSURANCE_E2_16_BYTE_POST_EQ = prove
 (`!pc stackpointer ra p q e m s s'. read memory s = m
    ==> (bp_assurance_16_post pc stackpointer ra p q e m s s' <=>
         bp_assurance_16_byte_post pc stackpointer ra p q e m s s')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[bp_assurance_16_post; bp_assurance_16_byte_post;
    READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[BP_WORDPAIR_BYTE16]);;

let ASSURANCE_E2_16_BYTE_POLICY_FRAME = prove
 (`!pc stackpointer ra p q m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q 16 m rp xp ordinary s
    ==> assurance_checked_run 15
      (bp_assurance_16_byte_post pc stackpointer ra p q (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q 16 stackpointer)
        bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary pc)) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`pc:num`; `stackpointer:int64`; `ra:int64`; `p:int64`;
    `q:int64`; `m:int64->byte`; `rp:num->bool`; `xp:num->bool`;
    `ordinary:num->bool`; `s:x86state`] ASSURANCE_E2_16_POLICY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN ASSURANCE_E2_COMPONENT_POST_TAC
   (REWRITE_TAC[] THEN GEN_TAC THEN
    SUBGOAL_THEN `read memory (s:x86state) = m` ASSUME_TAC THENL
     [ASM_MESON_TAC[bp_e2_crypto_pre]; ALL_TAC] THEN
    ASM_SIMP_TAC[ASSURANCE_E2_16_BYTE_POST_EQ]));;

let ASSURANCE_E2_16_BYTE_EXTENDED_ABI = prove
 (`!pc stackpointer ra p q m rp xp ordinary s a.
    bp_e2_crypto_pre pc stackpointer ra p q 16 m rp xp ordinary s
    ==> eventually_n abi_scalar_extended_step 15
      (\t. bp_assurance_16_byte_post pc stackpointer ra p q (read events s) m s
             (FST t) /\ SND t = a /\
           abi_required_controls_preserved a (SND t)) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`15`;
    `bp_assurance_16_byte_post pc stackpointer ra p q (read events s) m s`;
    `bp_e2_crypto_allowed_read rp ordinary p q 16 stackpointer`;
    `bp_e2_crypto_allowed_write`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `s:x86state`; `a:abi_omitted_state`] ASSURANCE_E2_POLICY_PRODUCT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ASSURANCE_E2_16_BYTE_POLICY_FRAME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;
