let ASSURANCE_E2_CALL_ZERO_POST = prove
 (assurance_e2_call_zero_post_statement,
  REWRITE_TAC[FUN_EQ_THM; bp_assurance_call_post; bp_assurance_zero_post;
    crypto_trace_call; ARITH_RULE `~(i<0)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let ASSURANCE_E2_CALL_16_POST = prove
 (assurance_e2_call_16_post_statement,
  REWRITE_TAC[FUN_EQ_THM; bp_assurance_call_post; bp_assurance_16_byte_post;
    crypto_trace_call] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let ASSURANCE_E2_GENERIC_POLICY_FRAME = prove
 (assurance_e2_generic_policy_frame_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_E2_FETCH_SPAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bp_e2_crypto_pre]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  MP_TAC(ISPECL [`rp:num->bool`; `ordinary:num->bool`; `p:int64`; `q:int64`;
    `n:num`; `stackpointer:int64`] ASSURANCE_E2_READ_SPANS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`pc:num`; `stackpointer:int64`; `ra:int64`; `p:int64`;
    `q:int64`; `n:num`; `m:int64->byte`; `read events s`;
    `bp_e2_crypto_allowed_read rp ordinary p q n stackpointer`;
    `bp_e2_crypto_allowed_fetch xp ordinary pc`; `s:x86state`]
    CRYPTO_CONTROL_GENERIC_COMBINED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ASSURANCE_E2_PERMISSION_FUNCTIONS] THEN
    ASSURANCE_E2_COMPONENT_POST_TAC
     (REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[bp_assurance_call_post] THEN
      ASM_SIMP_TAC[ASSURANCE_STACK_ADVANCE_NONWRAP])]);;

let ASSURANCE_E2_ALL_LENGTH_POLICY_FRAME = prove
 (assurance_e2_all_length_policy_frame_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n=0` THENL
   [ASM_REWRITE_TAC[bp_assurance_call_steps; ASSURANCE_E2_CALL_ZERO_POST] THEN
    MATCH_MP_TAC ASSURANCE_E2_ZERO_POLICY_FRAME THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n=16` THENL
   [ASM_REWRITE_TAC[bp_assurance_call_steps; ASSURANCE_E2_CALL_16_POST] THEN
    MATCH_MP_TAC ASSURANCE_E2_16_BYTE_POLICY_FRAME THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[bp_assurance_call_steps] THEN
    MATCH_MP_TAC ASSURANCE_E2_GENERIC_POLICY_FRAME THEN ASM_REWRITE_TAC[]]);;

let ASSURANCE_E2_ALL_LENGTH_EXTENDED_ABI = prove
 (assurance_e2_all_length_extended_abi_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`bp_assurance_call_steps n`;
    `bp_assurance_call_post pc stackpointer ra p q n (read events s) m s`;
    `bp_e2_crypto_allowed_read rp ordinary p q n stackpointer`;
    `bp_e2_crypto_allowed_write`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `s:x86state`; `a:abi_omitted_state`] ASSURANCE_E2_POLICY_PRODUCT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ASSURANCE_E2_ALL_LENGTH_POLICY_FRAME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;
