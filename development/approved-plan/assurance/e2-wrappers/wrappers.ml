(* Refinement of the restricted components to the exact frozen E2 Pre. *)
let ASSURANCE_E2_COMPONENT_POST_TAC endpoint_tac =
  DISCH_THEN(fun run -> fun (asl,w) ->
    let _,target = strip_comb w and _,source = strip_comb(concl run) in
    (MATCH_MP_TAC(ISPECL [hd target; List.nth source 1; List.nth target 1;
       List.nth target 2; List.nth target 3] ASSURANCE_E2_CHECKED_RUN_MONO) THEN
     CONJ_TAC THENL [endpoint_tac; ACCEPT_TAC run]) (asl,w));;

let ASSURANCE_E2_ZERO_POLICY_FRAME = prove
 (`!pc stackpointer ra p q m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q 0 m rp xp ordinary s
    ==> assurance_checked_run 6
      (bp_assurance_zero_post pc stackpointer ra (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q 0 stackpointer)
        bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary pc)) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_E2_FETCH_SPAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bp_e2_crypto_pre]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  MP_TAC(ISPECL [`pc:num`; `stackpointer:int64`; `ra:int64`; `p:int64`;
    `q:int64`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `\a:num. rp a /\ ordinary a`; `read events s`; `m:int64->byte`;
    `s:x86state`] ASSURANCE_CRYPTO_ZERO_FRAMED_POLICY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ASSURANCE_SPAN_SELF_REGION THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSURANCE_E2_ZERO_ALLOWED_READ;
      ASSURANCE_E2_PERMISSION_FUNCTIONS] THEN
    ASSURANCE_E2_COMPONENT_POST_TAC
     (REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[bp_assurance_zero_post] THEN
      ASM_SIMP_TAC[ASSURANCE_STACK_ADVANCE_NONWRAP])]);;

let ASSURANCE_E2_16_POLICY_FRAME = prove
 (`!pc stackpointer ra p q m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q 16 m rp xp ordinary s
    ==> assurance_checked_run 15
      (bp_assurance_16_post pc stackpointer ra p q (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q 16 stackpointer)
        bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary pc)) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASSURANCE_E2_FETCH_SPAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bp_e2_crypto_pre]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  MP_TAC(ISPECL [`pc:num`; `stackpointer:int64`; `ra:int64`; `p:int64`;
    `q:int64`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `\a:num. rp a /\ ordinary a`;
    `read (memory :> bytes64 p) s`;
    `read (memory :> bytes64 (word_add p (word 8))) s`;
    `read (memory :> bytes64 q) s`;
    `read (memory :> bytes64 (word_add q (word 8))) s`;
    `read events s`; `m:int64->byte`; `s:x86state`]
    ASSURANCE_CRYPTO_16_FRAMED_POLICY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSURANCE_E2_PERMISSION_FUNCTIONS] THEN
    ASSURANCE_E2_COMPONENT_POST_TAC
     (REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[bp_assurance_16_post] THEN
      ASM_SIMP_TAC[ASSURANCE_STACK_ADVANCE_NONWRAP])]);;

let ASSURANCE_E2_ZERO_EXTENDED_ABI = prove
 (`!pc stackpointer ra p q m rp xp ordinary s a.
    bp_e2_crypto_pre pc stackpointer ra p q 0 m rp xp ordinary s
    ==> eventually_n abi_scalar_extended_step 6
      (\t. bp_assurance_zero_post pc stackpointer ra (read events s) m s (FST t) /\
           SND t = a /\ abi_required_controls_preserved a (SND t)) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`6`;
    `bp_assurance_zero_post pc stackpointer ra (read events s) m s`;
    `bp_e2_crypto_allowed_read rp ordinary p q 0 stackpointer`;
    `bp_e2_crypto_allowed_write`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `s:x86state`; `a:abi_omitted_state`] ASSURANCE_E2_POLICY_PRODUCT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ASSURANCE_E2_ZERO_POLICY_FRAME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let ASSURANCE_E2_16_EXTENDED_ABI = prove
 (`!pc stackpointer ra p q m rp xp ordinary s a.
    bp_e2_crypto_pre pc stackpointer ra p q 16 m rp xp ordinary s
    ==> eventually_n abi_scalar_extended_step 15
      (\t. bp_assurance_16_post pc stackpointer ra p q (read events s) m s (FST t) /\
           SND t = a /\ abi_required_controls_preserved a (SND t)) (s,a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`15`;
    `bp_assurance_16_post pc stackpointer ra p q (read events s) m s`;
    `bp_e2_crypto_allowed_read rp ordinary p q 16 stackpointer`;
    `bp_e2_crypto_allowed_write`; `bp_e2_crypto_allowed_fetch xp ordinary pc`;
    `s:x86state`; `a:abi_omitted_state`] ASSURANCE_E2_POLICY_PRODUCT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ASSURANCE_E2_16_POLICY_FRAME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;
