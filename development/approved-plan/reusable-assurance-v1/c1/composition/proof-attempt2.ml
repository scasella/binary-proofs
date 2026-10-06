(* Retains source1 static-invalid tab binders; literal lambda t repair only. *)
(* Frozen original end statements. Public handoff/callee completion/tail
   objects are composed; no byte decoder or execution rule occurs here. *)
let C1_CRYPTO_CALLER_CHECKED = prove
 (c1_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[c1_steps;ARITH_RULE `8+b=3+(b+5)`] THEN
  MATCH_MP_TAC (ISPECL [`3`;`bp_assurance_call_steps n`;`5`;
    `c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary s a`;
    `c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary s a`;
    `c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary s a`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_segment_policy stackpointer p q n rp wp xp ordinary`;
    `c1_segment_policy stackpointer p q n rp wp xp ordinary`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;`s:x86state`]
     RA_CHECKED_RUN_THREE_SEGMENT) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
      `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
      `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
      `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;
      `a:abi_omitted_state`] C1_CRYPTO_HANDOFF) THEN ASM_REWRITE_TAC[];
    MESON_TAC[];
    X_GEN_TAC `entry:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC C1_CRYPTO_COMPLETED_RUN THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
      `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
      `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
      `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;
      `a:abi_omitted_state`;`returned:x86state`] C1_COMPLETED_TAIL_RUN) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC C1_SHIFTED_SEGMENT_POLICY THEN CONJ_TAC THENL
     [ARITH_TAC;ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC C1_SHIFTED_SEGMENT_POLICY THEN CONJ_TAC THENL
     [ARITH_TAC;ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;
let C1_COMPOSITION_CHECKED_TAC =
 MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
   `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
   `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
   `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
   `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;
   `a:abi_omitted_state`] C1_CRYPTO_CALLER_CHECKED) THEN ASM_REWRITE_TAC[];;
let C1_COMPOSITION_NORMAL_TAC (asl,w) =
 let expanded=REWRITE_RULE[c1_pre] (ASSUME
  `c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary (s,a)`) in
 ACCEPT_TAC(find(fun th -> aconv w (concl th)) (CONJUNCTS expanded)) (asl,w);;
let C1_COMPOSITION_QUALIFIED_TAC =
 REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC C1_STEP_POLICY_QUALIFIED THEN
 ASM_REWRITE_TAC[];;
let C1_CRYPTO_CALLER_INTERFACE = prove
 (c1_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (let p=`\t:x86state#abi_omitted_state.
     c1_scalar_post stackpointer ra p q n m s (FST t) /\ SND t=a` in
   let q=`c1_public_post stackpointer ra p q n m s a` in
   let projection=prove(mk_forall(`t:x86state#abi_omitted_state`,
     mk_imp(mk_comb(p,`t:x86state#abi_omitted_state`),
            mk_comb(q,`t:x86state#abi_omitted_state`))),
     BETA_TAC THEN REWRITE_TAC[c1_public_post] THEN
     MESON_TAC[ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS]) in
   MATCH_MP_TAC (MATCH_MP (ISPECL [`abi_caller_scalar_extended_step`;p;q;
     `c1_steps n`;`(s:x86state,a:abi_omitted_state)`] EVENTUALLY_N_MONO) projection)) THEN
  MATCH_MP_TAC (ISPECL [`c1_steps n`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;
    `s:x86state`;`a:abi_omitted_state`] ABI_CALLER_CHECKED_RUN_LIFT) THEN
  MATCH_MP_TAC (ISPECL [`c1_steps n`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;
    `\k source target. c1_step_policy stackpointer p q n rp wp xp ordinary
       k source target /\ abi_all_decodes_caller_scalar source`;
    `s:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];MATCH_MP_TAC C1_STEP_POLICY_QUALIFIED THEN ASM_REWRITE_TAC[]];
    C1_COMPOSITION_CHECKED_TAC]);;
let C1_CRYPTO_CALLER_NORMAL_CHECKED = prove
 (c1_normal_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`c1_steps n`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;`s:x86state`]
      E5_CHECKED_RUN_NORMAL) THEN
  REPEAT CONJ_TAC THENL
   [C1_COMPOSITION_QUALIFIED_TAC;C1_COMPOSITION_CHECKED_TAC;C1_COMPOSITION_NORMAL_TAC]);;
let C1_CRYPTO_CALLER_RF_NORMAL_CHECKED = prove
 (c1_rf_normal_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`c1_steps n`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;`s:x86state`]
      E5_RF_CHECKED_RUN_NORMAL) THEN
  REPEAT CONJ_TAC THENL
   [C1_COMPOSITION_QUALIFIED_TAC;C1_COMPOSITION_CHECKED_TAC;C1_COMPOSITION_NORMAL_TAC]);;
let C1_CRYPTO_CALLER_NORMAL_INTERFACE = prove
 (c1_normal_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (let p=`\t:x86state#abi_omitted_state.
      c1_scalar_post stackpointer ra p q n m s (FST t) /\ e5_normal_flags(FST t) /\
      SND t=a /\ abi_required_controls_preserved a (SND t)` in
   let q=`\t:x86state#abi_omitted_state.
      c1_public_post stackpointer ra p q n m s a t /\ e5_normal_flags(FST t)` in
   let projection=prove(mk_forall(`t:x86state#abi_omitted_state`,
     mk_imp(mk_comb(p,`t:x86state#abi_omitted_state`),
            mk_comb(q,`t:x86state#abi_omitted_state`))),
     BETA_TAC THEN REWRITE_TAC[c1_public_post] THEN MESON_TAC[]) in
   MATCH_MP_TAC (MATCH_MP (ISPECL [`e5_rf_retired_extended_step`;p;q;
     `c1_steps n`;`(s:x86state,a:abi_omitted_state)`] EVENTUALLY_N_MONO) projection)) THEN
  MATCH_MP_TAC (ISPECL [`c1_steps n`;
    `c1_scalar_post stackpointer ra p q n m s`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;
    `s:x86state`;`a:abi_omitted_state`] E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT) THEN
  REPEAT CONJ_TAC THENL
   [C1_COMPOSITION_QUALIFIED_TAC;C1_COMPOSITION_CHECKED_TAC;C1_COMPOSITION_NORMAL_TAC]);;
let C1_CRYPTO_CALLER_COUNT = prove
 (c1_count_statement,REWRITE_TAC[c1_steps;bp_assurance_call_steps]);;
