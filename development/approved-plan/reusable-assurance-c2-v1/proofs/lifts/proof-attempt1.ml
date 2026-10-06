(* C2 O6 lifts: C1 proof2 recipe was inspected, but no C1 theorem is imported.
   New caller-specific instantiations of unchanged public E5/generic rules.
   CONSTRUCTED_NOT_CHECKED until actual reconstruction succeeds. *)
let c2_step_policy_qualified_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k source target:x86state.
    c2_step_policy stackpointer p q n m rp wp xp ordinary k source target
    ==> abi_all_decodes_caller_scalar source`;;
let C2_STEP_POLICY_QUALIFIED = prove
 (c2_step_policy_qualified_statement,
  REWRITE_TAC[c2_step_policy] THEN MESON_TAC[]);;
let C2_COMPOSITION_CHECKED_TAC =
 MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
   `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
   `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
   `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
   `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;
   `a:abi_omitted_state`] C2_CALLER_CHECKED) THEN ASM_REWRITE_TAC[];;
let C2_COMPOSITION_NORMAL_TAC (asl,w) =
 let expanded=REWRITE_RULE[c2_pre] (ASSUME
  `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary (s,a)`) in
 ACCEPT_TAC(find(fun th -> aconv w (concl th)) (CONJUNCTS expanded)) (asl,w);;
let C2_COMPOSITION_QUALIFIED_TAC =
 REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `k:num`;`source:x86state`;`target:x86state`] C2_STEP_POLICY_QUALIFIED) THEN
 ASM_REWRITE_TAC[];;
let C2_CALLER_INTERFACE = prove
 (c2_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (let p=`\t:x86state#abi_omitted_state.
     c2_scalar_post stackpointer ra p q n m s (FST t) /\ SND t=a` in
   let q=`c2_public_post stackpointer ra p q n m s a` in
   let projection=prove(mk_forall(`t:x86state#abi_omitted_state`,
     mk_imp(mk_comb(p,`t:x86state#abi_omitted_state`),
            mk_comb(q,`t:x86state#abi_omitted_state`))),
     BETA_TAC THEN REWRITE_TAC[c2_public_post] THEN
     MESON_TAC[ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS]) in
   MATCH_MP_TAC (MATCH_MP (ISPECL [`abi_caller_scalar_extended_step`;p;q;
     `c2_steps p q n m`;`(s:x86state,a:abi_omitted_state)`] EVENTUALLY_N_MONO) projection)) THEN
  MATCH_MP_TAC (ISPECL [`c2_steps p q n m`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary`;
    `s:x86state`;`a:abi_omitted_state`] ABI_CALLER_CHECKED_RUN_LIFT) THEN
  MATCH_MP_TAC (ISPECL [`c2_steps p q n m`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary`;
    `\k source target. c2_step_policy stackpointer p q n m rp wp xp ordinary
       k source target /\ abi_all_decodes_caller_scalar source`;
    `s:x86state`] RA_CHECKED_RUN_POLICY_MONO) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `k:num`;`source:x86state`;`target:x86state`] C2_STEP_POLICY_QUALIFIED) THEN ASM_REWRITE_TAC[]];
    C2_COMPOSITION_CHECKED_TAC]);;
let C2_CALLER_NORMAL_CHECKED = prove
 (c2_normal_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`c2_steps p q n m`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary`;`s:x86state`]
      E5_CHECKED_RUN_NORMAL) THEN
  REPEAT CONJ_TAC THENL
   [C2_COMPOSITION_QUALIFIED_TAC;C2_COMPOSITION_CHECKED_TAC;C2_COMPOSITION_NORMAL_TAC]);;
let C2_CALLER_RF_NORMAL_CHECKED = prove
 (c2_rf_normal_checked_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`c2_steps p q n m`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary`;`s:x86state`]
      E5_RF_CHECKED_RUN_NORMAL) THEN
  REPEAT CONJ_TAC THENL
   [C2_COMPOSITION_QUALIFIED_TAC;C2_COMPOSITION_CHECKED_TAC;C2_COMPOSITION_NORMAL_TAC]);;
let C2_CALLER_NORMAL_INTERFACE = prove
 (c2_normal_interface_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (let p=`\t:x86state#abi_omitted_state.
      c2_scalar_post stackpointer ra p q n m s (FST t) /\ e5_normal_flags(FST t) /\
      SND t=a /\ abi_required_controls_preserved a (SND t)` in
   let q=`\t:x86state#abi_omitted_state.
      c2_public_post stackpointer ra p q n m s a t /\ e5_normal_flags(FST t)` in
   let projection=prove(mk_forall(`t:x86state#abi_omitted_state`,
     mk_imp(mk_comb(p,`t:x86state#abi_omitted_state`),
            mk_comb(q,`t:x86state#abi_omitted_state`))),
     BETA_TAC THEN REWRITE_TAC[c2_public_post] THEN MESON_TAC[]) in
   MATCH_MP_TAC (MATCH_MP (ISPECL [`e5_rf_retired_extended_step`;p;q;
     `c2_steps p q n m`;`(s:x86state,a:abi_omitted_state)`] EVENTUALLY_N_MONO) projection)) THEN
  MATCH_MP_TAC (ISPECL [`c2_steps p q n m`;
    `c2_scalar_post stackpointer ra p q n m s`;
    `c2_step_policy stackpointer p q n m rp wp xp ordinary`;
    `s:x86state`;`a:abi_omitted_state`] E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT) THEN
  REPEAT CONJ_TAC THENL
   [C2_COMPOSITION_QUALIFIED_TAC;C2_COMPOSITION_CHECKED_TAC;C2_COMPOSITION_NORMAL_TAC]);;
let C2_CALLER_COUNT = prove
 (c2_count_statement,REWRITE_TAC[c2_steps;bp_assurance_call_steps]);;
