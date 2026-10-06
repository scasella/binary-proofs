(* Repeated use of the unchanged public supplier theorem at the actual third
 call continuation 0x2300115a. No implementation semantics are consumed. *)
let C3_SECOND_CRYPTO_PUBLIC_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p q:int64 n rp xp ordinary entry a.
 bp_e2_crypto_public_pre lib_file (read memory entry)(read memory entry)
   (word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory entry)
   rp xp ordinary (entry,a)
 ==> assurance_checked_run (bp_assurance_call_steps n)
   (bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48))
     (word 0x2300115a)p q n(read events entry)(read memory entry)entry)
   (\k source target. bp_assurance_step_policy
      (bp_e2_crypto_allowed_read rp ordinary (word_sub stackpointer(word 48))p q n)
      (bp_e2_crypto_allowed_write)
      (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
      k source target /\ abi_all_decodes_caller_scalar source) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`read memory(entry:x86state)`;
   `read memory(entry:x86state)`;`word_sub(stackpointer:int64)(word 48)`;
   `word 0x2300115a:int64`;`p:int64`;`q:int64`;`n:num`;`read memory(entry:x86state)`;
   `rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `entry:x86state`;`a:abi_omitted_state`]BP_E3_CRYPTO_PUBLIC_CALLER_POLICY) THEN
 ASM_REWRITE_TAC[]);;

let C3_SECOND_CRYPTO_CALLER_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p q:int64 n m rp wp xp ordinary entry a.
 bp_e2_crypto_public_pre lib_file (read memory entry)(read memory entry)
   (word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory entry)
   rp xp ordinary (entry,a)
 ==> assurance_checked_run (bp_assurance_call_steps n)
   (bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48))
     (word 0x2300115a)p q n(read events entry)(read memory entry)entry)
   (c3_segment_policy stackpointer p q n m rp wp xp ordinary) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`bp_assurance_call_steps(n:num)`;
   `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48))
      (word 0x2300115a)p q n(read events(entry:x86state))(read memory entry)entry`;
   `\k source target. bp_assurance_step_policy
      (bp_e2_crypto_allowed_read rp ordinary (word_sub(stackpointer:int64)(word 48))p q n)
      bp_e2_crypto_allowed_write
      (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
      k source target /\ abi_all_decodes_caller_scalar source`;
   `c3_segment_policy stackpointer p q n m rp wp xp ordinary`;`entry:x86state`]
 RA_CHECKED_RUN_POLICY_MONO) THEN CONJ_TAC THENL
 [REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `k:num`;`source:x86state`;`target:x86state`]C3_FIRST_CRYPTO_POLICY_INCLUDED) THEN
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
   `n:num`;`rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `entry:x86state`;`a:abi_omitted_state`]C3_SECOND_CRYPTO_PUBLIC_POLICY_APPLICATION) THEN
  ASM_REWRITE_TAC[]]);;
print_endline "C3_SECOND_CRYPTO_APPLICATION_V1_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
