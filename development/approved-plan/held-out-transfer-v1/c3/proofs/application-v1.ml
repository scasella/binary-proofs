(* First actual C3 call: only supplier public policy theorem plus frozen caller-ready definition. *)
let C3_FIRST_CRYPTO_PUBLIC_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry.
  c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
  ==> assurance_checked_run (bp_assurance_call_steps n)
    (bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48)) (word 0x23001138) p q n
     (read events entry) (read memory entry) entry)
    (\k source target. assurance_zero_step
      (bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer(word 48)))
      bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
      k source target /\ abi_all_decodes_caller_scalar source) entry`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_crypto_ready] THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`read memory(entry:x86state)`;`read memory(entry:x86state)`;
 `word_sub(stackpointer:int64)(word 48)`;`word 0x23001138:int64`;`p:int64`;`q:int64`;`n:num`;
 `read memory(entry:x86state)`;`rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]
 BP_E3_CRYPTO_PUBLIC_CALLER_POLICY) THEN ASM_REWRITE_TAC[]);;
(* Concrete return slot is part of this caller's fixed48-byte scratch. *)
let C3_FIRST_CRYPTO_READ_POLICY_INCLUDED = prove
 (`!stackpointer p q:int64 n rp ordinary addr.
 bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer(word 48)) addr
 ==> c3_allowed_read rp ordinary stackpointer p q n addr`,
 REWRITE_TAC[bp_e2_crypto_allowed_read;c3_allowed_read;c3_scratch;assurance_region] THEN ARITH_TAC);;
let C3_FIRST_CRYPTO_POLICY_INCLUDED = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary k source target.
 assurance_zero_step
   (bp_e2_crypto_allowed_read rp ordinary p q n(word_sub stackpointer(word 48)))
   bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840) k source target /\
 abi_all_decodes_caller_scalar source
 ==> c3_segment_policy stackpointer p q n m rp wp xp ordinary k source target`,
 REPEAT GEN_TAC THEN REWRITE_TAC[assurance_zero_step] THEN STRIP_TAC THEN
 REWRITE_TAC[c3_segment_policy] THEN ASM_REWRITE_TAC[] THEN
 MATCH_MP_TAC HT_POLICY_STEP_MONO THEN
 EXISTS_TAC `bp_e2_crypto_allowed_read rp ordinary p q n(word_sub(stackpointer:int64)(word 48))` THEN
 EXISTS_TAC `bp_e2_crypto_allowed_write` THEN
 EXISTS_TAC `bp_e2_crypto_allowed_fetch xp ordinary 0x10241840` THEN
 ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
 [MESON_TAC[C3_FIRST_CRYPTO_READ_POLICY_INCLUDED];
  REWRITE_TAC[bp_e2_crypto_allowed_write];
  REWRITE_TAC[bp_e2_crypto_allowed_fetch;c3_allowed_fetch;assurance_region;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]]);;
let C3_FIRST_CRYPTO_CALLER_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry.
  c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
  ==> assurance_checked_run (bp_assurance_call_steps n)
    (bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48)) (word 0x23001138) p q n
     (read events entry) (read memory entry) entry)
    (c3_segment_policy stackpointer p q n m rp wp xp ordinary) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RA_CHECKED_RUN_POLICY_MONO THEN
 EXISTS_TAC `\k source target. assurance_zero_step
      (bp_e2_crypto_allowed_read rp ordinary p q n (word_sub(stackpointer:int64)(word 48)))
      bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
      k source target /\ abi_all_decodes_caller_scalar source` THEN
 CONJ_TAC THENL [MESON_TAC[C3_FIRST_CRYPTO_POLICY_INCLUDED];
 MATCH_MP_TAC C3_FIRST_CRYPTO_PUBLIC_POLICY_APPLICATION THEN ASM_REWRITE_TAC[]]);;
