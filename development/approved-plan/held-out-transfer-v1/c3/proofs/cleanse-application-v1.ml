(* Actual C3 second call: direct public precondition at S-48, continuation
   0x2300114c; no new phase predicate, generic rule, or supplier execution.
   Named obligation: apply the unchanged cleanse interface and lift its access
   policy after the actual seven-step caller/PLT handoff. *)
let C3_CLEANSE_PUBLIC_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p n rp wp xp ordinary entry a.
   bp_e2_cleanse_public_pre lib_file (read memory entry) (read memory entry)
     (word_sub stackpointer(word 48)) (word 0x2300114c) p n
     (read memory entry) rp wp xp ordinary (entry,a)
   ==> assurance_checked_run (cleanse_functional_steps p n)
     (bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer(word 48))
       (word 0x2300114c) p n (read memory entry) entry)
     (\k source target. cleanse_access_covered_step 0x102417d0
       (bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer(word 48)))
       (bp_e2_cleanse_allowed_write wp ordinary p n)
       (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
       k source target /\ abi_all_decodes_caller_scalar source) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`read memory(entry:x86state)`;
   `read memory(entry:x86state)`;`word_sub(stackpointer:int64)(word 48)`;
   `word 0x2300114c:int64`;`p:int64`;`n:num`;`read memory(entry:x86state)`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `entry:x86state`;`a:abi_omitted_state`]BP_E3_CLEANSE_PUBLIC_CALLER_POLICY) THEN
 ASM_REWRITE_TAC[]);;

let C3_CLEANSE_READ_POLICY_INCLUDED = prove
 (`!stackpointer p q:int64 n rp ordinary addr.
   bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer(word 48)) addr
   ==> c3_allowed_read rp ordinary stackpointer p q n addr`,
 REPEAT GEN_TAC THEN
 REWRITE_TAC[bp_e2_cleanse_allowed_read;c3_allowed_read;c3_scratch;assurance_region] THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C3_CLEANSE_WRITE_POLICY_INCLUDED = prove
 (`!stackpointer p q:int64 n m wp ordinary addr.
   bp_e2_cleanse_allowed_write wp ordinary p n addr
   ==> c3_allowed_write wp ordinary stackpointer p q n m addr`,
 REWRITE_TAC[bp_e2_cleanse_allowed_write;c3_allowed_write] THEN MESON_TAC[]);;

let C3_CLEANSE_FETCH_POLICY_INCLUDED = prove
 (`!xp ordinary addr.
   bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0 addr
   ==> c3_allowed_fetch xp ordinary addr`,
 REWRITE_TAC[bp_e2_cleanse_allowed_fetch;c3_allowed_fetch] THEN MESON_TAC[]);;

let C3_CLEANSE_POLICY_INCLUDED = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary k source target.
   cleanse_access_covered_step 0x102417d0
     (bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer(word 48)))
     (bp_e2_cleanse_allowed_write wp ordinary p n)
     (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
     k source target /\ abi_all_decodes_caller_scalar source
   ==> c3_segment_policy stackpointer p q n m rp wp xp ordinary k source target`,
 REPEAT GEN_TAC THEN REWRITE_TAC[cleanse_access_covered_step;assurance_zero_step] THEN
 STRIP_TAC THEN REWRITE_TAC[c3_segment_policy] THEN ASM_REWRITE_TAC[] THEN
 MATCH_MP_TAC HT_POLICY_STEP_MONO THEN
 EXISTS_TAC `bp_e2_cleanse_allowed_read rp ordinary (word_sub(stackpointer:int64)(word 48))` THEN
 EXISTS_TAC `bp_e2_cleanse_allowed_write wp ordinary (p:int64) (n:num)` THEN
 EXISTS_TAC `bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0` THEN
 ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
 [MESON_TAC[C3_CLEANSE_READ_POLICY_INCLUDED];
  MESON_TAC[C3_CLEANSE_WRITE_POLICY_INCLUDED];
  MESON_TAC[C3_CLEANSE_FETCH_POLICY_INCLUDED]]);;

let C3_CLEANSE_CALLER_POLICY_APPLICATION = prove
 (`!lib_file stackpointer p q:int64 n m rp wp xp ordinary entry a.
   bp_e2_cleanse_public_pre lib_file (read memory entry) (read memory entry)
     (word_sub stackpointer(word 48)) (word 0x2300114c) p n
     (read memory entry) rp wp xp ordinary (entry,a)
   ==> assurance_checked_run (cleanse_functional_steps p n)
     (bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer(word 48))
       (word 0x2300114c) p n (read memory entry) entry)
     (c3_segment_policy stackpointer p q n m rp wp xp ordinary) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`cleanse_functional_steps (p:int64)(n:num)`;
   `bp_e2_cleanse_call_post 0x102417d0 (word_sub(stackpointer:int64)(word 48))
      (word 0x2300114c) p n (read memory(entry:x86state)) entry`;
   `\k source target. cleanse_access_covered_step 0x102417d0
       (bp_e2_cleanse_allowed_read rp ordinary (word_sub(stackpointer:int64)(word 48)))
       (bp_e2_cleanse_allowed_write wp ordinary p n)
       (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
       k source target /\ abi_all_decodes_caller_scalar source`;
   `c3_segment_policy stackpointer p q n m rp wp xp ordinary`;`entry:x86state`]
   RA_CHECKED_RUN_POLICY_MONO) THEN
 CONJ_TAC THENL
 [REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `k:num`;`source:x86state`;`target:x86state`]C3_CLEANSE_POLICY_INCLUDED) THEN
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`n:num`;
    `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `entry:x86state`;`a:abi_omitted_state`]C3_CLEANSE_PUBLIC_POLICY_APPLICATION) THEN
  ASM_REWRITE_TAC[]]);;
print_endline "C3_CLEANSE_APPLICATION_V1_DEVELOPMENT_CHECKED";;
