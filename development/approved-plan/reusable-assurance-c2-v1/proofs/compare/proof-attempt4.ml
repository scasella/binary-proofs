(* C2-only public-contract composition; supplier instruction bodies are not unfolded. *)
let C2_CRYPTO_SEGMENT_APPLICATION = prove
 (c2_crypto_segment_application_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_crypto_ready] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`a:abi_omitted_state`;`entry:x86state`] C2_CRYPTO_INTERFACE_APPLICATION) THEN ASM_REWRITE_TAC[]);;
let C2_CRYPTO_COMPLETED_RUN = prove
 (c2_crypto_completed_run_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`bp_assurance_call_steps n`;
    `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 32))
      (word 0x22001132) p q n (read events (entry:x86state)) (read memory entry) entry`;
    `c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a:
       x86state->bool`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:
       num->x86state->x86state->bool`;`entry:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN
    REWRITE_TAC[c2_crypto_completed] THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`] C2_CRYPTO_SEGMENT_APPLICATION) THEN ASM_REWRITE_TAC[]]);;
let C2_COMPARE_MEMORY_CODE_GOT_TRANSPORT = prove
 (c2_compare_memory_code_got_transport_statement,
  REWRITE_TAC[c2_loaded_code;c2_got;bytes_loaded;READ_COMPONENT_COMPOSE] THEN MESON_TAC[]);;
let C2_COMPARE_MEMORY_SLOT_TRANSPORT = prove
 (c2_compare_memory_slot_transport_statement,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN MESON_TAC[]);;
let C2_CRYPTO_RESULT_TRANSPORT = prove
 (c2_crypto_result_transport_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_crypto_ready lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c2_crypto_ready;c2_saved_prefix] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 32))
     (word 0x22001132) p q n (read events (entry:x86state))
     (read memory entry) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i<n ==> read memory (entry:x86state) (word_add p (word i))=
                 read memory entry (word_add q (word i))) <=> c2_equal m p q n`
   ASSUME_TAC THENL
   [REWRITE_TAC[c2_equal] THEN ASM_MESON_TAC[];ASM_REWRITE_TAC[]]);;
let C2_CRYPTO_RETURN_STACK = prove
 (c2_crypto_return_stack_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64;
    ARITH_RULE `32<=x ==> 24<=x`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPEC `stackpointer:int64` C2_STACK_SUB32_VALUE) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C2_COMPARE_INITIAL_FACTS = prove
 (c2_compare_initial_facts_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_crypto_completed lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (returned:x86state)` THEN
  REWRITE_TAC[c2_crypto_completed] THEN
  DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `read RAX (returned:x86state)=(if c2_equal m p q n then word 0 else word 1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
      `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
      `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
      `entry:x86state`;`returned:x86state`] C2_CRYPTO_RESULT_TRANSPORT) THEN
    ASM_REWRITE_TAC[];ALL_TAC] THEN
  UNDISCH_TAC
   `c2_crypto_ready lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c2_crypto_ready;c2_saved_prefix] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 32))
     (word 0x22001132) p q n (read events (entry:x86state))
     (read memory entry) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`entry:x86state`;`returned:x86state`] C2_CRYPTO_PUBLIC_SAVED_PRESERVED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `read RSP (returned:x86state)=word_sub stackpointer (word 24)` ASSUME_TAC THENL
   [MATCH_MP_TAC C2_CRYPTO_RETURN_STACK THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `c2_loaded_code (returned:x86state) /\ c2_got returned`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[C2_COMPARE_MEMORY_CODE_GOT_TRANSPORT];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (ASM_MESON_TAC[C2_COMPARE_MEMORY_SLOT_TRANSPORT] ORELSE
   (fun gl -> print_endline "C2_COMPARE_INITIAL_FACT_RESIDUAL";
      print_goal gl; FAIL_TAC "C2 compare initial facts residual" gl)));;
