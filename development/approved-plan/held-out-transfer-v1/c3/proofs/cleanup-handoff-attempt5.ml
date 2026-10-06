(* Concrete C3 path obligation: first comparison return to actual unconditional
 cleanup entry through six caller instructions and the actual cleanse PLT.
 These local premises must be discharged in C3 composition from the original
 frozen precondition and public comparison post. They are not new public premises. *)
let c3_cleanup_handoff_abi_local_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48))
   (word 0x23001138) p q n (read events entry)(read memory entry) entry returned
 ==> assurance_checked_run 7
  (\t. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
      (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)
      rp wp xp ordinary (t,a) /\
      c3_saved_prefix stackpointer p q n m initial t /\
      read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
      read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
      (c3_frame stackpointer p q n m ,, MAYCHANGE [RBX;RBP;R12;R13]) initial t)
  (c3_segment_policy stackpointer p q n m rp wp xp ordinary) returned`;;

let C3_CLEANUP_PLT_ADDRESS = prove
 (`(word(0x23001120+18446744073709551392):int64)=word 0x23001040`,
 GEN_REWRITE_TAC LAND_CONV[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let C3_CLEANUP_INITIAL_FACTS_TAC =
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_RETURN_WORKING_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_RETURN_SAVED_PREFIX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_COMPARISON_RESULT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 UNDISCH_TAC `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48))
   (word 0x23001138) p q n (read events(entry:x86state))(read memory entry) entry returned` THEN
 REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
 SUBGOAL_THEN `read RSP(returned:x86state)=word_sub(stackpointer:int64)(word 40)` ASSUME_TAC THENL
 [ACCEPT_TAC(MATCH_MP(ISPECL[`stackpointer:int64`;`returned:x86state`]C3_FIRST_RETURN_STACKPOINTER)
   (CONJ(CONJUNCT1(CONJUNCT2(REWRITE_RULE[c3_pre](ASSUME
    `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a)`))))
    (ASSUME `val(read RSP(returned:x86state))=val(word_sub(stackpointer:int64)(word 48))+8`)));ALL_TAC];;
let C3_CLEANUP_PERMISSION_FACTS_TAC = UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(returned:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix;c3_loaded_code;c3_got] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary (initial,a)` THEN
 REWRITE_TAC[c3_pre;c3_loaded_code;c3_got;C_ARGUMENTS] THEN STRIP_TAC THEN
 C3_PREFIX_PERMISSION_TAC THEN C3_PREFIX_PROTECTION_TAC THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001040 6` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_CLEANSE_PLT_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)0x23003fd8 8` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_CLEANSE_GOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `MAYCHANGE [] (returned:x86state) returned` ASSUME_TAC THENL
 [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
 ABBREV_TAC `pc=0x23001120` THEN
 SUBGOAL_THEN `read RIP(returned:x86state)=word(pc+24)` ASSUME_TAC THENL
 [UNDISCH_TAC `read RIP(returned:x86state)=word 0x23001138` THEN
  EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];ALL_TAC];;
let C3_CLEANUP_ACTUAL_SEVEN_TAC = 
 (* Concrete backward proof weakening: discard only five obsolete initial-state
    loaded-code facts after current-returned bindings have been derived. The
    frozen FIRST_X_ASSUM updater remains unchanged and now sees current facts. *)
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word pc)c3_caller_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001030)c3_crypto_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001040)c3_cleanse_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x10241840)crypto_memcmp_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x102417d0)openssl_cleanse_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u1" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u2" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u3" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u4" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u5" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u6" THEN
 SUBGOAL_THEN `read RIP(u6:x86state)=word 0x23001040` ASSUME_TAC THENL
 [UNDISCH_TAC `read RIP(u6:x86state)=word(pc+18446744073709551392)` THEN
  EXPAND_TAC "pc" THEN REWRITE_TAC[C3_CLEANUP_PLT_ADDRESS];ALL_TAC] THEN
 ABBREV_TAC `cleansepltpc=0x23001040` THEN
 C3_PLT_CHECKED_STEP_TAC "cleansepltpc" C3_CLEANSE_PLT_EXEC C3_CALLER_SUBTHS "u7";;
g c3_cleanup_handoff_abi_local_statement;;
e C3_CLEANUP_INITIAL_FACTS_TAC;;
print_endline "C3_CLEANUP_INITIAL_FACTS_V5_RETURN";;
e C3_CLEANUP_PERMISSION_FACTS_TAC;;
print_endline "C3_CLEANUP_PERMISSION_FACTS_V5_RETURN";;
e C3_CLEANUP_ACTUAL_SEVEN_TAC;;
print_endline "C3_CLEANUP_ACTUAL_SEVEN_V5_RETURN";;
print_endline("C3_CLEANUP_ABI_SEVEN_STEP_RESIDUAL "^string_of_term(snd(top_goal())));;
