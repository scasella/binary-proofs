(* Concrete second-call entry, strengthened only by propagated caller facts.
   Raw ML literal: inherited HOL definition registry is unchanged. *)
let c3_second_handoff_complete_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 bp_e2_cleanse_public_pre lib_file(read memory entry)(read memory entry)(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry /\
 bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)entry returned
 ==> assurance_checked_run 5
 (\t:x86state. bp_e2_crypto_public_pre lib_file(read memory t)(read memory t)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory t)rp xp ordinary(t,a) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX initial /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial t)
 (c3_segment_policy stackpointer p q n m rp wp xp ordinary)returned`;;
let C3_SECOND_INITIAL_FACTS_TAC =
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `48<=val(stackpointer:int64)` ASSUME_TAC THENL
 [ACCEPT_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[c3_pre](ASSUME `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial,a)`))));ALL_TAC] THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_RETURN_WORKING_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_SAVED_BINDINGS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`n:num`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`;`returned:x86state`]C3_CLEANSE_LIBRARY_IMAGE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 UNDISCH_TAC `c3_loaded_code(returned:x86state)` THEN REWRITE_TAC[c3_loaded_code] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_got(returned:x86state)` THEN REWRITE_TAC[c3_got] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial,a)` THEN
 DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[c3_pre;c3_loaded_code;c3_got;C_ARGUMENTS]th)) THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
 `\a:num. rp a /\ ordinary a`;`initial:x86state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_CURRENT_INPUTS) THEN
 ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 C3_PREFIX_PERMISSION_TAC THEN C3_PREFIX_PROTECTION_TAC THEN
 SUBGOAL_THEN `MAYCHANGE [] (returned:x86state)returned` ASSUME_TAC THENL [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
 ABBREV_TAC `pc=0x23001120` THEN
 SUBGOAL_THEN `read RIP(returned:x86state)=word(pc+44)` ASSUME_TAC THENL [UNDISCH_TAC `read RIP(returned:x86state)=word 0x2300114c` THEN EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];ALL_TAC];;
let C3_SECOND_ACTUAL_FIVE_TAC =
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word pc)c3_caller_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001030)c3_crypto_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001040)c3_cleanse_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x10241840)crypto_memcmp_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x102417d0)openssl_cleanse_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "v1" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "v2" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "v3" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "v4" THEN
 SUBGOAL_THEN `read RIP(v4:x86state)=word 0x23001030` ASSUME_TAC THENL
 [UNDISCH_TAC `read RIP(v4:x86state)=word(pc+18446744073709551376)` THEN EXPAND_TAC "pc" THEN REWRITE_TAC[C3_FIRST_PLT_ADDRESS];ALL_TAC] THEN
 ABBREV_TAC `secondpltpc=0x23001030` THEN
 C3_PLT_CHECKED_STEP_TAC "secondpltpc" C3_CRYPTO_PLT_EXEC C3_CALLER_SUBTHS "v5";;
