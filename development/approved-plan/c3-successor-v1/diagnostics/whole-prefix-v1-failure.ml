g c3s_second_chain_statement;;
e(
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`10+(bp_assurance_call_steps n+7)`;`cleanse_functional_steps p n`;`5`;`\t:x86state. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)rp wp xp ordinary(t,a) /\
 c3_saved_prefix stackpointer p q n m initial t /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial t`;`\t:x86state. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)rp wp xp ordinary(t,a) /\
 c3_saved_prefix stackpointer p q n m initial t /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial t`;`\t:x86state. ?entry:x86state. (bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial entry) /\ bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)entry t`;`\t:x86state. bp_e2_crypto_public_pre lib_file(read memory t)(read memory t)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory t)rp xp ordinary(t,a) /\
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
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial t`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`initial:x86state`]RA_CHECKED_RUN_THREE_SEGMENT) THEN REPEAT CONJ_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`]C3S_CLEANUP_CHAIN) THEN ASM_REWRITE_TAC[];
 REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `entry:x86state` THEN DISCH_TAC THEN MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`]C3S_CLEANSE_COMPLETED) THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `returned:x86state` THEN BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_SECOND_HANDOFF) THEN ASM_REWRITE_TAC[];
 REWRITE_TAC[c3_segment_policy];REWRITE_TAC[c3_segment_policy];REWRITE_TAC[c3_segment_policy]]);;
print_endline "C3S_SECOND_ENTRY_CHAIN_RESIDUAL_NOT_ACCEPTANCE";;
