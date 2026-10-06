(* Successor-local first milestone: actual prefix, opaque first call, actual cleanup handoff.
 No supplier-body execution or new generic composition rule. *)
let C3S_FIRST_CALL_COMPLETED = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
 ==> assurance_checked_run (bp_assurance_call_steps n) (\t:x86state. ?entry:x86state.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x23001138)
 p q n(read events entry)(read memory entry)entry t)
 (c3_segment_policy stackpointer p q n m rp wp xp ordinary) entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`bp_assurance_call_steps n`;
 `bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x23001138)p q n(read events entry)(read memory entry)entry`;
 `\t:x86state. ?entry:x86state.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x23001138)
 p q n(read events entry)(read memory entry)entry t`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`entry:x86state`]RA_CHECKED_RUN_POST_MONO) THEN
 CONJ_TAC THENL
 [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[];
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
 `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`]C3_FIRST_CRYPTO_CALLER_POLICY_APPLICATION) THEN ASM_REWRITE_TAC[]]);;

let c3s_cleanup_chain_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary initial a.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary (initial,a)
 ==> assurance_checked_run (10+(bp_assurance_call_steps n+7)) (\t:x86state. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)rp wp xp ordinary(t,a) /\
 c3_saved_prefix stackpointer p q n m initial t /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial t)
 (c3_segment_policy stackpointer p q n m rp wp xp ordinary) initial`;;
let C3S_CLEANUP_CHAIN = prove(c3s_cleanup_chain_statement,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`10`;`bp_assurance_call_steps n`;`7`;
 `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a`;
 `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a`;
 `\t:x86state. ?entry:x86state.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x23001138)
 p q n(read events entry)(read memory entry)entry t`;`\t:x86state. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)rp wp xp ordinary(t,a) /\
 c3_saved_prefix stackpointer p q n m initial t /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial t`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`initial:x86state`]RA_CHECKED_RUN_THREE_SEGMENT) THEN
 REPEAT CONJ_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;
 `client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`]C3_HANDOFF) THEN ASM_REWRITE_TAC[];
 REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `entry:x86state` THEN DISCH_TAC THEN MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
 `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`]C3S_FIRST_CALL_COMPLETED) THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `returned:x86state` THEN BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;
 `client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
 `entry:x86state`;`returned:x86state`]C3_CLEANUP_HANDOFF) THEN ASM_REWRITE_TAC[];
 REWRITE_TAC[c3_segment_policy];REWRITE_TAC[c3_segment_policy];REWRITE_TAC[c3_segment_policy]]);;
if hyp C3S_CLEANUP_CHAIN<>[] || frees(concl C3S_CLEANUP_CHAIN)<>[] || not(aconv(concl C3S_CLEANUP_CHAIN)c3s_cleanup_chain_statement) then failwith "C3S_CLEANUP_CHAIN_LITERAL_CLOSURE";;
print_endline "C3S_CLEANUP_CHAIN_FROM_ORIGINAL_PRE_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
print_thm C3S_CLEANUP_CHAIN;;
