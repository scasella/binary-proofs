(* Fixed C3 phase composition using unchanged exported rules. Raw literal ML terms,
 no new HOL definition or generic algorithm. Source construction is not checking. *)
let c3s_cleanup_q = `\t:x86state. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)rp wp xp ordinary(t,a) /\
 c3_saved_prefix stackpointer p q n m initial t /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial t`;;
let c3s_second_q = `\t:x86state. bp_e2_crypto_public_pre lib_file(read memory t)(read memory t)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory t)rp xp ordinary(t,a) /\
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
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial t`;;
let C3S_CLEANSE_COMPLETED = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary initial a entry.
 (bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial entry) ==> assurance_checked_run(cleanse_functional_steps p n)
 (\t:x86state. ?entry:x86state. (bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial entry) /\ bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)entry t)(c3_segment_policy stackpointer p q n m rp wp xp ordinary)entry`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`cleanse_functional_steps p n`;`bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory(entry:x86state))entry`;`\t:x86state. ?entry:x86state. (bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial entry) /\ bp_e2_cleanse_call_post 0x102417d0(word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)entry t`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`entry:x86state`]RA_CHECKED_RUN_POST_MONO) THEN CONJ_TAC THENL
 [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[];
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]C3_CLEANSE_CALLER_POLICY_APPLICATION) THEN
 ACCEPT_TAC(CONJUNCT1(ASSUME `bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
 (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)rp wp xp ordinary(entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) initial entry`))]);;
if hyp C3S_CLEANSE_COMPLETED<>[] || frees(concl C3S_CLEANSE_COMPLETED)<>[] then failwith "C3S_CLEANSE_COMPLETED_CLOSURE";;
