(* Fixed C3 whole chain, unchanged literal end-theorem and supplier interfaces. *)
let C3S_SECOND_CALL_SUFFIX = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary initial a entry. c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial,a) /\ (bp_e2_crypto_public_pre lib_file(read memory entry)(read memory entry)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory entry)rp xp ordinary(entry,a) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))entry=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))entry=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))entry=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))entry=read RBX initial /\
 read(memory :> bytes64 stackpointer)entry=ra /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 read DF entry=F /\ ~bit 18(read rflags entry) /\
 (!i. i<n ==> read memory entry(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory entry(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory entry addr=m addr) /\
 c3_loaded_code entry /\ c3_got entry /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry) ==> assurance_checked_run(bp_assurance_call_steps n)
 (\t:x86state.  48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP t=word 0x2300115a /\ read RSP t=word_sub stackpointer(word 40) /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX t=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX initial /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial t /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89)(c3_segment_policy stackpointer p q n m rp wp xp ordinary)entry`,
 REPEAT GEN_TAC THEN DISCH_THEN(fun all -> ASSUME_TAC(CONJUNCT1 all) THEN ASSUME_TAC(CONJUNCT2 all)) THEN
 MATCH_MP_TAC(ISPECL[`bp_assurance_call_steps n`;`bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read events(entry:x86state))(read memory entry)entry`;`\t:x86state.  48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP t=word 0x2300115a /\ read RSP t=word_sub stackpointer(word 40) /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX t=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX initial /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial t /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`entry:x86state`]RA_CHECKED_RUN_POST_MONO) THEN CONJ_TAC THENL
 [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN BETA_TAC THEN
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_SECOND_PUBLIC_RETURN_TO_SUFFIX) THEN ASM_REWRITE_TAC[];
 MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`]C3_SECOND_CRYPTO_CALLER_POLICY_APPLICATION) THEN
 ACCEPT_TAC(CONJUNCT1(ASSUME `bp_e2_crypto_public_pre lib_file(read memory entry)(read memory entry)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory entry)rp xp ordinary(entry,a) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))entry=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))entry=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))entry=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))entry=read RBX initial /\
 read(memory :> bytes64 stackpointer)entry=ra /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 entry=read R14 initial /\ read R15 entry=read R15 initial /\
 read DF entry=F /\ ~bit 18(read rflags entry) /\
 (!i. i<n ==> read memory entry(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory entry(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory entry addr=m addr) /\
 c3_loaded_code entry /\ c3_got entry /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry`))]);;
let C3_CHECKED = prove(c3_checked_statement,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 (* The frozen whole theorem uses s; use it as the concrete initial state. *)
 SUBGOAL_THEN `c3_steps p q n m = ((10+(bp_assurance_call_steps n+7))+(cleanse_functional_steps p n+5))+(bp_assurance_call_steps n+(if c3_equal m p q n then 12 else 9))` SUBST1_TAC THENL
 [REWRITE_TAC[c3_steps] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
 MATCH_MP_TAC(ISPECL[`(10+(bp_assurance_call_steps n+7))+(cleanse_functional_steps p n+5)`;`bp_assurance_call_steps n`;`if c3_equal m p q n then 12 else 9`;`\t:x86state. bp_e2_crypto_public_pre lib_file(read memory t)(read memory t)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory t)rp xp ordinary(t,a) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 s /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 s /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP s /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX s /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])s t`;`\t:x86state. bp_e2_crypto_public_pre lib_file(read memory t)(read memory t)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory t)rp xp ordinary(t,a) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 s /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 s /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP s /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX s /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])s t`;`\t:x86state.  48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP t=word 0x2300115a /\ read RSP t=word_sub stackpointer(word 40) /\
 read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX t=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))t=read R13 s /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))t=read R12 s /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))t=read RBP s /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))t=read RBX s /\
 read(memory :> bytes64 stackpointer)t=ra /\
 read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=F /\ ~bit 18(read rflags t) /\
 (!i. i<n ==> read memory t(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory t(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory t addr=m addr) /\
 c3_loaded_code t /\ c3_got t /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])s t /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89`;`c3_scalar_post stackpointer ra p q n m s`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`c3_step_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;`s:x86state`]RA_CHECKED_RUN_THREE_SEGMENT) THEN REPEAT CONJ_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;`a:abi_omitted_state`]C3S_SECOND_ENTRY_CHAIN) THEN ASM_REWRITE_TAC[];
 REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `entry:x86state` THEN DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;`a:abi_omitted_state`;`entry:x86state`]C3S_SECOND_CALL_SUFFIX) THEN ASM_REWRITE_TAC[];
 X_GEN_TAC `entry:x86state` THEN DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s:x86state`;`entry:x86state`]C3_FINAL_RETURN_SITE) THEN ASM_REWRITE_TAC[];
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_segment_policy;c3_step_policy] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_segment_policy;c3_step_policy] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
 REWRITE_TAC[]]);;
if hyp C3_CHECKED<>[] || frees(concl C3_CHECKED)<>[] || not(aconv(concl C3_CHECKED)c3_checked_statement) then failwith "C3_CHECKED_LITERAL_CLOSURE";;
print_endline "C3_SUCCESSOR_WHOLE_CHECKED_DEVELOPMENT_ONLY_NOT_ACCEPTANCE";;
print_thm C3_CHECKED;;
