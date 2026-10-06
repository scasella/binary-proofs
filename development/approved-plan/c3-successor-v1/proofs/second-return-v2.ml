(* Actual second public return to exact final-return-site-v5 antecedents.
   No synthetic suffix state, no supplier execution, and no new HOL definitions. *)
let C3_SECOND_CALL_FRAME_OUTSIDE = prove
 (`!stackpointer p q:int64 n entry returned:x86state.
 bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read events entry)(read memory entry)entry returned
 ==> read R13 returned=read R13 entry /\ read R14 returned=read R14 entry /\
 read R15 returned=read R15 entry /\ read DF returned=read DF entry /\
 bit 18(read rflags returned)=bit 18(read rflags entry)`,
 REPEAT GEN_TAC THEN REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
 REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN REPEAT CONJ_TAC THENL
 [MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;`[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R14:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;`[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R15:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;`[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`DF:(x86state,bool)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;`[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`(rflags :> bitelement 18):(x86state,bool)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;`[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]]]);;
let C3_SECOND_CALL_TOTAL_FRAME_INCLUDED = prove
 (`!stackpointer p q:int64 n m:int64->byte.
 ((c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) ,, (MAYCHANGE[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[events]))
 subsumed (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_frame;SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC);;

let c3_second_public_return_to_suffix_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial,a) /\
 (bp_e2_crypto_public_pre lib_file(read memory entry)(read memory entry)(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read memory entry)rp xp ordinary(entry,a) /\
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
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial entry) /\
 bp_assurance_call_post 0x10241840(word_sub stackpointer(word 48))(word 0x2300115a)p q n(read events entry)(read memory entry)entry returned
 ==>  48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
 read RIP returned=word 0x2300115a /\ read RSP returned=word_sub stackpointer(word 40) /\
 read R13 returned=(if c3_equal m p q n then word 1 else word 0) /\
 read RAX returned=(if c3_equal(c3_cleansed_memory m p n)p q n then word 0 else word 1) /\
 read(memory :> bytes64(word_sub stackpointer(word 8)))returned=read R13 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 16)))returned=read R12 initial /\
 read(memory :> bytes64(word_sub stackpointer(word 24)))returned=read RBP initial /\
 read(memory :> bytes64(word_sub stackpointer(word 32)))returned=read RBX initial /\
 read(memory :> bytes64 stackpointer)returned=ra /\
 read R14 returned=read R14 initial /\ read R15 returned=read R15 initial /\
 read DF returned=F /\ ~bit 18(read rflags returned) /\
 (!i. i<n ==> read memory returned(word_add p(word i))=word 0) /\
 (!i. i<n ==> read memory returned(word_add q(word i))=
     c3_cleansed_memory m p n(word_add q(word i))) /\
 (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
     ==> read memory returned addr=m addr) /\
 c3_loaded_code returned /\ c3_got returned /\
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial returned /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer-48)48 /\
 assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val stackpointer)8 /\
 assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89
`;;

let C3_SECOND_PUBLIC_RETURN_TO_SUFFIX = prove(c3_second_public_return_to_suffix_statement,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding stackpointer ra p q n m rp wp xp ordinary(initial:x86state,a:abi_omitted_state)` THEN
 DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[c3_pre]th)) THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`entry:x86state`;`returned:x86state`]C3_SECOND_CALL_FRAME_OUTSIDE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 SUBGOAL_THEN `c3_equal(read memory(entry:x86state))p q n <=> c3_equal(c3_cleansed_memory m p n)p q n` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`m:int64->byte`;`read memory(entry:x86state)`;`p:int64`;`q:int64`;`n:num`]C3_CURRENT_LOGICAL_SNAPSHOT_EQ) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 UNDISCH_TAC `bp_assurance_call_post 0x10241840(word_sub(stackpointer:int64)(word 48))(word 0x2300115a)p q n(read events(entry:x86state))(read memory entry)entry(returned:x86state)` THEN
 DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[bp_assurance_call_post;GSYM c3_equal]th)) THEN STRIP_TAC THEN
 SUBGOAL_THEN `read RSP(returned:x86state)=word_sub stackpointer(word 40)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`]C3_FIRST_RETURN_STACKPOINTER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])(initial:x86state)(returned:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]C3_SECOND_CALL_TOTAL_FRAME_INCLUDED)) THEN
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val(stackpointer:int64)-48)48` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`]C3_SCRATCH_READ_SPAN) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val(stackpointer:int64))8` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`]C3_INCOMING_READ_SPAN) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001120 89` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`]C3_CALLER_FETCH_SPAN) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 RULE_ASSUM_TAC(REWRITE_RULE[c3_loaded_code;c3_got;bytes_loaded;READ_COMPONENT_COMPOSE]) THEN
 REWRITE_TAC[c3_loaded_code;c3_got;bytes_loaded;READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[]);;
if hyp C3_SECOND_PUBLIC_RETURN_TO_SUFFIX<>[] || frees(concl C3_SECOND_PUBLIC_RETURN_TO_SUFFIX)<>[] ||
 not(aconv(concl C3_SECOND_PUBLIC_RETURN_TO_SUFFIX)c3_second_public_return_to_suffix_statement)
then failwith "C3_SUCCESSOR_SECOND_RETURN_SUFFIX_LITERAL_CLOSURE";;
print_endline "C3_SUCCESSOR_SECOND_PUBLIC_RETURN_TO_ACTUAL_SUFFIX_CHECKED_NOT_ACCEPTANCE";;
print_thm C3_SECOND_PUBLIC_RETURN_TO_SUFFIX;;
