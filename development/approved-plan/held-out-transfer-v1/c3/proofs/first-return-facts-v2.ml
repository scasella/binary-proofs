(* Version2: match the existing symbolic MAYCHANGE SOME_FLAGS premise before expanding the orthogonality obligations.
  Concrete first-call continuation working/saved state, proved only from public post/frame.
  Named obligation: actual seven-step unconditional cleanse handoff after first comparison. *)
let C3_FIRST_RETURN_WORKING_STATE = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry returned.
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48)) (word 0x23001138) p q n
 (read events entry) (read memory entry) entry returned
 ==> read RBX returned=p /\
 read RBP returned=word n /\
 read R12 returned=q /\
 read R13 returned=read R13 initial /\
 read R14 returned=read R14 initial /\
 read R15 returned=read R15 initial /\
 read DF returned=F /\
 ~bit 18(read rflags returned)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`initial:x86state`;`entry:x86state`]C3_PREFIX_FRAME_OUTSIDE) THEN
 UNDISCH_TAC `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry` THEN
 REWRITE_TAC[c3_crypto_ready;c3_saved_prefix;bp_e2_crypto_public_pre;bp_e2_crypto_pre;C_ARGUMENTS] THEN
 STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48)) (word 0x23001138) p q n
 (read events(entry:x86state)) (read memory entry) entry returned` THEN
 REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
 REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(ISPECL[`RBX:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`RBP:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R12:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R14:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R15:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`DF:(x86state,bool)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`(rflags :> bitelement 18):(x86state,bool)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[]:((x86state,int64)component)list`;
 `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
 R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[MAYCHANGE_LID;ALL] THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]]]);;
