(* Concrete C3 cleanse return working state, derived from unchanged public
   entry/post/frame and caller saved-prefix. Named obligation: actual five-step
   second-comparison handoff. Local entry premises must be discharged by the
   protected caller precondition and actual cleanup handoff. *)
let C3_CLEANSE_RETURN_WORKING_STATE = prove
 (`!lib_file stackpointer p q n m rp wp xp ordinary initial a entry returned.
 bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
   (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)
   rp wp xp ordinary (entry,a) /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 read R13 entry=(if c3_equal m p q n then word 1 else word 0) /\
 48<=val(stackpointer:int64) /\
 bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> read RIP returned=word 0x2300114c /\
     read RSP returned=word_sub stackpointer(word 40) /\
     read RBX returned=p /\ read RBP returned=word n /\ read R12 returned=q /\
     read R13 returned=(if c3_equal m p q n then word 1 else word 0) /\
     read R14 returned=read R14 entry /\ read R15 returned=read R15 entry /\
     read DF returned=F /\ ~bit 18(read rflags returned)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_public_pre lib_file (read memory(entry:x86state))(read memory entry)
   (word_sub(stackpointer:int64)(word 48))(word 0x2300114c)p n(read memory entry)
   rp wp xp ordinary (entry,a)` THEN
 REWRITE_TAC[bp_e2_cleanse_public_pre;bp_e2_cleanse_pre] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(entry:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_call_post 0x102417d0 (word_sub(stackpointer:int64)(word 48))
   (word 0x2300114c)p n(read memory(entry:x86state))entry returned` THEN
 REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
 SUBGOAL_THEN `read RSP(returned:x86state)=word_sub(stackpointer:int64)(word 40)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`]C3_FIRST_RETURN_STACKPOINTER) THEN
  ASM_REWRITE_TAC[];ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(ISPECL[`RBX:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`RBP:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R12:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R13:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R14:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`R15:(x86state,int64)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`DF:(x86state,bool)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]];
 MP_TAC(ISPECL[`(rflags :> bitelement 18):(x86state,bool)component`;
  `[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(p,n)]:((x86state,num)component)list`;
  `[events]:((x86state,uarch_event list)component)list`;`entry:x86state`;`returned:x86state`]
  R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REWRITE_TAC[ALL] THEN ANTS_TAC THENL
 [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;READ_BITELEMENT]]]);;
print_endline "C3_CLEANSE_RETURN_WORKING_STATE_V1_DEVELOPMENT_CHECKED";;
