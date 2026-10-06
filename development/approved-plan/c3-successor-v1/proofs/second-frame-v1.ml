(* Successor-local second handoff: five actual instructions, fixed frame instances.
   No new HOL definition or generic integration procedure. Source-only until checked. *)
let C3_SECOND_CONCRETE_FRAME_INCLUDED = prove
 (`!stackpointer:int64. (MAYCHANGE[RIP] ,, MAYCHANGE[RDX] ,, MAYCHANGE[RSI] ,, MAYCHANGE[RDI] ,, MAYCHANGE[events] ,, MAYCHANGE[RSP] ,, MAYCHANGE[memory :> bytes64(word_sub(word_sub(stackpointer:int64)(word 40))(word 8))]) subsumed (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events])`,
 GEN_TAC THEN REWRITE_TAC[HT_WORD_SUB_SUB;SOME_FLAGS] THEN CONV_TAC NUM_REDUCE_CONV THEN (MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;(MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;(MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;(MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;(MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;(MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC;CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC;SUBSUMED_MAYCHANGE_TAC]])]])]])]])]])]]));;
let C3_SECOND_FRAME_WIDE_INCLUDED = prove
 (`!stackpointer:int64. (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events]) subsumed (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE[events])`,
 GEN_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC);;
let C3_SECOND_FRAME_WIDE_BYTE = prove
 (`!stackpointer addr:int64 s t:x86state. 48<=val stackpointer /\
 ~c3_scratch stackpointer(val addr) /\
 (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(word_sub stackpointer(word 48),48)] ,, MAYCHANGE [events]) s t
 ==> read memory t addr=read memory s addr`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `nonoverlapping(addr:int64,1)(word_sub stackpointer(word 48),48)` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_SCRATCH_BYTE_NONOVERLAPPING THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `read(memory :> bytes8(addr:int64))(t:x86state)=read(memory :> bytes8 addr)(s:x86state)` MP_TAC THENL
 [MATCH_MP_TAC(ISPECL[`memory :> bytes8(addr:int64)`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 REWRITE_TAC[BYTES8_ELEMENT;READ_COMPONENT_COMPOSE;READ_ELEMENT]]);;
let C3_SECOND_FRAME_SAVED = prove
 (`!stackpointer:int64 s t:x86state.
 48<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\ (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events]) s t
 ==> read(memory :> bytes64(word_sub(stackpointer:int64)(word 8)))(t:x86state)=read(memory :> bytes64(word_sub(stackpointer:int64)(word 8)))(s:x86state) /\
 read(memory :> bytes64(word_sub(stackpointer:int64)(word 16)))(t:x86state)=read(memory :> bytes64(word_sub(stackpointer:int64)(word 16)))(s:x86state) /\
 read(memory :> bytes64(word_sub(stackpointer:int64)(word 24)))(t:x86state)=read(memory :> bytes64(word_sub(stackpointer:int64)(word 24)))(s:x86state) /\
 read(memory :> bytes64(word_sub(stackpointer:int64)(word 32)))(t:x86state)=read(memory :> bytes64(word_sub(stackpointer:int64)(word 32)))(s:x86state) /\
 read(memory :> bytes64(stackpointer:int64))(t:x86state)=read(memory :> bytes64(stackpointer:int64))(s:x86state)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
 [MATCH_MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 8))`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 16))`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 24))`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`memory :> bytes64(word_sub(stackpointer:int64)(word 32))`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`memory :> bytes64(stackpointer:int64)`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC]);;
let C3_SECOND_FRAME_OUTSIDE = prove
 (`!stackpointer:int64 s t:x86state. (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events]) s t
 ==> read R13 t=read R13 s /\ read R14 t=read R14 s /\ read R15 t=read R15 s /\ read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
 REPEAT CONJ_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`R14:(x86state,int64)component`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`R15:(x86state,int64)component`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`DF:(x86state,bool)component`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC;
 MATCH_MP_TAC(ISPECL[`(rflags :> bitelement 18):(x86state,bool)component`;
 `[RIP;RSP;RDX;RSI;RDI]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
 ORTHOGONAL_COMPONENTS_TAC THEN NONOVERLAPPING_TAC]);;
let C3_SECOND_TOTAL_FRAME_INCLUDED = prove
 (`!stackpointer p q:int64 n m:int64->byte.
 ((c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) ,,
 (MAYCHANGE[RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(p,n)] ,, MAYCHANGE[events]) ,,
 (MAYCHANGE [RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events])) subsumed (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_frame;SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC);;
print_endline "C3_SUCCESSOR_SECOND_FIXED_FRAMES_CHECKED_NOT_ACCEPTANCE";;
