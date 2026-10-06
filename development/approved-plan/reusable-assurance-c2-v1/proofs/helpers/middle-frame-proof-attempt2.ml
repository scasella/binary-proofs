(* Caller-only public frame algebra, no supplier instruction semantics. *)
let C2_MIDDLE_FRAME_BYTE = prove
 (c2_middle_frame_byte_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_middle_frame] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping(addr:int64,1)(word_sub stackpointer (word 32),32)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C2_SCRATCH_BYTE_NONOVERLAPPING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes8 (addr:int64)) (t:x86state) =
    read (memory :> bytes8 addr) (s:x86state)` MP_TAC THENL
   [MATCH_MP_TAC (ISPECL
      [`memory :> bytes8 (addr:int64)`;
       `[RIP;RSP;RDI;RSI]:((x86state,int64)component)list`;
       `[]:((x86state,bool)component)list`;
       `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
       `[events]:((x86state,uarch_event list)component)list`;
       `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
    REWRITE_TAC[BYTES8_ELEMENT;READ_COMPONENT_COMPOSE;READ_ELEMENT]]);;

let C2_MIDDLE_FRAME_SLOT = prove
 (c2_middle_frame_slot_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_middle_frame] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`memory :> bytes64(slot:int64)`;
    `[RIP;RSP;RDI;RSI]:((x86state,int64)component)list`;
    `[]:((x86state,bool)component)list`;
    `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
    `[events]:((x86state,uarch_event list)component)list`;
    `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
  ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
  REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC);;
let C2_MIDDLE_FRAME_INCOMING_SLOT = prove
 (c2_middle_frame_incoming_slot_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`stackpointer:int64`;
    `s:x86state`;`t:x86state`] C2_MIDDLE_FRAME_SLOT) THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC);;
let C2_MIDDLE_FRAME_SAVED_PRESERVED = prove
 (c2_middle_frame_saved_preserved_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_middle_frame] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC(ISPECL
    [c;`[RIP;RSP;RDI;RSI]:((x86state,int64)component)list`;
     `[]:((x86state,bool)component)list`;
     `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let C2_MIDDLE_BEFORE_CLEANUP_INCLUDED = prove
 (c2_middle_before_cleanup_included_statement,
  GEN_TAC THEN REWRITE_TAC[c2_middle_frame;c2_before_cleanup_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_MIDDLE_BEFORE_CLEANUP_COMPOSE = prove
 (c2_middle_before_cleanup_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (returned:x86state) next`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C2_MIDDLE_BEFORE_CLEANUP_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
    [GSYM(SPEC `stackpointer:int64` C2_BEFORE_CLEANUP_FRAME_IDEMPOTENT)] THEN
  REWRITE_TAC[seq] THEN EXISTS_TAC `returned:x86state` THEN ASM_REWRITE_TAC[]);;
