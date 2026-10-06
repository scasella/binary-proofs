(* Named O3 saved-state/O5 incoming-return adapters using public frames only. *)
let C2_CRYPTO_PUBLIC_SAVED_PRESERVED = prove
 (c2_crypto_public_saved_preserved_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC (ISPECL
    [c;`[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[]:((x86state,num)component)list`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REWRITE_TAC[SOME_FLAGS;ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let C2_PREFIX_FRAME_SLOT = prove
 (c2_prefix_frame_slot_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_prefix_frame] THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`memory :> bytes64(slot:int64)`;
    `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
    `SOME_FLAGS:((x86state,bool)component)list`;
    `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
    `[events]:((x86state,uarch_event list)component)list`;
    `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
  ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
  REWRITE_TAC[SOME_FLAGS;ALL] THEN
  REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC);;
let C2_PREFIX_FRAME_INCOMING_SLOT = prove
 (c2_prefix_frame_incoming_slot_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`stackpointer:int64`;
    `s:x86state`;`t:x86state`] C2_PREFIX_FRAME_SLOT) THEN
  ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC);;
