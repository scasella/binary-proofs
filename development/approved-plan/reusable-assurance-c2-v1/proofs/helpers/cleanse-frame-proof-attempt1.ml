(* O4 opaquecleanupframe preserves result/savedslots; O5 protectactualcode/GOT. No body semantics. *)
let C2_CLEANSE_FRAME_PRESERVED = prove
 (c2_cleanse_frame_preserved_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC (ISPECL
    [c;`[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[memory :> bytes(p:int64,n)]`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REWRITE_TAC[SOME_FLAGS;ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let C2_CLEANSE_FRAME_COMPONENT_TAC c =
 MATCH_MP_TAC (ISPECL
  [c;`[RIP;RSP;RAX;RDI;RSI]:((x86state,int64)component)list`;
   `SOME_FLAGS:((x86state,bool)component)list`;
   `[memory :> bytes(p:int64,n)]`;`[events]:((x86state,uarch_event list)component)list`;
   `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
 REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;;
let C2_CLEANSE_FRAME_SLOT = prove
 (c2_cleanse_frame_slot_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C2_CLEANSE_FRAME_COMPONENT_TAC `memory :> bytes64 (slot:int64)`);;
let C2_CLEANSE_FRAME_CODE = prove
 (c2_cleanse_frame_code_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `read (memory :> bytelist(codebase:int64,LENGTH (mc:byte list))) (t:x86state)=
    read (memory :> bytelist(codebase,LENGTH mc)) (s:x86state)` ASSUME_TAC THENL
   [C2_CLEANSE_FRAME_COMPONENT_TAC `memory :> bytelist(codebase:int64,LENGTH(mc:byte list))`;
    UNDISCH_TAC `bytes_loaded (s:x86state) (codebase:int64) (mc:byte list)` THEN
    REWRITE_TAC[bytes_loaded] THEN ASM_REWRITE_TAC[]]);;
