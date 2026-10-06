(* Header-only frame adapter. Original four-frame rule; no code addresses or callee proofs. *)
let C2_HEADER_FRAME_PRESERVED = prove
 (c2_header_frame_preserved_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC(ISPECL
    [c;`[RIP;R12]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[]:((x86state,num)component)list`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
