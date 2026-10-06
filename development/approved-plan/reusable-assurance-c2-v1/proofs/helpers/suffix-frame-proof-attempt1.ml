(* Exact suffix frame projection through the unchanged four-frame theorem.
   This caller adapter discharges named O5 endpoint preservation obligations. *)
let C2_SUFFIX_FRAME_PRESERVED = prove
 (c2_suffix_frame_preserved_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC(ISPECL
    [c;`[RIP;RSP;RAX;RBX;RBP;R12]:((x86state,int64)component)list`;
     `[]:((x86state,bool)component)list`;
     `[]:((x86state,num)component)list`;
     `[events]:((x86state,uarch_event list)component)list`;
     `returned:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
