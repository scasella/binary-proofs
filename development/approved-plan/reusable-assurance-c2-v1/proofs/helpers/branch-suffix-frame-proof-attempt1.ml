(* Public frame algebra; unchanged generic four-frame rule and existing named C2 frame inclusions. *)
let C2_HEADER_FRAME_AC = prove
 (c2_header_frame_ac_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
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
let C2_HEADER_FRAME_BEFORE_CLEANUP_INCLUDED = prove
 (c2_header_frame_before_cleanup_included_statement,
  GEN_TAC THEN REWRITE_TAC[c2_before_cleanup_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_HEADER_BEFORE_CLEANUP_COMPOSE = prove
 (c2_header_before_cleanup_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (returned:x86state) next`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C2_HEADER_FRAME_BEFORE_CLEANUP_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
    [GSYM(SPEC `stackpointer:int64` C2_BEFORE_CLEANUP_FRAME_IDEMPOTENT)] THEN
  REWRITE_TAC[seq] THEN EXISTS_TAC `returned:x86state` THEN ASM_REWRITE_TAC[]);;
let C2_SUFFIX_FRAME_ACCUMULATED_INCLUDED = prove
 (c2_suffix_frame_accumulated_included_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_accumulated_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_ACCUMULATED_SUFFIX_COMPOSE = prove
 (c2_accumulated_suffix_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_accumulated_frame stackpointer p q n m (returned:x86state) next`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
     C2_SUFFIX_FRAME_ACCUMULATED_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
    [GSYM(SPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
      C2_ACCUMULATED_FRAME_IDEMPOTENT)] THEN
  REWRITE_TAC[seq] THEN EXISTS_TAC `returned:x86state` THEN ASM_REWRITE_TAC[]);;
let C2_BEFORE_SUFFIX_ACCUMULATED_COMPOSE = prove
 (c2_before_suffix_accumulated_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
   `m:int64->byte`;`initial:x86state`;`returned:x86state`;`next:x86state`]
    C2_ACCUMULATED_SUFFIX_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]
   C2_BEFORE_CLEANUP_ACCUMULATED_INCLUDED) THEN
  REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
