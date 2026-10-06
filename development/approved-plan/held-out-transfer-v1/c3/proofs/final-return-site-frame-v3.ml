(* FixedC3 frame repair: one intermediate state for saved-prefix sequence; fourexplicit frozenR1Four instances, no new algorithm. *)
let C3_FINAL_RETURN_PRESERVES_R13 = prove
 (`!stackpointer p q:int64 n m u v:x86state.
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12])u v ==> read R13 v=read R13 u`,
 REPEAT GEN_TAC THEN REWRITE_TAC[seq] THEN
 DISCH_THEN(X_CHOOSE_THEN `mid:x86state` STRIP_ASSUME_TAC) THEN
 SUBGOAL_THEN `read R13(mid:x86state)=read R13(u:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(p,n);memory :> bytes(word_sub stackpointer(word 48),48)]`;`[events]:((x86state,uarch_event list)component)list`;
 `u:x86state`;`mid:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REPEAT CONJ_TAC THENL
 [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
  MATCH_ACCEPT_TAC(REWRITE_RULE[c3_frame]
   (ASSUME `c3_frame stackpointer p q n m (u:x86state)(mid:x86state)`))];ALL_TAC] THEN
 SUBGOAL_THEN `read R13(v:x86state)=read R13(mid:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RBX;RBP;R12]:((x86state,int64)component)list`;`mid:x86state`;`v:x86state`]
 MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN CONJ_TAC THENL
  [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
   ASM_REWRITE_TAC[]];ALL_TAC] THEN ASM_REWRITE_TAC[]);;
let C3_FINAL_RETURN_PRESERVES_R12 = prove
 (`!stackpointer p q:int64 n m u v:x86state.
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP])u v ==> read R12 v=read R12 u`,
 REPEAT GEN_TAC THEN REWRITE_TAC[seq] THEN
 DISCH_THEN(X_CHOOSE_THEN `mid:x86state` STRIP_ASSUME_TAC) THEN
 SUBGOAL_THEN `read R12(mid:x86state)=read R12(u:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R12:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(p,n);memory :> bytes(word_sub stackpointer(word 48),48)]`;`[events]:((x86state,uarch_event list)component)list`;
 `u:x86state`;`mid:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REPEAT CONJ_TAC THENL
 [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
  MATCH_ACCEPT_TAC(REWRITE_RULE[c3_frame]
   (ASSUME `c3_frame stackpointer p q n m (u:x86state)(mid:x86state)`))];ALL_TAC] THEN
 SUBGOAL_THEN `read R12(v:x86state)=read R12(mid:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R12:(x86state,int64)component`;
 `[RBX;RBP]:((x86state,int64)component)list`;`mid:x86state`;`v:x86state`]
 MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN CONJ_TAC THENL
  [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
   ASM_REWRITE_TAC[]];ALL_TAC] THEN ASM_REWRITE_TAC[]);;
let C3_FINAL_RETURN_PRESERVES_RBP = prove
 (`!stackpointer p q:int64 n m u v:x86state.
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX])u v ==> read RBP v=read RBP u`,
 REPEAT GEN_TAC THEN REWRITE_TAC[seq] THEN
 DISCH_THEN(X_CHOOSE_THEN `mid:x86state` STRIP_ASSUME_TAC) THEN
 SUBGOAL_THEN `read RBP(mid:x86state)=read RBP(u:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`RBP:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(p,n);memory :> bytes(word_sub stackpointer(word 48),48)]`;`[events]:((x86state,uarch_event list)component)list`;
 `u:x86state`;`mid:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REPEAT CONJ_TAC THENL
 [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
  MATCH_ACCEPT_TAC(REWRITE_RULE[c3_frame]
   (ASSUME `c3_frame stackpointer p q n m (u:x86state)(mid:x86state)`))];ALL_TAC] THEN
 SUBGOAL_THEN `read RBP(v:x86state)=read RBP(mid:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`RBP:(x86state,int64)component`;
 `[RBX]:((x86state,int64)component)list`;`mid:x86state`;`v:x86state`]
 MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN CONJ_TAC THENL
  [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
   ASM_REWRITE_TAC[]];ALL_TAC] THEN ASM_REWRITE_TAC[]);;
let C3_FINAL_RETURN_PRESERVES_RBX = prove
 (`!stackpointer p q:int64 n m u v:x86state.
 (c3_frame stackpointer p q n m)u v ==> read RBX v=read RBX u`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(ISPECL[`RBX:(x86state,int64)component`;
 `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;`SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(p,n);memory :> bytes(word_sub stackpointer(word 48),48)]`;`[events]:((x86state,uarch_event list)component)list`;
 `u:x86state`;`v:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 REPEAT CONJ_TAC THENL
 [REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC;
  MATCH_ACCEPT_TAC(REWRITE_RULE[c3_frame]
   (ASSUME `c3_frame stackpointer p q n m (u:x86state)(v:x86state)`))]);;
let C3_FINAL_RETURN_SAVED4_SPLIT = prove
 (`MAYCHANGE[RBX;RBP;R12;R13] = MAYCHANGE[RBX;RBP;R12] ,, MAYCHANGE[R13]`,
 REWRITE_TAC[MAYCHANGE;SEQ_ID;SEQ_ASSOC]);;
let C3_FINAL_RETURN_SAVED3_SPLIT = prove
 (`MAYCHANGE[RBX;RBP;R12] = MAYCHANGE[RBX;RBP] ,, MAYCHANGE[R12]`,
 REWRITE_TAC[MAYCHANGE;SEQ_ID;SEQ_ASSOC]);;
let C3_FINAL_RETURN_SAVED2_SPLIT = prove
 (`MAYCHANGE[RBX;RBP] = MAYCHANGE[RBX] ,, MAYCHANGE[RBP]`,
 REWRITE_TAC[MAYCHANGE;SEQ_ID;SEQ_ASSOC]);;
let C3_FINAL_RETURN_CANCEL_SAVED4 = prove
 (`!stackpointer p q:int64 n m initial final:x86state.
 (c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])initial final /\
 read RBX final=read RBX initial /\ read RBP final=read RBP initial /\
 read R12 final=read R12 initial /\ read R13 final=read R13 initial
 ==> c3_frame stackpointer p q n m initial final`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12])initial final` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12]`;`initial:x86state`;`final:x86state`] HT_FRAME_CANCEL_COMPONENT) THEN
 REPEAT CONJ_TAC THENL
 [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
  MATCH_ACCEPT_TAC C3_FINAL_RETURN_PRESERVES_R13;
  ASM_REWRITE_TAC[SEQ_ASSOC;GSYM C3_FINAL_RETURN_SAVED4_SPLIT];
  ASM_REWRITE_TAC[]];ALL_TAC] THEN
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP])initial final` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`R12:(x86state,int64)component`;
 `c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP]`;`initial:x86state`;`final:x86state`] HT_FRAME_CANCEL_COMPONENT) THEN
 REPEAT CONJ_TAC THENL
 [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
  MATCH_ACCEPT_TAC C3_FINAL_RETURN_PRESERVES_R12;
  ASM_REWRITE_TAC[SEQ_ASSOC;GSYM C3_FINAL_RETURN_SAVED3_SPLIT];
  ASM_REWRITE_TAC[]];ALL_TAC] THEN
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX])initial final` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`RBP:(x86state,int64)component`;
 `c3_frame stackpointer p q n m ,, MAYCHANGE[RBX]`;`initial:x86state`;`final:x86state`] HT_FRAME_CANCEL_COMPONENT) THEN
 REPEAT CONJ_TAC THENL
 [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
  MATCH_ACCEPT_TAC C3_FINAL_RETURN_PRESERVES_RBP;
  ASM_REWRITE_TAC[SEQ_ASSOC;GSYM C3_FINAL_RETURN_SAVED2_SPLIT];
  ASM_REWRITE_TAC[]];ALL_TAC] THEN
 MATCH_MP_TAC(ISPECL[`RBX:(x86state,int64)component`;
 `c3_frame stackpointer p q n m`;`initial:x86state`;`final:x86state`] HT_FRAME_CANCEL_COMPONENT) THEN
 REPEAT CONJ_TAC THENL
 [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
  MATCH_ACCEPT_TAC C3_FINAL_RETURN_PRESERVES_RBX;
  ASM_REWRITE_TAC[SEQ_ASSOC];
  ASM_REWRITE_TAC[]]);;
print_endline "C3_FINAL_RETURN_SAVED4_CANCEL_CHECKED_NOT_ACCEPTANCE";;
