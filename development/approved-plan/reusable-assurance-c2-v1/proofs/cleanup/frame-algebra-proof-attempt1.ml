(* O4/O5 cleanup-return transport using public endpoint effects/frame only.
   Code arrays below supply public byte-length binding facts, never callee
   execution rules. C2-specific protection/snapshot/stack facts are new. *)
let c2_before_cleanup_untouched_statement =
 `!stackpointer:int64 s t:x86state.
    c2_before_cleanup_frame stackpointer s t
    ==> read R13 t=read R13 s /\ read R14 t=read R14 s /\
        read R15 t=read R15 s /\ read DF t=read DF s`;;
let C2_BEFORE_CLEANUP_UNTOUCHED = prove
 (c2_before_cleanup_untouched_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_before_cleanup_frame] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC(ISPECL
    [c;`[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11;RBX;RBP;R12]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let c2_accumulated_frame_idempotent_statement =
 `!stackpointer p q n m.
    (c2_accumulated_frame stackpointer p q n m ,,
     c2_accumulated_frame stackpointer p q n m)=
    c2_accumulated_frame stackpointer p q n m`;;
let C2_ACCUMULATED_FRAME_IDEMPOTENT = prove
 (c2_accumulated_frame_idempotent_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_accumulated_frame;SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;
let c2_cleanse_frame_accumulated_statement =
 `!stackpointer p q n m. c2_equal m p q n ==>
    (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) subsumed
    c2_accumulated_frame stackpointer p q n m`;;
let C2_CLEANSE_FRAME_ACCUMULATED = prove
 (c2_cleanse_frame_accumulated_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[c2_accumulated_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
