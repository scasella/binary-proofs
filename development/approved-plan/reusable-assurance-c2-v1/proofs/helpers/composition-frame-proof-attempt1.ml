let C2_PREFIX_OUTSIDE_SAVED_PRESERVED = prove
 (c2_prefix_outside_saved_preserved_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_prefix_frame] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC(ISPECL
    [c;`[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let C2_BEFORE_CLEANUP_FRAME_IDEMPOTENT = prove
 (c2_before_cleanup_frame_idempotent_statement,
  GEN_TAC THEN REWRITE_TAC[c2_before_cleanup_frame;SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;
let C2_PREFIX_BEFORE_CLEANUP_INCLUDED = prove
 (c2_prefix_before_cleanup_included_statement,
  GEN_TAC THEN REWRITE_TAC[c2_prefix_frame;c2_before_cleanup_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_CRYPTO_BEFORE_CLEANUP_INCLUDED = prove
 (c2_crypto_before_cleanup_included_statement,
  GEN_TAC THEN REWRITE_TAC[c2_crypto_public_frame;c2_before_cleanup_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_BEFORE_CLEANUP_FRAME_COMPOSE = prove
 (c2_before_cleanup_frame_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (initial:x86state) entry`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C2_PREFIX_BEFORE_CLEANUP_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (entry:x86state) returned`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C2_CRYPTO_BEFORE_CLEANUP_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
    [GSYM(SPEC `stackpointer:int64` C2_BEFORE_CLEANUP_FRAME_IDEMPOTENT)] THEN
  REWRITE_TAC[seq] THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[]);;
let C2_BEFORE_CLEANUP_ACCUMULATED_INCLUDED = prove
 (c2_before_cleanup_accumulated_included_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_before_cleanup_frame;c2_accumulated_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C2_FRAME_CANCEL_COMPONENT = prove
 (c2_frame_cancel_component_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(R ,, MAYCHANGE [c:(A,B)component]) (s:A) t` THEN
  REWRITE_TAC[MAYCHANGE_SING;seq;ASSIGNS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:B` ASSUME_TAC))) THEN
  SUBGOAL_THEN `read (c:(A,B)component) (u:A)=read c s` ASSUME_TAC THENL
   [ASM_MESON_TAC[];ALL_TAC] THEN
  let valid=REWRITE_RULE[EXTENSIONALLY_VALID_COMPONENT]
    (ASSUME `extensionally_valid_component (c:(A,B)component)`) in
  let overwrite_read=CONJUNCT1(CONJUNCT2 valid)
  and overwrite_write=CONJUNCT2(CONJUNCT2 valid) in
  SUBGOAL_THEN `write (c:(A,B)component) (read c (t:A)) t=t` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_read;ALL_TAC] THEN
  SUBGOAL_THEN `write (c:(A,B)component) (read c (t:A)) (write c (y:B) (u:A))=
    write c (read c t) u` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_write;ALL_TAC] THEN
  SUBGOAL_THEN `write (c:(A,B)component) (read c (u:A)) u=u` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC overwrite_read;ALL_TAC] THEN
  SUBGOAL_THEN `(t:A)=u` ASSUME_TAC THENL
   [ASM_MESON_TAC[];ASM_MESON_TAC[]]);;
(* Pure foundation frame algebra. *)
let C2_RESTORED_FRAME_TAIL =
 let saved=[`RBX:(x86state,int64)component`;`RBP:(x86state,int64)component`;`R12:(x86state,int64)component`] in
 let bubble c tm =
  let a,b=dest_binary ",," tm in
  let selected=mk_comb(`ASSIGNS:(x86state,int64)component->x86state->x86state->bool`,c) in
  if a<>selected then failwith "not selected frame assignment";
  let next=if is_binary ",," b then fst(dest_binary ",," b) else b in
  let _,args=strip_comb next in
  if length args<>1 || mem (hd args) saved then failwith "stop at saved register tail";
  if is_binary ",," b then
   (REWR_CONV SEQ_ASSOC THENC LAND_CONV ASSIGNS_SWAP_CONV THENC
    REWR_CONV(GSYM SEQ_ASSOC)) tm
  else ASSIGNS_SWAP_CONV tm in
 prove(c2_restored_frame_tail_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_accumulated_frame;c2_frame;SOME_FLAGS] THEN
  CONV_TAC(BINOP_CONV MAYCHANGE_CANON_CONV) THEN
  MAP_EVERY (fun c -> CONV_TAC(LAND_CONV(TOP_DEPTH_CONV(bubble c)))) (rev saved) THEN
  REFL_TAC);;
let C2_MAIN_FRAME_SAVED_PRESERVED = prove
 (c2_main_frame_saved_preserved_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_frame] THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  (fun gl ->
   let c=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC (ISPECL [c;
    `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
    `SOME_FLAGS:((x86state,bool)component)list`;
    `[memory :> bytes(p,if c2_equal m p q n then n else 0);memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]:((x86state,num)component)list`;
    `[events]:((x86state,uarch_event list)component)list`;
    `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[c2_frame;ALL] THEN
    REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC) gl));;
let C2_RESTORED_FRAME_NARROW = prove
 (c2_restored_frame_narrow_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v:x86state. c2_frame stackpointer p q n m u v
    ==> read RBX v=read RBX u /\ read RBP v=read RBP u /\ read R12 v=read R12 u`
   ASSUME_TAC THENL [MESON_TAC[C2_MAIN_FRAME_SAVED_PRESERVED];ALL_TAC] THEN
  UNDISCH_TAC `c2_accumulated_frame stackpointer p q n m (s:x86state) t` THEN
  REWRITE_TAC[C2_RESTORED_FRAME_TAIL] THEN DISCH_TAC THEN
  MAP_EVERY (fun c ->
   let rest=if c=`R12:(x86state,int64)component` then
     `((c2_frame stackpointer p q n m ,, MAYCHANGE [RBX]) ,, MAYCHANGE [RBP]):x86state->x86state->bool`
    else if c=`RBP:(x86state,int64)component` then
     `(c2_frame stackpointer p q n m ,, MAYCHANGE [RBX]):x86state->x86state->bool`
    else `c2_frame stackpointer p q n m:x86state->x86state->bool` in
   SUBGOAL_THEN (list_mk_comb(rest,[`s:x86state`;`t:x86state`])) ASSUME_TAC THENL
    [MATCH_MP_TAC (ISPECL [c;rest;`s:x86state`;`t:x86state`] C2_FRAME_CANCEL_COMPONENT) THEN
     REPEAT CONJ_TAC THENL
      [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV;
       REPEAT GEN_TAC THEN
       REWRITE_TAC[seq] THEN REPEAT STRIP_TAC THEN
       (let ths=map (fun d ->
         let orth=ORTHOGONAL_COMPONENTS_RULE2 c d in
         REWRITE_RULE[ALL;orth] (ISPECL [c;mk_list([d],type_of d)]
          MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT))
         (if c=`R12:(x86state,int64)component` then [`RBX:(x86state,int64)component`;`RBP:(x86state,int64)component`]
          else if c=`RBP:(x86state,int64)component` then [`RBX:(x86state,int64)component`] else []) in
        ASM_MESON_TAC ths);
       ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]];ALL_TAC])
   [`R12:(x86state,int64)component`;`RBP:(x86state,int64)component`;`RBX:(x86state,int64)component`] THEN
  ASM_REWRITE_TAC[]);;
