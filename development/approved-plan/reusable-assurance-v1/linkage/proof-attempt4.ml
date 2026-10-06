let BP_LINKAGE_PRINT4 label (asl,w as goal) =
 print_endline label; print_goal goal; ALL_TAC goal;;
(* Preserve attempt1. Minimal repair: split the original progress/all-successor
   conjunction before simplification can discharge its progress conjunct. *)
let BP_REUSE_RIPREL_JUMP_SUCCESSOR = prove
 (bp_reuse_riprel_jump_successor_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x86 s =
    (RIP := target ,, events := APPEND
      [EventJump(word_add pc (word 6),target);
       EventLoad(word_add (word_add pc (word 6)) disp,8)] e) s`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`6`;`JUMP Unconditional (Memop Quadword (Riprel disp))`;
      `s:x86state`] BP_REUSE_DECODED_STEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SEQ; GSYM JMP; R1_NEAR_JMP_MEMORY;
                LET_DEF; LET_END_DEF; bsid_semantics] THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD; WORD_VAL; APPEND; SEQ; assign; FUN_EQ_THM] THEN
    REWRITE_TAC
     [CONJUNCT1(REWRITE_RULE[orthogonal_components]
       (ORTHOGONAL_COMPONENTS_CONV `orthogonal_components RIP events`))] THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
    REWRITE_TAC[] THEN
    BP_LINKAGE_PRINT4 "LINKAGE_REPAIR3_UNSOLVED_RELATION_EQUALITY" THEN
    FAIL_TAC "LINKAGE_REPAIR3_UNSOLVED_RELATION_EQUALITY";
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[SEQ; assign] THEN MESON_TAC[];
    X_GEN_TAC `next:x86state` THEN
    ASM_REWRITE_TAC[SEQ; assign] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[];
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[];
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[];
      REWRITE_TAC[MAYCHANGE; SEQ_ID; ASSIGNS; assign; seq] THEN
      MESON_TAC[]]]);;

let BP_REUSE_RIPREL_JUMP_CHECKED_HOP = prove
 (bp_reuse_riprel_jump_checked_hop_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`pc:int64`;`disp:int64`;`target:int64`;
                 `e:uarch_event list`;`m:int64->byte`;`s:x86state`]
                BP_REUSE_RIPREL_JUMP_SUCCESSOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`; assurance_checked_run] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  X_GEN_TAC `hopnext:x86state` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `read RIP hopnext=target /\ read memory hopnext=m /\
    read events hopnext=APPEND
      [EventJump(word_add pc (word 6),target);
       EventLoad(word_add (word_add pc (word 6)) disp,8)] e /\
    (MAYCHANGE [RIP] ,, MAYCHANGE [events]) s hopnext`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_step_policy] THEN
  MAP_EVERY EXISTS_TAC
   [`6`;`JUMP Unconditional (Memop Quadword (Riprel disp))`;
    `[EventJump(word_add pc (word 6),target);
      EventLoad(word_add (word_add pc (word 6)) disp,8)]`] THEN
  ASM_REWRITE_TAC[ALL; assurance_event_policy]);;

let BP_REUSE_RIPREL_JUMP_OMITTED = prove
 (bp_reuse_riprel_jump_omitted_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abi_all_decodes_caller_scalar s` ASSUME_TAC THENL
   [MATCH_MP_TAC ABI_CALLER_DECODED_SCALAR_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`6`;`JUMP Unconditional (Memop Quadword (Riprel disp))`] THEN
    ASM_REWRITE_TAC[abi_caller_scalar_instruction] THEN MESON_TAC[];
    ASM_MESON_TAC[ABI_CALLER_STEP_PRESERVES_OMITTED]]);;
