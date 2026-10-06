(* Composes the checked all-count access theorem and generic qualified-run
   bridge directly. Neither is an assumed entry hypothesis. *)
needs "/work/development/approved-plan/cleanse/interface/helper-proof-attempt3.ml";;
needs "/work/development/approved-plan/cleanse/interface/witness-proof-attempt1.ml";;
let BP_E2_CLEANSE_POLICY_FRAME = prove
 (bp_e2_cleanse_policy_frame_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bp_e2_cleanse_pre]) THEN
  SUBGOAL_THEN `val(stackpointer:int64)+8<=2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_IMP_LE];ALL_TAC] THEN
  SUBGOAL_THEN `read(bytes64 stackpointer) (m:int64->byte)=ra` ASSUME_TAC THENL
   [UNDISCH_TAC `read(memory :> bytes64 stackpointer) s=ra` THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`]
    BP_E2_CLEANSE_BOUNDED_FUNCTIONAL_RETURN) THEN
  REWRITE_TAC[ensures_n] THEN DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLEANSE_INTERFACE_RUN_MONO THEN
  EXISTS_TAC
   `\t:x86state. cleanse_access_return_post pc stackpointer ra t /\
    ((read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
      (!i. i<n ==> read memory t (word_add p (word i))=word 0) /\
      (!a. ~assurance_region p n (val a) ==> read memory t a=m a)) /\
     (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[cleanse_access_return_post;bp_e2_cleanse_call_post] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`n:num`;`m:int64->byte`;`t:x86state`]
      CLEANSE_INTERFACE_SLOT_PRESERVED) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLEANSE_INTERFACE_RUN_POST THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [ETA_AX] THEN
      MATCH_MP_TAC(ISPECL [`cleanse_functional_steps (p:int64) n`;`pc:num`;
        `bp_e2_cleanse_allowed_read rp ordinary stackpointer`;
        `bp_e2_cleanse_allowed_write wp ordinary p n`;
        `bp_e2_cleanse_allowed_fetch xp ordinary pc`;
        `cleanse_access_return_post pc stackpointer ra`;`s:x86state`]
        CLEANSE_ACCESS_CHECKED_RUN_QUALIFIED) THEN
      MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`ra:int64`;`p:int64`;`n:num`;
        `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
        `ordinary:num->bool`;`s:x86state`] CLEANSE_ACCESS_ALL_LENGTH) THEN
      ASM_REWRITE_TAC[CLEANSE_INTERFACE_COUNT_EQUAL];
      ASM_REWRITE_TAC[]]]);;
print_endline "CLEANSE_INTERFACE_POLICY_ATTEMPT1_COMPLETE";;
