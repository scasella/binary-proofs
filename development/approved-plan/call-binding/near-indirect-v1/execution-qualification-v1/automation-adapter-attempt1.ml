let R1_ABSOLUTE_OPERATION_ETA = prove
 (r1_absolute_operation_eta_statement,
  REWRITE_TAC[FUN_EQ_THM;x86_JMP_ABSOLUTE]);;
let R1_WORD_VAL_ADDRESS = prove
 (r1_word_val_address_statement,
  REWRITE_TAC[WORD_ADD;WORD_VAL]);;
let R1_X86_CONV decode_array ths tm =
 (X86_CONV decode_array ths THENC
  REWRITE_CONV[x86_JMP_ABSOLUTE;SEQ;assign;seq;UNWIND_THM1;BETA_THM] THENC
  TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
  REWRITE_CONV[R1_WORD_VAL_ADDRESS] THENC
  TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) tm;;
let R1_BASIC_STEP_TAC =
 GEN_BASIC_STEP_TAC "R1" `x86` `:x86state` R1_X86_CONV
   (REWRITE_TAC[]);;
let R1_STEP_TAC =
 GEN_STEP_TAC R1_BASIC_STEP_TAC ALL_TAC bytes_loaded_update
  (fun _ _->());;
let R1_STEPS_TAC rule snums =
 MAP_EVERY (fun sname->R1_STEP_TAC rule [] sname None
  (fun th->STRIP_ASSUME_TAC th)) (statenames "s" snums);;
let R1_SIM_TAC rule snums =
 REWRITE_TAC(!simulation_precanon_thms) THEN
 ENSURES_INIT_TAC "s0" THEN R1_STEPS_TAC rule snums THEN
 ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;
