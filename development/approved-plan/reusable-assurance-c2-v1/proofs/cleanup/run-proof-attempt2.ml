(* Public supplier policy only; no supplier instruction execution rule. *)
let C2_CLEANSE_SEGMENT_APPLICATION = prove
 (c2_cleanse_segment_application_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_cleanse_ready] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`a:abi_omitted_state`;`entry:x86state`] C2_CLEANSE_INTERFACE_APPLICATION) THEN ASM_REWRITE_TAC[]);;
let C2_CLEANSE_COMPLETED_RUN = prove
 (c2_cleanse_completed_run_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`cleanse_functional_steps p n`;
    `bp_e2_cleanse_call_post 0x102417d0 (word_sub (stackpointer:int64) (word 32))
      (word 0x22001153) p n (read memory (entry:x86state)) entry`;
    `c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a:
      x86state->bool`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:
      num->x86state->x86state->bool`;`entry:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN
    REWRITE_TAC[c2_cleanse_completed] THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`] C2_CLEANSE_SEGMENT_APPLICATION) THEN ASM_REWRITE_TAC[]]);;
