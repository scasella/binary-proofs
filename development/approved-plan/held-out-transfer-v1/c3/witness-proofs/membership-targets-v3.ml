(* Exact frozen C3 admissible-entry targets. No caller execution theorem. *)
let C3W_PRE = prove
 (c3w_pre_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:int64`;`q:int64`;`n:num`] C3W_LAYOUT_SPANS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:int64`;`q:int64`;`n:num`] C3W_LAYOUT_PROTECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[c3_pre; c3_got] THEN
  ASM_SIMP_TAC[C3W_STATE_PROJECTIONS; READ_COMPONENT_COMPOSE;
               C3W_MEMORY_WORDS; C3W_INITIAL_ABI; C3W_MEMORY_IMAGES;
               C3W_LOADED_CODE; C3W_IMAGE_PERMISSIONS] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; assurance_canonical48;
              WORD_EQ; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV C3W_FIXED_SPANS] THEN
  UNDISCH_TAC `c3w_layout p q n` THEN REWRITE_TAC[c3w_layout] THEN
  DISCH_THEN(ACCEPT_TAC o CONV_RULE NUM_REDUCE_CONV o CONJUNCT1));;

let C3W_GENERIC_WITNESS = prove
 (c3w_generic_witness_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lib_file:num->byte`;`client_file:num->byte`;`payload:int64->byte`;
               `p:int64`;`q:int64`;`n:num`] C3W_BUFFER_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[c3_entry_witness] THEN
  MAP_EVERY EXISTS_TAC
    [`c3w_memory lib_file client_file payload`;
     `c3w_memory lib_file client_file payload`;
     `c3w_memory lib_file client_file payload`;
     `c3w_memory lib_file client_file payload`;
     `c3w_memory lib_file client_file payload`;
     `c3w_read`; `c3w_write`; `c3w_execute`; `c3w_ordinary`;
     `c3w_state lib_file client_file payload p q n`; `fb_initial_abi`] THEN
  ASM_SIMP_TAC[C3W_PRE; c3w_read]);;

let C3_ADMISSIBLE_ENTRY_WITNESSES = prove
 (c3_admissible_entry_witnesses_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[C3W_GENERIC_WITNESS; C3W_EIGHT_LAYOUTS]);;

print_endline "C3W_FROZEN_MEMBERSHIP_TARGETS_V3_COMPLETE";;
