(* Private exact C3W_PRE tactic prefix, omitting the failed broad MESON call. *)
let (_,c3w_pre_private_goals_v1,_) =
 (  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV C3W_FIXED_SPANS]) ([],c3w_pre_statement);;
Printf.printf "C3W_PRE_PREFIX_GOALS=%d\n" (List.length c3w_pre_private_goals_v1);;
List.iter print_goal c3w_pre_private_goals_v1;;
print_endline "C3W_PRE_PRIVATE_DIAGNOSTIC_V1_COMPLETE";;
