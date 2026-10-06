(* Exact actual12 endpoint unfolding, before any framehelper. *)
let _,c3fr_unfolded_endpoint_goals,_ =
 (REWRITE_TAC[assurance_checked_run;c3_scalar_post;c3_loaded_code;c3_got;c3_result] THEN
  EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[CONV_RULE NUM_REDUCE_CONV C3_FINAL_RETURN_RSP_VALUE])
 (List.hd c3fr_actual_equal_endpoint);;
print_endline "C3_FINAL_RETURN_UNFOLDED_ENDPOINT";;List.iter print_goal c3fr_unfolded_endpoint_goals;;
print_endline "C3_FINAL_RETURN_UNFOLDED_ENDPOINT_PRIVATE_COMPLETE";;
