(* Exact intermediate residual before failed cancellation match. *)
let _,c3_successor_final_endpoint_v3_residuals,_ =
 (REWRITE_TAC[assurance_checked_run;c3_scalar_post;c3_loaded_code;c3_got;c3_result] THEN
  EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[CONV_RULE NUM_REDUCE_CONV C3_FINAL_RETURN_RSP_VALUE])
 (List.hd !c3_final_site_diagnostic_goals);;
print_endline "C3_SUCCESSOR_FINAL_ENDPOINT_V3_EXACT_RESIDUALS";;
List.iter print_goal c3_successor_final_endpoint_v3_residuals;;
print_endline "C3_SUCCESSOR_FINAL_ENDPOINT_V3_RESIDUALS_RETAINED";;
