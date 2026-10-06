(* Actual42 fixed transitions over four source Boolean cases; private goals only. *)
let _,c3fr_actual_endpoint_goals,_ =
 (C3_FINAL_RETURN_SITE_PREFIX_TAC THENL
  [C3_FINAL_RETURN_EQUAL_STEPS_TAC;
   C3_FINAL_RETURN_EQUAL_STEPS_TAC;
   C3_FINAL_RETURN_MISMATCH_STEPS_TAC;
   C3_FINAL_RETURN_MISMATCH_STEPS_TAC])([],c3_final_return_site_statement);;
print_endline "C3_FINAL_RETURN_FOUR_ACTUAL_PATH_ENDPOINTS";;
List.iter print_goal c3fr_actual_endpoint_goals;;
print_endline "C3_FINAL_RETURN_ACTUAL_PATH_DIAGNOSTIC_COMPLETE";;
