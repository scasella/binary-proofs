(* First12 fixed actual transitions through actualRET; private goals only. *)
let _,c3fr_actual_prefix_goals,_ = C3_FINAL_RETURN_SITE_PREFIX_TAC([],c3_final_return_site_statement);;
let _,c3fr_actual_equal_endpoint,_ = C3_FINAL_RETURN_EQUAL_STEPS_TAC(List.hd c3fr_actual_prefix_goals);;
print_endline "C3_FINAL_RETURN_FIRST_ACTUAL_12_RET_ENDPOINT";;
List.iter print_goal c3fr_actual_equal_endpoint;;
print_endline "C3_FINAL_RETURN_ACTUAL_12_DIAGNOSTIC_COMPLETE";;
