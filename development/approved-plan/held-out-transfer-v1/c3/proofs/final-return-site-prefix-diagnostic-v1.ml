(* Private local-tail prefix diagnosis; no global proofgoal mutation. *)
let _,c3fr_prefix_goals,_ = C3_FINAL_RETURN_SITE_PREFIX_TAC ([],c3_final_return_site_statement);;
print_endline "C3_FINAL_RETURN_PREFIX_GOALS";;
List.iter print_goal c3fr_prefix_goals;;
let _,c3fr_two_step_goals,_ =
 (C3_FINAL_RETURN_STEP_TAC `12` `entry:x86state` `fr1:x86state` "fr1" THEN
  C3_FINAL_RETURN_STEP_TAC `11` `fr1:x86state` `fr2:x86state` "fr2")
 (List.hd c3fr_prefix_goals);;
print_endline "C3_FINAL_RETURN_TWO_STEP_GOALS";;
List.iter print_goal c3fr_two_step_goals;;
print_endline "C3_FINAL_RETURN_PREFIX_DIAGNOSTIC_COMPLETE";;
