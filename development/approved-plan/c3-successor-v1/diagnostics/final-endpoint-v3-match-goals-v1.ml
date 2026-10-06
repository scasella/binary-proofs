(* Isolate exact checked cancellation match, then exact monotone input. *)
let _,c3_successor_final_endpoint_v3_cancel_goals,_ =
 (MATCH_MP_TAC C3_FINAL_RETURN_CANCEL_SAVED4 THEN REPEAT CONJ_TAC)
 (List.hd c3_successor_final_endpoint_v3_residuals);;
print_endline "C3_SUCCESSOR_FINAL_ENDPOINT_V3_CANCEL_MATCH_GOALS";;
List.iter print_goal c3_successor_final_endpoint_v3_cancel_goals;;
let _,c3_successor_final_endpoint_v3_maychange_input,_ =
 (REWRITE_TAC[c3_frame])(List.hd c3_successor_final_endpoint_v3_cancel_goals);;
print_endline "C3_SUCCESSOR_FINAL_ENDPOINT_V3_MONOTONE_INPUT";;
List.iter print_goal c3_successor_final_endpoint_v3_maychange_input;;
let _,c3_successor_final_endpoint_v3_monotone_goals,_ =
 MONOTONE_MAYCHANGE_TAC (List.hd c3_successor_final_endpoint_v3_maychange_input);;
print_endline "C3_SUCCESSOR_FINAL_ENDPOINT_V3_MONOTONE_RESULT";;
List.iter print_goal c3_successor_final_endpoint_v3_monotone_goals;;
