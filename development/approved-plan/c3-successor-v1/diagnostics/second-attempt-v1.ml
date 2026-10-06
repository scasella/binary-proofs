(* Development diagnostic only. Does not export a handoff theorem. *)
g c3_second_handoff_complete_statement;;
e C3_SECOND_INITIAL_FACTS_TAC;;
print_endline "C3_SUCCESSOR_SECOND_INITIAL_FACTS_RETURN";;
e C3_SECOND_ACTUAL_FIVE_TAC;;
print_endline "C3_SUCCESSOR_SECOND_ACTUAL_FIVE_RETURN";;
e C3_SECOND_ENDPOINT_CORE_TAC;;
print_endline "C3_SUCCESSOR_SECOND_ENDPOINT_CORE_RETURN";;
e C3_SECOND_ENDPOINT_TOTAL_FRAME_TAC;;
print_endline "C3_SUCCESSOR_SECOND_ENDPOINT_TOTAL_FRAME_RETURN";;
e C3_SECOND_ENDPOINT_PUBLIC_TAC;;
print_endline "C3_SUCCESSOR_SECOND_ENDPOINT_PUBLIC_RETURN";;
print_term(snd(top_goal()));;
print_newline();;
