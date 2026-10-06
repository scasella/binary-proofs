(* Closed local theorem candidate; original pre and actual public cleanse post.
   No theorem claim is made unless prove returns and literal closure checks pass. *)
let C3_SECOND_HANDOFF = prove(c3_second_handoff_complete_statement,
 C3_SECOND_INITIAL_FACTS_TAC THEN C3_SECOND_ACTUAL_FIVE_TAC THEN
 C3_SECOND_ENDPOINT_CORE_TAC THEN C3_SECOND_ENDPOINT_TOTAL_FRAME_TAC THEN
 C3_SECOND_ENDPOINT_PUBLIC_TAC);;
if hyp C3_SECOND_HANDOFF<>[] || frees(concl C3_SECOND_HANDOFF)<>[] ||
 not(aconv(concl C3_SECOND_HANDOFF)c3_second_handoff_complete_statement)
then failwith "C3_SUCCESSOR_SECOND_HANDOFF_LITERAL_CLOSURE";;
print_endline "C3_SUCCESSOR_SECOND_HANDOFF_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
print_thm C3_SECOND_HANDOFF;;
