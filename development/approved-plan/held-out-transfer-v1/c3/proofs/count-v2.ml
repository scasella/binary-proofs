(* Frozen literal accounting target; does not imply any execution guarantee. *)
let C3_COUNT = prove(c3_count_statement, REWRITE_TAC[c3_steps;bp_assurance_call_steps]);;
