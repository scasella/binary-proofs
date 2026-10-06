(* Runtime audit of actual bound whole-caller and E5 objects. *)
List.iter (fun (name,th,literal) ->
 if hyp th<>[] || frees(concl th)<>[] || not(aconv(concl th)literal) then
  failwith ("C3 final literal/closure mismatch: " ^ name);
 print_endline ("C3_SUCCESSOR_FINAL_EXACT_CLOSED_TARGET " ^ name);
 print_thm th)
 [("C3_CHECKED",C3_CHECKED,c3_checked_statement);
  ("C3_COUNT",C3_COUNT,c3_count_statement);
  ("C3_INTERFACE",C3_INTERFACE,c3_interface_statement);
  ("C3_NORMAL_CHECKED",C3_NORMAL_CHECKED,c3_normal_checked_statement);
  ("C3_RF_NORMAL_CHECKED",C3_RF_NORMAL_CHECKED,c3_rf_normal_checked_statement);
  ("C3_NORMAL_INTERFACE",C3_NORMAL_INTERFACE,c3_normal_interface_statement)];;
if axioms()=reuse_c3_foundation_axioms then
 print_endline "C3_SUCCESSOR_FINAL_CALLER_LIFTS_FOUNDATION_UNCHANGED"
else failwith "C3 successor final caller/E5 foundation changed";;
print_endline "C3_SUCCESSOR_FINAL_CALLER_LIFTS_LIVE_AUDIT_COMPLETE_NOT_FRESH_ACCEPTANCE";;
