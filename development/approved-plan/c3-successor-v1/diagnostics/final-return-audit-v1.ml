(* Runtime theorem checks. This is a conditional suffix intermediate only. *)
if hyp C3_FINAL_RETURN_CANCEL_SAVED4 = [] then
 print_endline "C3_SUCCESSOR_FINAL_FRAME_HYPOTHESES_EMPTY"
else failwith "C3 successor frame theorem has hypotheses";;
if hyp C3_FINAL_RETURN_SITE = [] &&
 aconv (concl C3_FINAL_RETURN_SITE) c3_final_return_site_statement then
 print_endline "C3_SUCCESSOR_FINAL_SITE_EXACT_CLOSED_CONDITIONAL_STATEMENT"
else failwith "C3 successor final-site conclusion or hypotheses mismatch";;
if axioms() = reuse_c3_foundation_axioms then
 print_endline "C3_SUCCESSOR_FINAL_SUFFIX_FOUNDATION_UNCHANGED"
else failwith "C3 successor suffix foundation changed";;
print_thm C3_FINAL_RETURN_CANCEL_SAVED4;;
print_thm C3_FINAL_RETURN_SITE;;
print_endline "C3_SUCCESSOR_FINAL_SUFFIX_AUDIT_COMPLETE_NOT_WHOLE_CALLER_ACCEPTANCE";;
