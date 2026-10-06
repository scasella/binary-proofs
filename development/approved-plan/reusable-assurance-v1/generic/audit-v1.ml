(* These checks run only after fresh kernel reconstruction. *)
let ra_generic_exports = [
 ("RA_CHECKED_RUN_APPEND", RA_CHECKED_RUN_APPEND, ra_checked_run_append_statement);
 ("RA_CHECKED_RUN_POST_MONO", RA_CHECKED_RUN_POST_MONO, ra_checked_run_post_mono_statement);
 ("RA_CHECKED_RUN_POLICY_MONO", RA_CHECKED_RUN_POLICY_MONO, ra_checked_run_policy_mono_statement);
 ("E5_RF_CLEAR_IDENTITY", E5_RF_CLEAR_IDENTITY, e5_rf_clear_identity_statement);
 ("E5_SCALAR_OPERATION_OUTSIDE_FLAGS", E5_SCALAR_OPERATION_OUTSIDE_FLAGS, e5_scalar_operation_outside_flags_statement);
 ("E5_QUALIFIED_STEP_OUTSIDE_FLAGS", E5_QUALIFIED_STEP_OUTSIDE_FLAGS, e5_qualified_step_outside_flags_statement);
 ("E5_QUALIFIED_STEP_NORMAL", E5_QUALIFIED_STEP_NORMAL, e5_qualified_step_normal_statement);
 ("E5_RF_RETIRED_STEP_NORMAL_EQ", E5_RF_RETIRED_STEP_NORMAL_EQ, e5_rf_retired_step_normal_eq_statement);
 ("E5_RF_RETIRED_EXTENDED_NORMAL_EQ", E5_RF_RETIRED_EXTENDED_NORMAL_EQ, e5_rf_retired_extended_normal_eq_statement);
 ("E5_CHECKED_RUN_NORMAL", E5_CHECKED_RUN_NORMAL, e5_checked_run_normal_statement);
 ("E5_RF_CHECKED_RUN_NORMAL", E5_RF_CHECKED_RUN_NORMAL, e5_rf_checked_run_normal_statement);
 ("E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT", E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT, e5_normal_checked_run_extended_lift_statement);
 ("RA_CHECKED_RUN_THREE_SEGMENT", RA_CHECKED_RUN_THREE_SEGMENT, ra_checked_run_three_segment_statement)
];;
if length ra_generic_exports <> 13 then failwith "RA_GENERIC_EXPORT_COUNT";;
List.iter (fun (name,th,expected) ->
 if hyp th <> [] || frees(concl th) <> [] || not(aconv (concl th) expected)
 then failwith ("RA_GENERIC_LITERAL_AUDIT:" ^ name);
 print_endline ("RA_GENERIC_RAW_CLOSED_LITERAL:" ^ name)) ra_generic_exports;;
if axioms() <> ra_generic_initial_axioms || axioms() <> [INFINITY_AX;SELECT_AX;ETA_AX]
then failwith "RA_GENERIC_AXIOMS_CHANGED";;
print_endline "RA_GENERIC_13_LITERAL_EXPORTS_STANDARD3_AUDIT_COMPLETE";;
