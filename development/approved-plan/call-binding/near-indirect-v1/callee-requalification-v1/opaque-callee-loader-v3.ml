(* First public proof import in a fresh candidate5 namespace. All proof objects
   are reconstructed and audited here; no saved PASS record is imported.
   Client workers use public definitions and exported theorem names only. *)
needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/prelude-v1.ml";;
component_guard(fun()->needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/components-v2.ml");;
component_guard(fun()->cleanse_aggregate_audit e3_callee_initial_axioms "/output/cleanse-");;
component_guard(fun()->r1_near_qualification_audit "/output/model-qualification.json");;
component_guard(fun()->r1_execution_qualification_audit "/output/execution-qualification.json");;
component_guard(fun()->needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/audit-v1.ml");;
component_guard(fun()->e3_callee_audit e3_callee_initial_axioms "/output/e3-interface.json");;
component_guard(fun()->if axioms()<>e3_callee_initial_axioms then failwith "E3 final axiom list mismatch");;
print_endline "E3_OPAQUE_CALLEE_INTERFACE_LOADED_AND_LIVE_AUDITED";;
