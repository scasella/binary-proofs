use_file_raise_failure := true;;
let r1_execution_initial_axioms=axioms();;
loadt "/work/development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/components-v1.ml";;
loadt "/work/development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1/audit-v2.ml";;
r1_execution_qualification_audit "/output/execution-qualification-audit.json";;
print_endline "R1_EXECUTION_FRESH_53_41_COMPLETE";;
exit 0;;
