use_file_raise_failure := true;;
if axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then exit 1;;
let fresh_initial_axioms=axioms();;
needs "/work/development/approved-plan/reusable-assurance-c1-successor-v1/replay/ambient-snapshot-v1.ml";;
c1_successor_ambient_snapshot "before-supplier" "/output/ambient-before-supplier-v1.json";;
let fresh_supplier_cpu_start=Sys.time();;
try needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/opaque-callee-loader-v3.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;

try needs "/work/development/approved-plan/held-out-transfer-v1/layer/load-v1.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;
let diagnostic_cpu_start=Sys.time();;
try needs "/c3-input/diagnostic.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;
if axioms()<>fresh_initial_axioms then exit 2;;
print_endline("C3_TYPECHECK_CPU "^string_of_float(Sys.time()-.diagnostic_cpu_start));;
print_endline "C3_TYPECHECK_STANDARD3_UNCHANGED";;
exit 0;;
