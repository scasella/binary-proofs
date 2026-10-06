use_file_raise_failure := true;;
if axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then exit 1;;
let fresh_initial_axioms=axioms();;
let fresh_supplier_cpu_start=Sys.time();;
try needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/opaque-callee-loader-v3.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;
