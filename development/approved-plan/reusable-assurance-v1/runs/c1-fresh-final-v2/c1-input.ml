if axioms()<>fresh_initial_axioms then exit 1;;
print_endline("C1_FRESH_SUPPLIER_CPU "^string_of_float(Sys.time()-.fresh_supplier_cpu_start));;
let c1_fresh_cpu_start=Sys.time();;
try needs "/reuse/replay/c1-final-loader-v3.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;
try needs "/reuse/replay/c1-final-v2-audit.ml" with e -> prerr_endline(Printexc.to_string e); exit 1;;
print_endline("C1_FRESH_CALLER_CPU "^string_of_float(Sys.time()-.c1_fresh_cpu_start));;
if axioms()<>fresh_initial_axioms then exit 1;;
print_endline "C1_FRESH_FINAL_STANDARD3_AXIOMS_UNCHANGED";;
exit 0;;
