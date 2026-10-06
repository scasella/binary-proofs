use_file_raise_failure := true;;
let cleanse_functional_initial_axioms = axioms();;
let cleanse_functional_guard f = try f() with e -> prerr_endline(Printexc.to_string e); exit 1;;
cleanse_functional_guard(fun () -> loadt "/work/development/approved-plan/cleanse/functional/components-v1.ml");;
cleanse_functional_guard(fun () -> loadt "/work/development/approved-plan/cleanse/functional/audit-v1.ml");;
cleanse_functional_guard(fun () -> cleanse_functional_audit cleanse_functional_initial_axioms "/output/functional-audit.json");;
cleanse_functional_guard(fun () -> print_endline "CLEANSE_FRESH_FUNCTIONAL_ACCEPTED"; exit 0);;
