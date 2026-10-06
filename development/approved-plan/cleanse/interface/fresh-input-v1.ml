use_file_raise_failure := true;;
let cleanse_aggregate_initial_axioms=axioms();;
let clw_initial_axioms=cleanse_aggregate_initial_axioms;;
let cleanse_aggregate_guard f=try f() with e->prerr_endline(Printexc.to_string e);exit 1;;
cleanse_aggregate_guard(fun()->needs "/work/development/approved-plan/cleanse/interface/aggregate-components-v1.ml");;
cleanse_aggregate_guard(fun()->needs "/work/development/approved-plan/cleanse/interface/aggregate-audit-v1.ml");;
cleanse_aggregate_guard(fun()->cleanse_aggregate_audit cleanse_aggregate_initial_axioms "/output/");;
cleanse_aggregate_guard(fun()->print_endline "CLEANSE_AGGREGATE_FRESH_ACCEPTED";exit 0);;
