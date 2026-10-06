(* Fail-fast cold checker; this component cannot accept O1/O2. *)
use_file_raise_failure := true;;
let cleanse_access_fresh_initial_axioms=axioms();;
let cleanse_access_fresh_guard action =
 try action() with e -> prerr_endline("CLEANSE_ACCESS_FRESH_FAILURE:"^Printexc.to_string e);exit 1;;
cleanse_access_fresh_guard (fun()->needs "x86/proofs/base.ml");;
cleanse_access_fresh_guard (fun()->needs "/work/development/approved-plan/cleanse/access/components-v1.ml");;
cleanse_access_fresh_guard (fun()->needs "/work/development/approved-plan/cleanse/access/audit-v1.ml");;
cleanse_access_fresh_guard (fun()->cleanse_access_audit cleanse_access_fresh_initial_axioms "/output/access-audit.json");;
print_endline "CLEANSE_FRESH_ACCESS_ACCEPTED";;
exit 0;;
