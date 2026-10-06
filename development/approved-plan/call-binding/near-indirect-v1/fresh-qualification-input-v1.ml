use_file_raise_failure := true;;
let model_initial_axioms = axioms();;
let r1_near_checked_load path =
 try loadt path with e -> prerr_endline(Printexc.to_string e); exit 1;;
r1_near_checked_load "/work/proofs/qualification/qualification.ml";;
r1_near_checked_load "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-statements-v1.ml";;
r1_near_checked_load "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-proof-attempt2.ml";;
r1_near_checked_load "/work/development/approved-plan/call-binding/near-indirect-v1/decoder-qualification-proof-attempt2.ml";;
r1_near_checked_load "/work/development/approved-plan/call-binding/near-indirect-v1/qualification-audit-v2.ml";;
(try r1_near_qualification_audit "/output/qualification-audit.json"
 with e -> prerr_endline(Printexc.to_string e); exit 1);;
exit 0;;
