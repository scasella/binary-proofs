(* Fail closed: every expected theorem must be a live kernel object. No
   placeholder export or source-string success marker can satisfy this audit. *)
needs "/work/development/approved-plan/cleanse/interface/expected-definition-terms-v1.ml";;
let cleanse_interface_json s="\"" ^ String.escaped s ^ "\"";;
let cleanse_interface_audit initial_axioms path =
 let claims=[
  ("CLEANSE_INTERFACE_COUNT_EQUAL",cleanse_interface_count_equal_statement,CLEANSE_INTERFACE_COUNT_EQUAL);
  ("CLEANSE_INTERFACE_RUN_POST",cleanse_interface_run_post_statement,CLEANSE_INTERFACE_RUN_POST);
  ("CLEANSE_INTERFACE_RUN_MONO",cleanse_interface_run_mono_statement,CLEANSE_INTERFACE_RUN_MONO);
  ("CLEANSE_INTERFACE_SLOT_PRESERVED",cleanse_interface_slot_preserved_statement,CLEANSE_INTERFACE_SLOT_PRESERVED);
  ("BP_E2_CLEANSE_POLICY_FRAME",bp_e2_cleanse_policy_frame_statement,BP_E2_CLEANSE_POLICY_FRAME);
  ("BP_E2_CLEANSE_EXTENDED",bp_e2_cleanse_extended_statement,BP_E2_CLEANSE_EXTENDED);
  ("BP_E2_CLEANSE_PUBLIC_POLICY",bp_e2_cleanse_public_policy_statement,BP_E2_CLEANSE_PUBLIC_POLICY);
  ("BP_E2_CLEANSE_PUBLIC_INTERFACE",bp_e2_cleanse_public_interface_statement,BP_E2_CLEANSE_PUBLIC_INTERFACE);
  ("BP_E2_CLEANSE_PUBLIC_WITNESS_BRIDGE",bp_e2_cleanse_public_witness_bridge_statement,BP_E2_CLEANSE_PUBLIC_WITNESS_BRIDGE)] in
 let check name expected th =
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": wrong exact conclusion");
  if axioms()<>initial_axioms then failwith(name^": changed foundation axiom list") in
 let records=List.map(fun(name,expected,th)->
  check name expected th;
  "{\"name\":"^cleanse_interface_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0,"^
  "\"statement\":"^cleanse_interface_json(string_of_term(concl th))^"}") claims in
 let definitions=List.map(fun(name,expected,th)->
  check name expected th;
  "{\"name\":"^cleanse_interface_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,"^
  "\"statement\":"^cleanse_interface_json(string_of_term(concl th))^"}")
  cleanse_interface_expected_definitions_v1 in
 let oc=open_out path in
 output_string oc
  ("{\"status\":\"PASS_CLEANSE_CALLABLE_PUBLIC_INTERFACE_COMPONENT\","^
   "\"full_O1_pass\":false,\"full_O2_pass\":false,"^
   "\"scope\":\"Unchanged E2 Pre, initial full-image binding only, all original successors, strict data/fetch policy, actual final RET, exact finite termination, functional/modeled frame and V5 all-fourteen added-state equality; complete routine acceptance/witness acquisition separate\","^
   "\"theorems\":["^String.concat "," records^
   "],\"expanded_definitions\":["^String.concat "," definitions^"]}\n");
 close_out oc;
 print_endline "CLEANSE_INTERFACE_LIVE_EXACT_AUDIT_PASS:9/39";;
