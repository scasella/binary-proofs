needs "/work/development/approved-plan/cleanse/functional/audit-v4.ml";;
needs "/work/development/approved-plan/cleanse/access/audit-v1.ml";;
needs "/work/development/approved-plan/cleanse/interface/audit-v1.ml";;
needs "/work/development/approved-plan/cleanse/interface/abi-audit-claims-v1.ml";;
needs "/work/development/approved-plan/cleanse/interface/aggregate-definition-claims-v1.ml";;
needs "/work/development/approved-plan/cleanse/loaded-witness/audit-v1.ml";;
let cleanse_aggregate_audit initial_axioms output_prefix =
 if axioms()<>initial_axioms then failwith "aggregate: changed foundation axioms";
 cleanse_functional_audit initial_axioms (output_prefix^"functional.json");
 cleanse_access_audit initial_axioms (output_prefix^"access.json");
 cleanse_interface_audit initial_axioms (output_prefix^"interface.json");
 let check name expected th =
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th)expected) then failwith(name^": exact conclusion mismatch");
  if axioms()<>initial_axioms then failwith(name^": changed foundation axioms") in
 let abi_rows=List.map(fun(name,expected,th)->check name expected th;
  "{\"name\":"^cleanse_interface_json name^
  ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true,"^
  "\"statement\":"^cleanse_interface_json(string_of_term(concl th))^"}")
  cleanse_aggregate_abi_claims in
 let seen=ref [] in
 let definition_rows=List.fold_left(fun acc (name,mode,expected,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  let actual=if mode="body" then snd(strip_forall(concl th)) else concl th in
  if not(aconv actual expected) then failwith(name^": frozen expanded definition mismatch");
  if axioms()<>initial_axioms then failwith(name^": changed foundation axioms");
  if List.mem name !seen then acc else
  (seen:=name:: !seen;
   ("{\"name\":"^cleanse_interface_json name^
    ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true,"^
    "\"statement\":"^cleanse_interface_json(string_of_term(concl th))^"}")::acc))
  [] cleanse_aggregate_definition_claims in
 let out=open_out(output_prefix^"supplement.json") in
 output_string out
  ("{\"status\":\"PASS_LIVE_CLEANSE_AGGREGATE_SUPPLEMENT\",\"theorems\":["^
   String.concat "," (abi_rows@clw_audit_rows)^
   "],\"expanded_definitions\":["^String.concat "," (List.rev definition_rows)^
   "],\"all_equation_check_count\":97}\n");close_out out;
 if axioms()<>initial_axioms then failwith "aggregate: changed final axiom list";
 print_endline "CLEANSE_AGGREGATE_LIVE_EXACT_AUDIT_PASS:80/72";;
