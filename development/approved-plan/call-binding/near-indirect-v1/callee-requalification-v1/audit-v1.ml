needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/statement-claims-v1.ml";;
needs "/work/development/approved-plan/call-binding/near-indirect-v1/callee-requalification-v1/definition-claims-v1.ml";;
let e3_callee_json s = "\"" ^ String.escaped s ^ "\"";;
let e3_callee_audit initial_axioms path =
 if axioms()<>initial_axioms then failwith "E3 callee: changed foundation axioms";
 let rows=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th)expected) then failwith(name^": frozen exact conclusion mismatch");
  if axioms()<>initial_axioms then failwith(name^": changed foundation axioms");
  "{\"name\":"^e3_callee_json name^
  ",\"statement\":"^e3_callee_json(string_of_term(concl th))^
  ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true}")
  e3_callee_new_claims in
 let seen=ref [] in
 let definitions=List.fold_left(fun acc(name,mode,expected,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  let actual=if mode="body" then snd(strip_forall(concl th)) else concl th in
  let expected=if mode="body" then snd(strip_forall expected) else expected in
  if not(aconv actual expected) then failwith(name^": frozen expanded model/ABI definition mismatch");
  if axioms()<>initial_axioms then failwith(name^": changed foundation axioms");
  if List.mem name !seen then acc else
  (seen:=name:: !seen;
   ("{\"name\":"^e3_callee_json name^
    ",\"statement\":"^e3_callee_json(string_of_term(concl th))^
    ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true}")::acc))
  [] e3_callee_definition_claims in
 if List.length rows<>7 || List.length definitions<>119 ||
    List.length e3_callee_definition_claims<>218 then failwith "E3 callee: incomplete registry";
 let oc=open_out path in
 output_string oc ("{\"status\":\"PASS_LIVE_E3_CALLEE_INTERFACES\",\"theorems\":["^
  String.concat "," rows^"],\"expanded_definitions\":["^
  String.concat "," (List.rev definitions)^
  "],\"all_equation_check_count\":218,\"expanded_definition_count\":119}\n");
 close_out oc;
 if axioms()<>initial_axioms then failwith "E3 callee: changed final axioms";
 print_endline "E3_CALLEE_LIVE_EXACT_AUDIT_PASS7_DEFS119_EQUATIONS218";;
