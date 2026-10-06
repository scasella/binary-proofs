let crypto_observation_json s="\"" ^ String.escaped s ^ "\"";;
let crypto_observation_audit initial_axioms path =
 let claims=[
  ("ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS",crypto_observation_actual_bridge_statement,ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS);
  ("CRYPTO_OBSERVATION_BODY7",crypto_observation_body7_statement,CRYPTO_OBSERVATION_BODY7);
  ("CRYPTO_OBSERVATION_LOOP",crypto_observation_loop_statement,CRYPTO_OBSERVATION_LOOP);
  ("CRYPTO_OBSERVATION_CALLABLE",crypto_observation_callable_statement,CRYPTO_OBSERVATION_CALLABLE);
  ("CRYPTO_OBSERVATION_UNIQUE",crypto_observation_unique_statement,CRYPTO_OBSERVATION_UNIQUE);
  ("CRYPTO_OBSERVATION_MONO",crypto_observation_mono_statement,CRYPTO_OBSERVATION_MONO);
  ("CRYPTO_OBSERVATION_PROJECT",crypto_observation_project_statement,CRYPTO_OBSERVATION_PROJECT);
  ("CRYPTO_OBSERVATION_EXECUTION_EXACT",crypto_observation_execution_exact_statement,CRYPTO_OBSERVATION_EXECUTION_EXACT);
  ("CRYPTO_OBSERVATION_LOOP_LENGTH",crypto_observation_loop_length_statement,CRYPTO_OBSERVATION_LOOP_LENGTH);
  ("CRYPTO_OBSERVATION_CALL_LENGTH",crypto_observation_call_length_statement,CRYPTO_OBSERVATION_CALL_LENGTH);
  ("CRYPTO_OBSERVATION_E2",crypto_observation_e2_statement,CRYPTO_OBSERVATION_E2);
  ("CRYPTO_OBSERVATION_RELATIONAL",crypto_observation_relational_statement,CRYPTO_OBSERVATION_RELATIONAL);
  ("CRYPTO_OBSERVATION_ALL_PAIRS",crypto_observation_all_pairs_statement,CRYPTO_OBSERVATION_ALL_PAIRS)] in
 let definitions=[("crypto_observed_run",crypto_observed_run);
  ("crypto_observed_execution",crypto_observed_execution);
  ("crypto_public_decode",crypto_public_decode);("crypto_public_observation",crypto_public_observation);
  ("crypto_public_entry5",crypto_public_entry5);("crypto_public_entry7",crypto_public_entry7);
  ("crypto_public_body7",crypto_public_body7);("crypto_public_exit",crypto_public_exit);
  ("crypto_public_loop",crypto_public_loop);("crypto_public_call",crypto_public_call)] in
 let records=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": wrong exact conclusion");
  if axioms()<>initial_axioms then failwith(name^": new axioms");
  "{\"name\":"^crypto_observation_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0,"^
  "\"statement\":"^crypto_observation_json(string_of_term(concl th))^"}") claims in
 let defs=List.map(fun(name,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  "{\"name\":"^crypto_observation_json name^",\"hypothesis_count\":0,\"statement\":"^
  crypto_observation_json(string_of_term(concl th))^"}") definitions in
 let oc=open_out path in output_string oc
  ("{\"status\":\"PASS_ALL_LENGTH_ARCHITECTURAL_OBSERVATION_COMPONENT\",\"full_O2_pass\":false,"^
  "\"scope\":\"Exact whole original transition observation schema; progress+every successor; actual preRIP/decoded length/instruction/ordered event deltas; same-E2-Pre arbitrary memories and every full-count observed execution pair; physical/microarchitectural correspondence separate\","^
  "\"theorems\":["^String.concat "," records^"],\"expanded_definitions\":["^String.concat "," defs^"]}\n");close_out oc;;
