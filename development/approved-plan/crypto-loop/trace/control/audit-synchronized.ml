let crypto_control_sync_json s="\"" ^ String.escaped s ^ "\"";;
let crypto_control_sync_audit initial_axioms path =
 let claims=[
  ("CRYPTO_CONTROL_BODY7",crypto_control_body7_statement,CRYPTO_CONTROL_BODY7);
  ("CRYPTO_CONTROL_LOOP_SCALAR",crypto_control_loop_scalar_statement,CRYPTO_CONTROL_LOOP_SCALAR);
  ("CRYPTO_CONTROL_GENERIC_SCALAR",crypto_control_generic_scalar_statement,CRYPTO_CONTROL_GENERIC_SCALAR);
  ("CRYPTO_CONTROL_RUN_POST",crypto_control_run_post_statement,CRYPTO_CONTROL_RUN_POST);
  ("CRYPTO_CONTROL_RUN_MONO",crypto_control_run_mono_statement,CRYPTO_CONTROL_RUN_MONO);
  ("CRYPTO_CONTROL_GENERIC_COMBINED",crypto_control_generic_combined_statement,CRYPTO_CONTROL_GENERIC_COMBINED);
  ("CRYPTO_BOUNDED_ITERATION",crypto_bounded_iteration_statement,CRYPTO_BOUNDED_ITERATION);
  ("CRYPTO_BOUNDED_LOOP_EVENTS",crypto_bounded_loop_statement,CRYPTO_BOUNDED_LOOP_EVENTS);
  ("CRYPTO_BOUNDED_GENERIC_CORE",crypto_bounded_generic_core_statement,CRYPTO_BOUNDED_GENERIC_CORE);
  ("CRYPTO_BOUNDED_GENERIC_RETURN",crypto_bounded_generic_return_statement,CRYPTO_BOUNDED_GENERIC_RETURN);
  ("CRYPTO_BOUNDED_ZERO_RETURN",crypto_bounded_zero_statement,CRYPTO_BOUNDED_ZERO_RETURN);
  ("CRYPTO_BOUNDED_16_RETURN",crypto_bounded_16_statement,CRYPTO_BOUNDED_16_RETURN);
  ("CRYPTO_BOUNDED_16_BYTES_RETURN",crypto_bounded_16_bytes_statement,CRYPTO_BOUNDED_16_BYTES_RETURN)] in
 let records=List.map (fun (name,expected,th) ->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": wrong exact conclusion");
  if axioms()<>initial_axioms then failwith(name^": new axioms");
  "{\"name\":"^crypto_control_sync_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0,"^
  "\"statement\":"^crypto_control_sync_json(string_of_term(concl th))^"}") claims in
 let oc=open_out path in
 output_string oc ("{\"status\":\"PASS_CONTROL_BOUNDED_SYNCHRONIZED_COMPONENT\",\"full_O1_pass\":false,"^
  "\"scope\":\"Generic same-endpoint byte functionality/frame/events plus every-original-successor progress/fetch/data policy/scalar qualification/final actualRET; bounded restricted functional components; shared E2 wrappers separate\","^
  "\"theorems\":["^String.concat "," records^"]}\n");close_out oc;;
