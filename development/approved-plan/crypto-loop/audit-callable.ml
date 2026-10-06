let crypto_dev_json s = "\"" ^ String.escaped s ^ "\"";;
let crypto_dev_audit_claim (name,expected,th) =
 if hyp th <> [] then failwith(name ^ ": hypotheses");
 if not(aconv(concl th) expected) then failwith(name ^ ": wrong exact conclusion");
 if axioms() <> crypto_dev_initial_axioms then failwith(name ^ ": new axioms");
 "{\"name\":" ^ crypto_dev_json name ^
 ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0," ^
 "\"statement\":" ^ crypto_dev_json(string_of_term(concl th)) ^ "}";;
let crypto_dev_audit_callable path =
 let claims = [
  ("CRYPTO_MEMCMP_BYTE_LOOP_CORRECT",crypto_byte_loop_statement,CRYPTO_MEMCMP_BYTE_LOOP_CORRECT);
  ("CRYPTO_MEMCMP_GENERIC_CORE_CORRECT",crypto_dev_generic_core_statement,CRYPTO_MEMCMP_GENERIC_CORE_CORRECT);
  ("CRYPTO_MEMCMP_GENERIC_MODELED_RETURN",crypto_dev_generic_return_statement,CRYPTO_MEMCMP_GENERIC_MODELED_RETURN);
  ("CRYPTO_MEMCMP_ALL_LENGTH_MODELED_RETURN",crypto_dev_callable_statement,CRYPTO_MEMCMP_ALL_LENGTH_MODELED_RETURN)] in
 let records = List.map crypto_dev_audit_claim claims in
 let oc = open_out path in
 output_string oc ("{\"status\":\"PASS_ALL_LENGTH_MODELED_CALLABLE_COMPONENT\"," ^
  "\"full_O1_pass\":false,\"scope\":\"Modeled all-length byte-sequence functional/return/frame, not full policy/fetch/ABI/witness package\"," ^
  "\"theorems\":[" ^ String.concat "," records ^ "]}\n");
 close_out oc;;
