let crypto_control_audit path =
 let claims=[
  ("CRYPTO_CONTROL_BODY7",crypto_control_body7_statement,CRYPTO_CONTROL_BODY7);
  ("CRYPTO_CONTROL_LOOP_SCALAR",crypto_control_loop_scalar_statement,CRYPTO_CONTROL_LOOP_SCALAR);
  ("CRYPTO_CONTROL_GENERIC_SCALAR",crypto_control_generic_scalar_statement,CRYPTO_CONTROL_GENERIC_SCALAR)] in
 let records=List.map crypto_trace_audit_claim claims in let oc=open_out path in
 output_string oc ("{\"status\":\"PASS_CONTROL_SCALAR_COMPONENT\",\"full_O1_pass\":false,"^
  "\"scope\":\"Original every-successor exact finite runs; progress, every fetch/data policy, source scalar qualification and final actualRET; functional endpoint synchronization separate\","^
  "\"theorems\":["^String.concat "," records^"]}\n");close_out oc;;
