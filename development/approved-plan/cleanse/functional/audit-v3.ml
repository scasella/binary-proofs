let cleanse_functional_json s="\"" ^ String.escaped s ^ "\"";;
let cleanse_functional_audit initial_axioms path =
 let claims=[
  ("CLEANSE_FUNCTIONAL_PREFIX_READ",cleanse_functional_prefix_read_statement,CLEANSE_FUNCTIONAL_PREFIX_READ);
  ("OPENSSL_CLEANSE_BYTE_LOOP",cleanse_functional_byte_loop_expected,OPENSSL_CLEANSE_BYTE_LOOP);
  ("CLEANSE_FUNCTIONAL_BULK_MASK",cleanse_functional_bulk_mask_statement,CLEANSE_FUNCTIONAL_BULK_MASK);
  ("CLEANSE_FUNCTIONAL_PREFIX_READ64",cleanse_functional_prefix_read64_statement,CLEANSE_FUNCTIONAL_PREFIX_READ64);
  ("OPENSSL_CLEANSE_BULK_LOOP",cleanse_functional_bulk_loop_statement,OPENSSL_CLEANSE_BULK_LOOP);
  ("CLEANSE_FUNCTIONAL_LOW3",cleanse_functional_low3_statement,CLEANSE_FUNCTIONAL_LOW3);
  ("OPENSSL_CLEANSE_ALIGNMENT",cleanse_functional_alignment_statement,OPENSSL_CLEANSE_ALIGNMENT)] in
 if not(aconv(cleanse_functional_byte_loop_expected)cleanse_byte_loop_statement) then
  failwith "Independent byte-loop expected term differs from unchanged frozen root target";
 let definitions=[("bp_e2_cleanse_pre",bp_e2_cleanse_pre);
  ("bp_e2_cleanse_allowed_read",bp_e2_cleanse_allowed_read);
  ("bp_e2_cleanse_allowed_write",bp_e2_cleanse_allowed_write);
  ("bp_e2_cleanse_allowed_fetch",bp_e2_cleanse_allowed_fetch)] in
 let records=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": wrong exact conclusion");
  if axioms()<>initial_axioms then failwith(name^": new axioms");
  "{\"name\":"^cleanse_functional_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0,"^
  "\"statement\":"^cleanse_functional_json(string_of_term(concl th))^"}") claims in
 let defs=List.map(fun(name,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  "{\"name\":"^cleanse_functional_json name^",\"hypothesis_count\":0,\"statement\":"^
  cleanse_functional_json(string_of_term(concl th))^"}") definitions in
 let oc=open_out path in output_string oc
  ("{\"status\":\"PASS_MODELED_CLEANSE_FUNCTIONAL_COMPONENT\",\"full_O1_pass\":false,\"full_O2_pass\":false,"^
  "\"scope\":\"Genuine all-count internal byte/bulk loops and every public first-hit alignment prefix, including arbitrary 0-7 byte bulk tails; memory frame/code preservation; endpoints before actual RET; no full callable/access/ABI/O1 claim\","^
  "\"theorems\":["^String.concat "," records^"],\"expanded_definitions\":["^String.concat "," defs^"]}\n");close_out oc;;
