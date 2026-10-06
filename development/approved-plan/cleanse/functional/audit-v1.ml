let cleanse_functional_json s="\"" ^ String.escaped s ^ "\"";;
let cleanse_functional_audit initial_axioms path =
 let claims=[
  ("CLEANSE_FUNCTIONAL_PREFIX_READ",cleanse_functional_prefix_read_statement,CLEANSE_FUNCTIONAL_PREFIX_READ);
  ("OPENSSL_CLEANSE_BYTE_LOOP",cleanse_functional_byte_loop_expected,OPENSSL_CLEANSE_BYTE_LOOP)] in
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
  "\"scope\":\"All-count genuine internal byte loop under unchanged root frozen statement; memory frame/code preservation; reaches RET source before execution; no full callable/function/access/ABI claim\","^
  "\"theorems\":["^String.concat "," records^"],\"expanded_definitions\":["^String.concat "," defs^"]}\n");close_out oc;;
