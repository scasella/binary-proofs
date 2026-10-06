let cleanse_functional_json s="\"" ^ String.escaped s ^ "\"";;
let cleanse_functional_audit initial_axioms path =
 let claims=[
  ("CLEANSE_FUNCTIONAL_PREFIX_READ",cleanse_functional_prefix_read_statement,CLEANSE_FUNCTIONAL_PREFIX_READ);
  ("OPENSSL_CLEANSE_BYTE_LOOP",cleanse_functional_byte_loop_expected,OPENSSL_CLEANSE_BYTE_LOOP);
  ("CLEANSE_FUNCTIONAL_BULK_MASK",cleanse_functional_bulk_mask_statement,CLEANSE_FUNCTIONAL_BULK_MASK);
  ("CLEANSE_FUNCTIONAL_PREFIX_READ64",cleanse_functional_prefix_read64_statement,CLEANSE_FUNCTIONAL_PREFIX_READ64);
  ("OPENSSL_CLEANSE_BULK_LOOP",cleanse_functional_bulk_loop_statement,OPENSSL_CLEANSE_BULK_LOOP);
  ("CLEANSE_FUNCTIONAL_LOW3",cleanse_functional_low3_statement,CLEANSE_FUNCTIONAL_LOW3);
  ("OPENSSL_CLEANSE_ALIGNMENT",cleanse_functional_alignment_statement,OPENSSL_CLEANSE_ALIGNMENT);
  ("CLEANSE_FUNCTIONAL_ALIGNMENT_COUNT",cleanse_functional_alignment_count_statement,CLEANSE_FUNCTIONAL_ALIGNMENT_COUNT);
  ("CLEANSE_FUNCTIONAL_CONCAT_ZERO",cleanse_functional_concat_zero_statement,CLEANSE_FUNCTIONAL_CONCAT_ZERO);
  ("OPENSSL_CLEANSE_BULK_TAIL",cleanse_functional_bulk_tail_statement,OPENSSL_CLEANSE_BULK_TAIL);
  ("OPENSSL_CLEANSE_FUNCTIONAL_CORE",cleanse_functional_core_statement,OPENSSL_CLEANSE_FUNCTIONAL_CORE);
  ("OPENSSL_CLEANSE_FUNCTIONAL_CALLABLE",cleanse_functional_callable_statement,OPENSSL_CLEANSE_FUNCTIONAL_CALLABLE);
  ("OPENSSL_CLEANSE_BOUNDED_BYTE_LOOP",cleanse_functional_bounded_byte_statement,OPENSSL_CLEANSE_BOUNDED_BYTE_LOOP);
  ("OPENSSL_CLEANSE_BOUNDED_BULK_LOOP",cleanse_functional_bounded_bulk_statement,OPENSSL_CLEANSE_BOUNDED_BULK_LOOP);
  ("OPENSSL_CLEANSE_BOUNDED_ALIGNMENT",cleanse_functional_bounded_alignment_statement,OPENSSL_CLEANSE_BOUNDED_ALIGNMENT);
  ("OPENSSL_CLEANSE_BOUNDED_BULK_TAIL",cleanse_functional_bounded_bulk_tail_statement,OPENSSL_CLEANSE_BOUNDED_BULK_TAIL);
  ("OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CORE",cleanse_functional_bounded_core_statement,OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CORE);
  ("OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CALLABLE",cleanse_functional_bounded_callable_statement,OPENSSL_CLEANSE_BOUNDED_FUNCTIONAL_CALLABLE);
  ("CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING",cleanse_regions_disjoint_nonoverlapping_statement,CLEANSE_REGIONS_DISJOINT_NONOVERLAPPING);
  ("CLEANSE_REGION_WORD_SUB",cleanse_region_word_sub_statement,CLEANSE_REGION_WORD_SUB);
  ("CLEANSE_MEMORY_WRITE_BYTES_OUTSIDE",cleanse_memory_write_bytes_outside_statement,CLEANSE_MEMORY_WRITE_BYTES_OUTSIDE);
  ("CLEANSE_STATE_WRITE_BYTES_OUTSIDE",cleanse_state_write_bytes_outside_statement,CLEANSE_STATE_WRITE_BYTES_OUTSIDE);
  ("CLEANSE_FUNCTIONAL_FRAME_OUTSIDE",cleanse_functional_frame_outside_statement,CLEANSE_FUNCTIONAL_FRAME_OUTSIDE);
  ("BP_E2_CLEANSE_BOUNDED_FUNCTIONAL_RETURN",cleanse_functional_e2_bounded_statement,BP_E2_CLEANSE_BOUNDED_FUNCTIONAL_RETURN);
  ("BP_E2_CLEANSE_FUNCTIONAL_RETURN",bp_e2_cleanse_functional_statement,BP_E2_CLEANSE_FUNCTIONAL_RETURN)] in
 if not(aconv(cleanse_functional_byte_loop_expected)cleanse_byte_loop_statement) then
  failwith "Independent byte-loop expected term differs from unchanged frozen root target";
 let definitions=[("bp_e2_cleanse_pre",bp_e2_cleanse_pre);
  ("bp_e2_cleanse_allowed_read",bp_e2_cleanse_allowed_read);
  ("bp_e2_cleanse_allowed_write",bp_e2_cleanse_allowed_write);
  ("bp_e2_cleanse_allowed_fetch",bp_e2_cleanse_allowed_fetch);
  ("cleanse_alignment_count",cleanse_alignment_count);
  ("cleanse_functional_steps",cleanse_functional_steps);
  ("assurance_region",assurance_region);
  ("assurance_span_ok",assurance_span_ok);
  ("assurance_canonical48",assurance_canonical48)] in
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
  "\"scope\":\"Whole actual OPENSSL_cleanse all-count modeled functional return and destination-only memory frame, exact finite count under unchanged full E2 Pre; public alignment/bulk/tail decomposition; no full access/ABI/O1/O2 acceptance claim\","^
  "\"theorems\":["^String.concat "," records^"],\"expanded_definitions\":["^String.concat "," defs^"]}\n");close_out oc;;
