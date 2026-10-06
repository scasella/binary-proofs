let cleanse_access_code_offset_value_expected =
 `!pc off. pc+97<=2 EXP 64 /\ off<97 ==> val(word(pc+off):int64)=pc+off`;;
let cleanse_access_code_base_value_expected =
 `!pc. pc+97<=2 EXP 64 ==> val(word pc:int64)=pc`;;
let cleanse_access_span_head_expected =
 `!wp p n width. assurance_span_ok wp (val(p:int64)) n /\ width<=n
    ==> assurance_span_ok wp (val p) width`;;
let cleanse_access_span_tail_expected =
 `!wp p n off. assurance_span_ok wp (val(p:int64)) n /\ off<=n
    ==> assurance_span_ok wp (val(word_add p (word off))) (n-off)`;;
let cleanse_access_nonoverlap_tail_expected =
 `!base width p n off count. nonoverlapping (base:int64,width) (p,n) /\ off+count<=n
    ==> nonoverlapping (base,width) (word_add p (word off),count)`;;
let cleanse_access_json s="\"" ^ String.escaped s ^ "\"";;
let cleanse_access_audit initial_axioms path =
 let claims=[
  ("CLEANSE_ACCESS_CODE_OFFSET_VALUE",cleanse_access_code_offset_value_expected,CLEANSE_ACCESS_CODE_OFFSET_VALUE);
  ("CLEANSE_ACCESS_CODE_BASE_VALUE",cleanse_access_code_base_value_expected,CLEANSE_ACCESS_CODE_BASE_VALUE);
  ("CLEANSE_ACCESS_SPAN_HEAD",cleanse_access_span_head_expected,CLEANSE_ACCESS_SPAN_HEAD);
  ("CLEANSE_ACCESS_SPAN_TAIL",cleanse_access_span_tail_expected,CLEANSE_ACCESS_SPAN_TAIL);
  ("CLEANSE_ACCESS_NONOVERLAP_TAIL",cleanse_access_nonoverlap_tail_expected,CLEANSE_ACCESS_NONOVERLAP_TAIL);
  ("CLEANSE_ACCESS_BYTE_RETURN",cleanse_access_byte_return_statement,CLEANSE_ACCESS_BYTE_RETURN);
  ("CLEANSE_ACCESS_TAIL_RETURN",cleanse_access_tail_return_statement,CLEANSE_ACCESS_TAIL_RETURN);
  ("CLEANSE_ACCESS_BULK_RETURN",cleanse_access_bulk_return_statement,CLEANSE_ACCESS_BULK_RETURN);
  ("CLEANSE_ACCESS_ALIGNMENT_RETURN",cleanse_access_alignment_return_statement,CLEANSE_ACCESS_ALIGNMENT_RETURN);
  ("CLEANSE_ACCESS_ALL_LENGTH",cleanse_access_all_length_statement,CLEANSE_ACCESS_ALL_LENGTH);
  ("CLEANSE_ACCESS_PRE_PERMISSIONS",cleanse_access_pre_permissions_statement,CLEANSE_ACCESS_PRE_PERMISSIONS);
  ("CLEANSE_ACCESS_LARGE_DECOMPOSITION",cleanse_access_large_decomposition_statement,CLEANSE_ACCESS_LARGE_DECOMPOSITION);
  ("CLEANSE_ACCESS_COVERED_DECODE_QUALIFIED",cleanse_access_covered_decode_qualified_statement,CLEANSE_ACCESS_COVERED_DECODE_QUALIFIED);
  ("CLEANSE_ACCESS_CHECKED_RUN_QUALIFIED",cleanse_access_checked_run_qualified_statement,CLEANSE_ACCESS_CHECKED_RUN_QUALIFIED);
  ("CLEANSE_ACCESS_COUNT_AGREEMENT",cleanse_access_count_agreement_statement,CLEANSE_ACCESS_COUNT_AGREEMENT);
  ("CLEANSE_ACCESS_ORIGINAL_RETURN",cleanse_access_original_return_statement,CLEANSE_ACCESS_ORIGINAL_RETURN);
  ("CLEANSE_ACCESS_QUALIFIED_RETURN",cleanse_access_qualified_return_statement,CLEANSE_ACCESS_QUALIFIED_RETURN);
  ("CLEANSE_ACCESS_EXTENDED_RETURN",cleanse_access_extended_return_statement,CLEANSE_ACCESS_EXTENDED_RETURN)] in
 let definitions=[
  ("cleanse_access_count",cleanse_access_count);
  ("cleanse_access_covered_step",cleanse_access_covered_step);
  ("cleanse_access_return_post",cleanse_access_return_post);
  ("cleanse_access_loop_pre",cleanse_access_loop_pre);
  ("bp_e2_cleanse_pre",bp_e2_cleanse_pre);
  ("bp_e2_cleanse_allowed_read",bp_e2_cleanse_allowed_read);
  ("bp_e2_cleanse_allowed_write",bp_e2_cleanse_allowed_write);
  ("bp_e2_cleanse_allowed_fetch",bp_e2_cleanse_allowed_fetch);
  ("assurance_region",assurance_region);
  ("assurance_span_ok",assurance_span_ok);
  ("assurance_canonical48",assurance_canonical48);
  ("assurance_checked_run",assurance_checked_run);
  ("assurance_step_policy",assurance_step_policy);
  ("assurance_zero_step",assurance_zero_step);
  ("cleanse_functional_steps",cleanse_functional_steps);
  ("abi_cleanse_site",abi_cleanse_site);
  ("abi_cleanse_scalar_instruction",abi_cleanse_scalar_instruction);
  ("abi_cleanse_scalar_extended_step",abi_cleanse_scalar_extended_step);
  ("abi_all_decodes_cleanse_scalar",abi_all_decodes_cleanse_scalar)] in
 if axioms()<>initial_axioms then failwith "access audit: new axioms";
 let records=List.map(fun(name,expected,th)->
  if hyp th<>[] then failwith(name^": hypotheses");
  if not(aconv(concl th) expected) then failwith(name^": wrong exact conclusion");
  "{\"name\":"^cleanse_access_json name^
  ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0,"^
  "\"statement\":"^cleanse_access_json(string_of_term(concl th))^"}") claims in
 let defs=List.map(fun(name,th)->
  if hyp th<>[] then failwith(name^": definition hypotheses");
  "{\"name\":"^cleanse_access_json name^",\"hypothesis_count\":0,\"statement\":"^
  cleanse_access_json(string_of_term(concl th))^"}") definitions in
 let audit_channel=open_out path in output_string audit_channel
  ("{\"status\":\"PASS_MODELED_CLEANSE_ALL_LENGTH_ACCESS_COMPONENT\",\"full_O1_pass\":false,\"full_O2_pass\":false,"^
  "\"scope\":\"Unchanged full E2 Pre, every length below 2^64, every original successor, exact finite count, full-width strict writes/slot-only reads/exact-code fetches, actual RET, and derived V5 scalar qualification and omitted-record preservation; human model/spec review pending\","^
  "\"theorems\":["^String.concat "," records^"],\"expanded_definitions\":["^String.concat "," defs^"]}\n");close_out audit_channel;;
