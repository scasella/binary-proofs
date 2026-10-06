(* Literal live-object audit before caller reconstruction; no stored theorem objects. *)
let ht_layer_json text =
 let b=Buffer.create 256 in Buffer.add_char b '"';
 String.iter (fun c->match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\r' -> Buffer.add_string b "\\r"
  | '\t' -> Buffer.add_string b "\\t"
  | _ -> if Char.code c<32 then Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c)) else Buffer.add_char b c) text;
 Buffer.add_char b '"'; Buffer.contents b;;
let ht_layer_rows=[
("BP_E3_CRYPTO_PUBLIC_CALLER_POLICY",BP_E3_CRYPTO_PUBLIC_CALLER_POLICY,bp_e3_crypto_public_caller_policy_statement);
("BP_E3_CRYPTO_PUBLIC_CALLER_INTERFACE",BP_E3_CRYPTO_PUBLIC_CALLER_INTERFACE,bp_e3_crypto_public_caller_interface_statement);
("BP_E3_CLEANSE_PUBLIC_CALLER_POLICY",BP_E3_CLEANSE_PUBLIC_CALLER_POLICY,bp_e3_cleanse_public_caller_policy_statement);
("BP_E3_CLEANSE_PUBLIC_CALLER_INTERFACE",BP_E3_CLEANSE_PUBLIC_CALLER_INTERFACE,bp_e3_cleanse_public_caller_interface_statement);
("RA_CHECKED_RUN_APPEND",RA_CHECKED_RUN_APPEND,ra_checked_run_append_statement);
("RA_CHECKED_RUN_POST_MONO",RA_CHECKED_RUN_POST_MONO,ra_checked_run_post_mono_statement);
("RA_CHECKED_RUN_POLICY_MONO",RA_CHECKED_RUN_POLICY_MONO,ra_checked_run_policy_mono_statement);
("RA_CHECKED_RUN_THREE_SEGMENT",RA_CHECKED_RUN_THREE_SEGMENT,ra_checked_run_three_segment_statement);
("R1_SECRET_SPAN_MONO",R1_SECRET_SPAN_MONO,r1_secret_span_mono_statement);
("R1_SECRET_SPAN_SUBSPAN",R1_SECRET_SPAN_SUBSPAN,r1_secret_span_subspan_statement);
("R1_SECRET_SPAN_REGION",R1_SECRET_SPAN_REGION,r1_secret_span_region_statement);
("R1_SECRET_FOUR_FRAME_PRESERVATION",R1_SECRET_FOUR_FRAME_PRESERVATION,bp_public_four_frame_preservation_statement);
("E5_CHECKED_RUN_NORMAL",E5_CHECKED_RUN_NORMAL,e5_checked_run_normal_statement);
("E5_RF_CHECKED_RUN_NORMAL",E5_RF_CHECKED_RUN_NORMAL,e5_rf_checked_run_normal_statement);
("E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT",E5_NORMAL_CHECKED_RUN_EXTENDED_LIFT,e5_normal_checked_run_extended_lift_statement);
("E5_RF_RETIRED_STEP_NORMAL_EQ",E5_RF_RETIRED_STEP_NORMAL_EQ,e5_rf_retired_step_normal_eq_statement);
("E5_RF_RETIRED_EXTENDED_NORMAL_EQ",E5_RF_RETIRED_EXTENDED_NORMAL_EQ,e5_rf_retired_extended_normal_eq_statement);
("E5_QUALIFIED_STEP_NORMAL",E5_QUALIFIED_STEP_NORMAL,e5_qualified_step_normal_statement);
("HT_POLICY_EVENT_MONO",HT_POLICY_EVENT_MONO,ht_policy_event_mono_statement);
("HT_POLICY_ALL_MONO",HT_POLICY_ALL_MONO,ht_policy_all_mono_statement);
("HT_POLICY_STEP_MONO",HT_POLICY_STEP_MONO,ht_policy_step_mono_statement);
("HT_POLICY_SPAN",HT_POLICY_SPAN,ht_policy_span_statement);
("HT_SPAN_POINT",HT_SPAN_POINT,ht_span_point_statement);
("HT_REGION_NONOVERLAPPING",HT_REGION_NONOVERLAPPING,ht_region_nonoverlapping_statement);
("HT_SPAN_WORD_ADD_REGION",HT_SPAN_WORD_ADD_REGION,ht_span_word_add_region_statement);
("HT_REGION_DISJOINT",HT_REGION_DISJOINT,ht_region_disjoint_statement);
("HT_FRAME_CANCEL_COMPONENT",HT_FRAME_CANCEL_COMPONENT,ht_frame_cancel_component_statement);
("HT_ORIGINAL_RET",HT_ORIGINAL_RET,ht_original_ret_statement);
("BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH",BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH,bp_public_crypto_memcmp_code_length_statement);
("BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH",BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH,bp_public_openssl_cleanse_code_length_statement);
("HT_WORD_SUB_SUB",HT_WORD_SUB_SUB,ht_word_sub_sub_statement);
("ABI_CALLER_CHECKED_RUN_LIFT",ABI_CALLER_CHECKED_RUN_LIFT,abi_caller_checked_run_lift_statement);
("ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS",ABI_CALLER_EQUAL_IMPLIES_REQUIRED_CONTROLS,abi_caller_equal_controls_statement);
("ABI_CALLER_DECODED_SCALAR_UNIQUE",ABI_CALLER_DECODED_SCALAR_UNIQUE,abi_caller_decoded_scalar_unique_statement);
 ];;
let ht_layer_audit_result = map (fun (name,th,expected) ->
 if hyp th<>[] || frees(concl th)<>[] || not(aconv(concl th)expected)
 then failwith("HT_LAYER_LITERAL_OR_CLOSURE:"^name);
 let vs,_=strip_forall(concl th) in
 "{\"name\":"^ht_layer_json name^",\"status\":\"PASS\",\"conclusion\":"^
 ht_layer_json(string_of_term(concl th))^",\"hypotheses\":[],\"free_variables\":[],\"leading_quantifiers\":["^
 String.concat "," (map(fun v->"{\"name\":"^ht_layer_json(fst(dest_var v))^",\"type\":"^ht_layer_json(string_of_type(type_of v))^"}")vs)^"]}") ht_layer_rows;;
if axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then failwith"HT_LAYER_AXIOMS_CHANGED";;
let ht_layer_audit_output = try Sys.getenv "HT_LAYER_AUDIT_PATH" with Not_found -> "/output/candidate-layer-live-audit-v1.json";;
let ht_layer_audit_channel=open_out ht_layer_audit_output;;
output_string ht_layer_audit_channel ("{\"status\":\"PASS\",\"human_review\":\"PENDING\",\"hypotheses_zero\":true,\"frees_zero\":true,\"standard3_unchanged\":true,\"formal_export_count\":34,\"formal_exports\":["^String.concat "," ht_layer_audit_result^"]}\n");;
close_out ht_layer_audit_channel;;
print_endline "HT_LAYER_LIVE_LITERAL_AUDIT_COMPLETE";;
