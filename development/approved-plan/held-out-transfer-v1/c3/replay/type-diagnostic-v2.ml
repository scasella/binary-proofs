(* PRE-FREEZE ELABORATION ONLY. No caller proof, goal closing, symbolic execution or solver search. *)
needs "/c3-input/contract/definitions-v2.ml";;
needs "/c3-input/contract/statements-v1.ml";;
needs "/c3-input/contract/witness-definitions-v1.ml";;
needs "/c3-input/contract/witness-statements-v1.ml";;
let c3_td_json text =
 let b=Buffer.create 256 in Buffer.add_char b '"';
 String.iter (fun c->match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\r' -> Buffer.add_string b "\\r"
  | '\t' -> Buffer.add_string b "\\t"
  | _ -> if Char.code c<32 then Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c)) else Buffer.add_char b c) text;
 Buffer.add_char b '"'; Buffer.contents b;;
let c3_td_var v = "{\"name\":"^c3_td_json(fst(dest_var v))^",\"type\":"^c3_td_json(string_of_type(type_of v))^"}";;
let c3_td_term_rows=[
("c3_checked_statement",c3_checked_statement);
("c3_interface_statement",c3_interface_statement);
("c3_normal_checked_statement",c3_normal_checked_statement);
("c3_rf_normal_checked_statement",c3_rf_normal_checked_statement);
("c3_normal_interface_statement",c3_normal_interface_statement);
("c3_handoff_statement",c3_handoff_statement);
("c3_count_statement",c3_count_statement);
("c3w_pre_statement",c3w_pre_statement);
("c3w_generic_witness_statement",c3w_generic_witness_statement);
("c3_admissible_entry_witnesses_statement",c3_admissible_entry_witnesses_statement);
];;
let c3_td_term_reports = map(fun (name,tm)->
 let fs=frees tm in if fs<>[] then failwith("C3_TERM_HAS_FREE_VARIABLES:"^name);
 if type_of tm<>`:bool` then failwith("C3_TERM_NOT_BOOLEAN:"^name);
 let vs,_=strip_forall tm in
 "{\"name\":"^c3_td_json name^",\"term\":"^c3_td_json(string_of_term tm)^",\"type\":"^c3_td_json(string_of_type(type_of tm))^",\"frees\":[],\"leading_quantifiers\":["^String.concat ","(map c3_td_var vs)^"]}") c3_td_term_rows;;
let c3_td_definition_rows=[
("c3_caller_mc",c3_caller_mc);
("c3_crypto_plt_prefix",c3_crypto_plt_prefix);
("c3_cleanse_plt_prefix",c3_cleanse_plt_prefix);
("c3_equal",c3_equal);
("c3_image_domain",c3_image_domain);
("c3_image_execute",c3_image_execute);
("c3_image_write",c3_image_write);
("c3_immutable",c3_immutable);
("c3_initialized_rw",c3_initialized_rw);
("c3_reference_image",c3_reference_image);
("c3_full_image",c3_full_image);
("c3_file_code",c3_file_code);
("c3_loaded_code",c3_loaded_code);
("c3_got",c3_got);
("c3_scratch",c3_scratch);
("c3_allowed_read",c3_allowed_read);
("c3_allowed_write",c3_allowed_write);
("c3_allowed_fetch",c3_allowed_fetch);
("c3_cleansed_memory",c3_cleansed_memory);
("c3_result",c3_result);
("c3_steps",c3_steps);
("c3_frame",c3_frame);
("c3_pre",c3_pre);
("c3_scalar_post",c3_scalar_post);
("c3_public_post",c3_public_post);
("c3_step_policy",c3_step_policy);
("c3_segment_policy",c3_segment_policy);
("c3_saved_prefix",c3_saved_prefix);
("c3_prefix_frame",c3_prefix_frame);
("c3_crypto_ready",c3_crypto_ready);
("c3w_external",c3w_external);
("c3w_layout",c3w_layout);
("c3w_seed",c3w_seed);
("c3w_memory",c3w_memory);
("c3w_state",c3w_state);
("c3w_read",c3w_read);
("c3w_write",c3w_write);
("c3w_execute",c3w_execute);
("c3w_ordinary",c3w_ordinary);
("c3_entry_witness",c3_entry_witness);
];;
let c3_td_definition_reports=map(fun(name,th)->
 if hyp th<>[] then failwith("C3_DEFINITION_HYPOTHESES:"^name);
 "{\"name\":"^c3_td_json name^",\"equation\":"^c3_td_json(string_of_term(concl th))^",\"hypotheses\":[],\"equation_frees\":["^String.concat ","(map c3_td_var(frees(concl th)))^"]}") c3_td_definition_rows;;
if axioms()<>[INFINITY_AX;SELECT_AX;ETA_AX] then failwith"C3_TYPE_DIAGNOSTIC_AXIOMS_CHANGED";;
let c3_td_file=open_out "/output/c3-type-diagnostic-v2.json";;
output_string c3_td_file ("{\"status\":\"PARSED_TYPED_CLOSED_STATEMENTS_ONLY\",\"proof_claim\":false,\"human_review\":\"PENDING\",\"standard3_unchanged\":true,\"terms\":["^String.concat "," c3_td_term_reports^"],\"definitions\":["^String.concat "," c3_td_definition_reports^"]}\n");;
close_out c3_td_file;;
print_endline "C3_PREFREEZE_TERM_TYPE_DIAGNOSTIC_COMPLETE";;
