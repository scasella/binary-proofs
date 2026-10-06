(* Live HOL theorem-object audit; exact terms are independently frozen. *)
List.iter (fun r -> r := None)
 [printer_color_const; printer_color_resword; printer_color_binder;
  printer_color_infix; printer_color_prefix; printer_color_type;
  printer_color_typevar; printer_color_itypevar];;
let byte_contract_audit path =
 let items =
  ["BP_READ_BYTES_AT_ZERO",bp_read_bytes_at_zero_statement,BP_READ_BYTES_AT_ZERO;
   "BP_READ_BYTES_DIFFERENT_EQ",bp_read_bytes_different_eq_statement,BP_READ_BYTES_DIFFERENT_EQ;
   "BP_PREFIX_16_SPLIT",bp_prefix_16_split_statement,BP_PREFIX_16_SPLIT;
   "BP_WORDPAIR_BYTE16",bp_wordpair_byte16_statement,BP_WORDPAIR_BYTE16;
   "BP_CRYPTO_MEMCMP_16_BYTES_RETURN",bp_crypto_16_bytes_statement,
                                      BP_CRYPTO_MEMCMP_16_BYTES_RETURN] in
 let audited = List.map (fun (name,expected,th) ->
   if hyp th <> [] then failwith(name^": nonempty hypotheses");
   if not(aconv(concl th) expected) then failwith(name^": expected term mismatch");
   if axioms() <> byte_contract_initial_axioms then failwith(name^": added axioms");
   "{\"name\":" ^ Printf.sprintf "%S" name ^
   ",\"statement\":" ^ Printf.sprintf "%S" (string_of_term(concl th)) ^
   ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true}") items in
 let oc = open_out path in
 output_string oc ("{\"status\":\"PASS_BYTE_CONTRACT_HELPERS\",\"full_O1_pass\":false,"^
  "\"theorems\":["^String.concat "," audited^"]}\n"); close_out oc;;
