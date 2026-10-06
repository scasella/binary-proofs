(* Operational validation of the three exact frozen witness bindings only.
   Execute after successful declarations. This does not construct a theorem.
   Replay owns the independent exact standard-three-axiom identity check. *)
let c3w_literal_targets_audit_v1 =
 [("C3W_PRE",C3W_PRE,c3w_pre_statement);
  ("C3W_GENERIC_WITNESS",C3W_GENERIC_WITNESS,c3w_generic_witness_statement);
  ("C3_ADMISSIBLE_ENTRY_WITNESSES",C3_ADMISSIBLE_ENTRY_WITNESSES,
    c3_admissible_entry_witnesses_statement)];;
List.iter
 (fun (name,theorem,literal) ->
    if type_of literal <> `:bool` then
      failwith ("C3W_LITERAL_TYPE_FAILURE:" ^ name);
    if not(aconv (concl theorem) literal) then
      failwith ("C3W_LITERAL_TARGET_MISMATCH:" ^ name);
    if hyp theorem <> [] then
      failwith ("C3W_LITERAL_OPEN_HYPOTHESES:" ^ name);
    if frees(concl theorem) <> [] then
      failwith ("C3W_LITERAL_FREE_VARIABLES:" ^ name);
    Printf.printf "C3W_LITERAL_TARGET_AUDIT_PASS:%s\n" name;
    print_thm theorem)
 c3w_literal_targets_audit_v1;;
if List.length(axioms()) <> 3 then
  failwith "C3W_LITERAL_AXIOM_COUNT_CHANGED";;
print_endline "C3W_LITERAL_THREE_TARGET_AUDIT_V1_COMPLETE";;
