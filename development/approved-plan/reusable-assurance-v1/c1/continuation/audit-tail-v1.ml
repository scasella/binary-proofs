(* Live logical-object audit; a displayed log is not a proof object. *)
let c1_tail_audit name expected theorem =
 if not (aconv expected (concl theorem)) then failwith (name ^ ": literal mismatch");
 if hyp theorem <> [] then failwith (name ^ ": hypotheses");
 if frees (concl theorem) <> [] then failwith (name ^ ": free variables");
 if axioms() <> reuse_c1_foundation_axioms then failwith (name ^ ": axiom delta");
 print_endline ("C1_TAIL_LIVE_AUDITED " ^ name);;
c1_tail_audit "C1_TAIL_CHECKED" c1_tail_checked_statement C1_TAIL_CHECKED;;
c1_tail_audit "C1_TAIL_RETURN_RSP_VALUE" c1_tail_return_rsp_value_statement C1_TAIL_RETURN_RSP_VALUE;;
