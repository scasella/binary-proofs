(* Exact target/closure inspection after successful construction.
   This is not a formal proof-dependency isolation test. *)
let bp_reuse_linkage_targets =
 ["BP_REUSE_DECODED_STEP",bp_reuse_decoded_step_statement,BP_REUSE_DECODED_STEP;
  "BP_REUSE_RIPREL_JUMP_SUCCESSOR",bp_reuse_riprel_jump_successor_statement,
    BP_REUSE_RIPREL_JUMP_SUCCESSOR;
  "BP_REUSE_RIPREL_JUMP_CHECKED_HOP",bp_reuse_riprel_jump_checked_hop_statement,
    BP_REUSE_RIPREL_JUMP_CHECKED_HOP;
  "BP_REUSE_RIPREL_JUMP_OMITTED",bp_reuse_riprel_jump_omitted_statement,
    BP_REUSE_RIPREL_JUMP_OMITTED;
  "BP_C1_PLT_DECODE",bp_c1_plt_decode_statement,BP_C1_PLT_DECODE;
  "BP_C1_PLT_CHECKED_HOP",bp_c1_plt_checked_hop_statement,BP_C1_PLT_CHECKED_HOP];;
List.iter (fun (name,expected,th) ->
 if not(aconv expected (concl th)) then failwith(name^": wrong literal target");
 if hyp th <> [] then failwith(name^": residual hypotheses");
 if frees(concl th) <> [] then failwith(name^": free variables");
 Printf.printf "LINKAGE_TARGET_CHECKED %s\n%!" name)
 bp_reuse_linkage_targets;;
