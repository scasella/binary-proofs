(* Actual seven caller/PLT transitions and complete cleanup endpoint.
   All dependencies are source-reconstructed by the successor loader. *)
let C3_CLEANUP_HANDOFF = prove(c3_cleanup_handoff_abi_local_statement,
 C3_CLEANUP_INITIAL_FACTS_TAC THEN C3_CLEANUP_PERMISSION_FACTS_TAC THEN
 C3_CLEANUP_ACTUAL_SEVEN_TAC THEN C3_CLEANUP_ENDPOINT_CORE_TAC THEN
 C3_CLEANUP_ENDPOINT_TOTAL_FRAME_TAC THEN C3_CLEANUP_ENDPOINT_PUBLIC_UNFOLD_TAC THEN
 REWRITE_TAC[ASSUME `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])(initial:x86state)(u7:x86state)`]);;
if hyp C3_CLEANUP_HANDOFF<>[] || frees(concl C3_CLEANUP_HANDOFF)<>[] ||
 not(aconv(concl C3_CLEANUP_HANDOFF)c3_cleanup_handoff_abi_local_statement)
then failwith "C3_SUCCESSOR_CLEANUP_HANDOFF_LITERAL_CLOSURE";;
print_endline "C3_SUCCESSOR_CLEANUP_HANDOFF_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
print_thm C3_CLEANUP_HANDOFF;;
