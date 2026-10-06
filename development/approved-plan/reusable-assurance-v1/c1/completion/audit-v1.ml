(* Exact frozen literal, closure and global-axiom audit. *)
let c1_completion_audit_goal name expected actual =
 if hyp actual <> [] then failwith ("C1_COMPLETION_NONEMPTY_HYPOTHESES "^name);
 if frees(concl actual) <> [] then failwith ("C1_COMPLETION_FREE_VARIABLES "^name);
 if not(aconv expected (concl actual)) then failwith ("C1_COMPLETION_LITERAL_MISMATCH "^name);
 let permitted=List.map concl [ETA_AX;SELECT_AX;INFINITY_AX] in
 let current=List.map concl (axioms()) in
 if axioms() <> e3_callee_initial_axioms || List.length current <> 3 ||
    not(List.for_all (fun tm -> List.exists (aconv tm) permitted) current) ||
    not(List.for_all (fun tm -> List.exists (aconv tm) current) permitted)
 then failwith "C1_COMPLETION_AXIOM_CHANGE";
 print_endline ("C1_COMPLETION_LIVE_CHECKED "^name);;
c1_completion_audit_goal "C1_COMPLETION_MEMORY_SLOT_TRANSPORT" c1_completion_memory_slot_transport_statement C1_COMPLETION_MEMORY_SLOT_TRANSPORT;;
c1_completion_audit_goal "C1_COMPLETION_MEMORY_CODE_GOT_TRANSPORT" c1_completion_memory_code_got_transport_statement C1_COMPLETION_MEMORY_CODE_GOT_TRANSPORT;;
c1_completion_audit_goal "C1_PREFIX_FRAME_INCLUDED" c1_prefix_frame_included_statement C1_PREFIX_FRAME_INCLUDED;;
c1_completion_audit_goal "C1_CRYPTO_PUBLIC_FRAME_INCLUDED" c1_crypto_public_frame_included_statement C1_CRYPTO_PUBLIC_FRAME_INCLUDED;;
c1_completion_audit_goal "C1_FRAME_IDEMPOTENT" c1_frame_idempotent_statement C1_FRAME_IDEMPOTENT;;
c1_completion_audit_goal "C1_CRYPTO_FRAME_COMPOSE" c1_crypto_frame_compose_statement C1_CRYPTO_FRAME_COMPOSE;;
c1_completion_audit_goal "C1_FRAME_SAVED_PRESERVED" c1_frame_saved_preserved_statement C1_FRAME_SAVED_PRESERVED;;
c1_completion_audit_goal "C1_CRYPTO_RESULT_TRANSPORT" c1_crypto_result_transport_statement C1_CRYPTO_RESULT_TRANSPORT;;
c1_completion_audit_goal "C1_CRYPTO_RESULT_01" c1_crypto_result_01_statement C1_CRYPTO_RESULT_01;;
c1_completion_audit_goal "C1_CRYPTO_RETURN_STACK" c1_crypto_return_stack_statement C1_CRYPTO_RETURN_STACK;;
c1_completion_audit_goal "C1_INCOMING_READ_SPAN" c1_incoming_read_span_statement C1_INCOMING_READ_SPAN;;
c1_completion_audit_goal "C1_CRYPTO_COMPLETED_FACTS" c1_crypto_completed_facts_statement C1_CRYPTO_COMPLETED_FACTS;;
c1_completion_audit_goal "C1_CRYPTO_COMPLETED_RUN" c1_crypto_completed_run_statement C1_CRYPTO_COMPLETED_RUN;;
c1_completion_audit_goal "C1_CRYPTO_COMPLETED_ACCESS" c1_crypto_completed_access_statement C1_CRYPTO_COMPLETED_ACCESS;;
(* SPEC_ALL retains literal free parameters of definition declarations. *)
if hyp c1_crypto_completed <> [] || not(aconv `c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary
    (initial:x86state) a (returned:x86state) <=>
    ?entry:x86state.
      c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry /\
      bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 16))
        (word 0x21001119) p q n (read events entry) (read memory entry) entry returned` (concl(SPEC_ALL c1_crypto_completed)))
 then failwith "C1_COMPLETION_DEFINITION_MISMATCH c1_crypto_completed";;
print_endline "C1_COMPLETION_DEFINITION_CHECKED c1_crypto_completed";;
if hyp c1_crypto_public_frame <> [] || not(aconv `c1_crypto_public_frame =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` (concl(SPEC_ALL c1_crypto_public_frame)))
 then failwith "C1_COMPLETION_DEFINITION_MISMATCH c1_crypto_public_frame";;
print_endline "C1_COMPLETION_DEFINITION_CHECKED c1_crypto_public_frame";;
