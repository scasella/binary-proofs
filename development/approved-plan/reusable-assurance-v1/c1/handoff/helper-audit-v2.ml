(* Retains audit v1 compile failure; explicit standard List functions. *)
(* Literal and closure audit only; no logical declarations or new axioms. *)
let c1_handoff_audit_goal name expected actual =
 if hyp actual <> [] then failwith ("C1_NONEMPTY_HYPOTHESES "^name);
 if frees(concl actual) <> [] then failwith ("C1_FREE_VARIABLES "^name);
 if not(aconv expected (concl actual)) then failwith ("C1_LITERAL_MISMATCH "^name);
 let permitted=List.map concl [ETA_AX;SELECT_AX;INFINITY_AX] in
 let current=List.map concl (axioms()) in
 if axioms() <> e3_callee_initial_axioms || List.length current <> 3 ||
    not(List.for_all (fun tm -> List.exists (aconv tm) permitted) current) ||
    not(List.for_all (fun tm -> List.exists (aconv tm) current) permitted)
 then failwith "C1_AXIOM_CHANGE";
 print_endline ("C1_LIVE_CHECKED "^name);;
c1_handoff_audit_goal "C1_STACK_SUB16_VALUE" c1_stack_sub16_value_statement C1_STACK_SUB16_VALUE;;
c1_handoff_audit_goal "C1_STACK_ALIGNMENT" c1_stack_alignment_statement C1_STACK_ALIGNMENT;;
c1_handoff_audit_goal "C1_SPAN_POINT" c1_span_point_statement C1_SPAN_POINT;;
c1_handoff_audit_goal "C1_SPAN_WORD_ADD_REGION" c1_span_word_add_region_statement C1_SPAN_WORD_ADD_REGION;;
c1_handoff_audit_goal "C1_REGION_NONOVERLAPPING" c1_region_nonoverlapping_statement C1_REGION_NONOVERLAPPING;;
c1_handoff_audit_goal "C1_NONOVERLAPPING_REGION_DISJOINT" c1_nonoverlapping_region_disjoint_statement C1_NONOVERLAPPING_REGION_DISJOINT;;
c1_handoff_audit_goal "C1_WRITABLE_READONLY_NONOVERLAPPING" c1_writable_readonly_nonoverlapping_statement C1_WRITABLE_READONLY_NONOVERLAPPING;;
c1_handoff_audit_goal "C1_LIBRARY_REBIND" c1_library_rebind_statement C1_LIBRARY_REBIND;;
c1_handoff_audit_goal "C1_LIBRARY_IMMUTABLE_READONLY" c1_library_immutable_readonly_statement C1_LIBRARY_IMMUTABLE_READONLY;;
c1_handoff_audit_goal "C1_CALLER_READONLY_REGION" c1_caller_readonly_region_statement C1_CALLER_READONLY_REGION;;
c1_handoff_audit_goal "C1_PLT_READONLY_REGION" c1_plt_readonly_region_statement C1_PLT_READONLY_REGION;;
c1_handoff_audit_goal "C1_GOT_READONLY_REGION" c1_got_readonly_region_statement C1_GOT_READONLY_REGION;;
c1_handoff_audit_goal "C1_CRYPTO_READONLY_REGION" c1_crypto_readonly_region_statement C1_CRYPTO_READONLY_REGION;;
c1_handoff_audit_goal "C1_SLOT_READ_SPAN" c1_slot_read_span_statement C1_SLOT_READ_SPAN;;
c1_handoff_audit_goal "C1_SLOT_WRITE_SPAN" c1_slot_write_span_statement C1_SLOT_WRITE_SPAN;;
c1_handoff_audit_goal "C1_CALLER_FETCH_SPAN" c1_caller_fetch_span_statement C1_CALLER_FETCH_SPAN;;
c1_handoff_audit_goal "C1_PLT_FETCH_SPAN" c1_plt_fetch_span_statement C1_PLT_FETCH_SPAN;;
c1_handoff_audit_goal "C1_GOT_READ_SPAN" c1_got_read_span_statement C1_GOT_READ_SPAN;;
c1_handoff_audit_goal "C1_LIBRARY_SLOT_DISJOINT" c1_library_slot_disjoint_statement C1_LIBRARY_SLOT_DISJOINT;;
c1_handoff_audit_goal "C1_SLOT_BYTE_NONOVERLAPPING" c1_slot_byte_nonoverlapping_statement C1_SLOT_BYTE_NONOVERLAPPING;;
c1_handoff_audit_goal "C1_PREFIX_FRAME_BYTE" c1_prefix_frame_byte_statement C1_PREFIX_FRAME_BYTE;;
c1_handoff_audit_goal "C1_PREFIX_FRAME_INCOMING_SLOT" c1_prefix_frame_incoming_slot_statement C1_PREFIX_FRAME_INCOMING_SLOT;;
c1_handoff_audit_goal "C1_UNCHANGED_BUFFER" c1_unchanged_buffer_statement C1_UNCHANGED_BUFFER;;
