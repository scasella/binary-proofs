(* Checks the constructed theorem objects against the frozen literal targets.
   Hypotheses, free variables and global axioms are audited independently. *)
let c1_application_audit_goal name expected actual =
 if hyp actual <> [] then failwith ("C1_APP_NONEMPTY_HYPOTHESES "^name);
 if frees(concl actual) <> [] then failwith ("C1_APP_FREE_VARIABLES "^name);
 if not(aconv expected (concl actual)) then failwith ("C1_APP_LITERAL_MISMATCH "^name);
 let permitted=List.map concl [ETA_AX;SELECT_AX;INFINITY_AX] in
 let current=List.map concl (axioms()) in
 if axioms() <> e3_callee_initial_axioms || List.length current <> 3 ||
    not(List.for_all (fun tm -> List.exists (aconv tm) permitted) current) ||
    not(List.for_all (fun tm -> List.exists (aconv tm) current) permitted)
 then failwith "C1_APP_AXIOM_CHANGE";
 print_endline ("C1_APP_LIVE_CHECKED "^name);;
c1_application_audit_goal "C1_APP_EVENT_POLICY_MONO"
 c1_app_event_policy_mono_statement C1_APP_EVENT_POLICY_MONO;;
c1_application_audit_goal "C1_APP_ALL_POLICY_MONO"
 c1_app_all_policy_mono_statement C1_APP_ALL_POLICY_MONO;;
c1_application_audit_goal "C1_APP_STEP_POLICY_MONO"
 c1_app_step_policy_mono_statement C1_APP_STEP_POLICY_MONO;;
c1_application_audit_goal "C1_CRYPTO_READ_INCLUSION"
 c1_crypto_read_inclusion_statement C1_CRYPTO_READ_INCLUSION;;
c1_application_audit_goal "C1_CRYPTO_WRITE_INCLUSION"
 c1_crypto_write_inclusion_statement C1_CRYPTO_WRITE_INCLUSION;;
c1_application_audit_goal "C1_CRYPTO_FETCH_INCLUSION"
 c1_crypto_fetch_inclusion_statement C1_CRYPTO_FETCH_INCLUSION;;
c1_application_audit_goal "C1_CRYPTO_INTERFACE_APPLICATION"
 c1_crypto_interface_application_statement C1_CRYPTO_INTERFACE_APPLICATION;;
c1_application_audit_goal "C1_CRYPTO_POLICY_WIDEN"
 c1_crypto_policy_widen_statement C1_CRYPTO_POLICY_WIDEN;;
c1_application_audit_goal "C1_CRYPTO_SEGMENT_APPLICATION"
 c1_crypto_segment_application_statement C1_CRYPTO_SEGMENT_APPLICATION;;
