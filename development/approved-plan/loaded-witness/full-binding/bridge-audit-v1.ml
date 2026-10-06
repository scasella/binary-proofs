(* Literal expected term from the preserved bridge pre-search freeze. *)
let fb_audit_rows = fb_audit_rows @ [
 fb_audit_one "FB_PRE_FILE_CODE" `!file_bytes initial_rw padding image p q n different.
    fb_pre file_bytes initial_rw padding image p q n different
    ==> fb_file_code file_bytes` FB_PRE_FILE_CODE];;
print_endline "FULL_BINDING_BRIDGE_EXACT_AUDIT_COMPLETED";;
