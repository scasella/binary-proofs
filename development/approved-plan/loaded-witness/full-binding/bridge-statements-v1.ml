(* Separate additive statement freeze before proof search. Connect the
   already-frozen complete machine Pre to the file-slice premise required by
   the exact public-entry interface. No new acquisition assumption is added. *)

let fb_pre_file_code_statement =
 `!file_bytes initial_rw padding image p q n different.
    fb_pre file_bytes initial_rw padding image p q n different
    ==> fb_file_code file_bytes`;;
