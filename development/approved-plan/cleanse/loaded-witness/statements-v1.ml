(* Frozen literal initial-domain targets; no output property or callee correctness. *)
let clw_reference_satisfies_statement =
 `!file_bytes initial_rw padding. fb_full_image file_bytes initial_rw padding (fb_reference_image file_bytes initial_rw padding)`;;

let clw_code_correspondence_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_reference_code image`;;

let clw_initial_image_binding_statement =
 `!file_bytes initial_rw padding image p n high_first. fb_full_image file_bytes initial_rw padding image /\ clw_layout p n ==> fb_full_image file_bytes initial_rw padding (clw_memory image p n high_first)`;;

let clw_valid_abi_statement =
 `fb_abi_initial_fields fb_initial_abi /\ assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi)) /\ fb_tls_page(val(read ABI_FS_BASE fb_initial_abi))`;;

let clw_full_pre_lift_statement =
 `!file_bytes initial_rw padding image p n high_first. fb_full_image file_bytes initial_rw padding image /\ clw_layout p n /\ clw_scalar_pre image p n high_first ==> clw_full_pre file_bytes initial_rw padding image p n high_first`;;

let clw_empty_statement =
 `!file_bytes initial_rw padding image p. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image p 0 F /\ (!a. ~lw_pagecover p 0 a)`;;

let clw_empty_no_permissions_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word(2 EXP 64-1)) 0 F /\ ~clw_read (word(2 EXP 64-1)) 0 (2 EXP 64-1) /\ ~clw_write (word(2 EXP 64-1)) 0 (2 EXP 64-1) /\ ~clw_ordinary (word(2 EXP 64-1)) 0 (2 EXP 64-1)`;;

let clw_byte_one_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200001) 1 F /\ clw_memory image (word 0x200001) 1 F (word 0x200001)=word 128`;;

let clw_byte_seven_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200003) 7 T /\ clw_memory image (word 0x200003) 7 T (word 0x200003)=word 255`;;

let clw_bulk_aligned_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200000) 24 F /\ clw_memory image (word 0x200000) 24 F (word 0x200000)=word 128`;;

let clw_misaligned_bulk_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200001) 17 F /\ clw_memory image (word 0x200001) 17 F (word 0x200001)=word 128`;;

let clw_misaligned_tail_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200003) 33 T /\ clw_memory image (word 0x200003) 33 T (word 0x200003)=word 255`;;

let clw_user_page_boundary_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200fff) 17 F /\ clw_memory image (word 0x200fff) 17 F (word 0x200fff)=word 128`;;

let clw_low_canonical_edge_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 47-1)) 1 F /\ clw_memory image (word (2 EXP 47-1)) 1 F (word (2 EXP 47-1))=word 128`;;

let clw_top_endpoint_wrap_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-1)) 1 T /\ clw_memory image (word (2 EXP 64-1)) 1 T (word (2 EXP 64-1))=word 255`;;

let clw_top_qword_endpoint_wrap_statement =
 `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-8)) 8 F /\ clw_memory image (word (2 EXP 64-8)) 8 F (word (2 EXP 64-8))=word 128`;;

let clw_machine_witness_exists_statement =
 `!file_bytes initial_rw padding. clw_file_code file_bytes ==> ?image. fb_full_image file_bytes initial_rw padding image /\ (!p. clw_full_pre file_bytes initial_rw padding image p 0 F) /\ clw_full_pre file_bytes initial_rw padding image (word 0x200001) 1 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200003) 7 T /\ clw_full_pre file_bytes initial_rw padding image (word 0x200000) 24 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200001) 17 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200003) 33 T /\ clw_full_pre file_bytes initial_rw padding image (word 0x200fff) 17 F /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 47-1)) 1 F /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-1)) 1 T /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-8)) 8 F`;;

