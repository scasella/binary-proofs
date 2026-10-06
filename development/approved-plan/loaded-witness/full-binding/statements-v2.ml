(* Frozen before proof search. Whole declared image plus full V4 initial
   machine-state pair. Artifact acquisition and physical loader/permission
   assumptions remain explicit boundaries; human review PENDING. *)

let fb_reference_satisfies_statement =
 `!file_bytes initial_rw padding.
    fb_full_image file_bytes initial_rw padding
      (fb_reference_image file_bytes initial_rw padding)`;;

let fb_image_preservation_statement =
 `!file_bytes initial_rw padding image p q n different.
    fb_full_image file_bytes initial_rw padding image /\ lw_layout p q n
    ==> fb_full_image file_bytes initial_rw padding
          (lw_memory image p q n different)`;;

let fb_code_correspondence_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> lw_reference_code image`;;

let fb_full_image_exists_statement =
 `!file_bytes initial_rw padding.
    fb_file_code file_bytes
    ==> ?image. fb_full_image file_bytes initial_rw padding image /\
                lw_reference_code image`;;

let fb_valid_abi_statement =
 `fb_abi_initial_fields fb_initial_abi /\
    assurance_canonical48 (val(read ABI_FS_BASE fb_initial_abi)) /\
    fb_tls_page (val(read ABI_FS_BASE fb_initial_abi))`;;

let fb_pre_lift_statement =
 `!file_bytes initial_rw padding image p q n different.
    fb_full_image file_bytes initial_rw padding image /\ lw_layout p q n /\
    lw_pre image p q n different
    ==> fb_pre file_bytes initial_rw padding image p q n different`;;

let fb_empty_statement =
 `!file_bytes initial_rw padding image p q.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image p q 0 F`;;

let fb_equal_misaligned_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200041) 17 F /\
        (!i. i<17 ==>
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200001) (word i)) = word 128 /\
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200041) (word i)) = word 128)`;;

let fb_unequal_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200041) 17 T /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T
          (word 0x200001) = word 128 /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T
          (word 0x200041) = word 255`;;

let fb_identical_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200003) (word 0x200003) 33 F`;;

let fb_overlap_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200002) 17 F`;;

let fb_fastpath_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200007) (word 0x200087) 16 F`;;

let fb_low_canonical_edge_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word (2 EXP 47-1)) (word 0x200001) 1 F`;;

let fb_top_edge_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word (2 EXP 64-1)) (word 0x200001) 1 F`;;

let fb_page_boundary_statement =
 `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200fff) (word 0x210003) 17 F`;;

let fb_machine_witness_exists_statement =
 `!file_bytes initial_rw padding.
    fb_file_code file_bytes
    ==> ?image.
      fb_full_image file_bytes initial_rw padding image /\
      (!p q. fb_pre file_bytes initial_rw padding image p q 0 F) /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200001) (word 0x200041) 17 F /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200001) (word 0x200041) 17 T /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200003) (word 0x200003) 33 F /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200001) (word 0x200002) 17 F /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200007) (word 0x200087) 16 F /\
      fb_pre file_bytes initial_rw padding image
        (word (2 EXP 47-1)) (word 0x200001) 1 F /\
      fb_pre file_bytes initial_rw padding image
        (word (2 EXP 64-1)) (word 0x200001) 1 F /\
      fb_pre file_bytes initial_rw padding image
        (word 0x200fff) (word 0x210003) 17 F`;;
