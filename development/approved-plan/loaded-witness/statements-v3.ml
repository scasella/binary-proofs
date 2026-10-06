(* Literal frozen family statements, independent of later proof recipes.
   Conditional reference-image families, not an acquired full-image witness. *)
let lw_preserves_image_statement =
 `!image p q n different. lw_layout p q n
    ==> !a. lw_image_domain (val(a:int64))
            ==> lw_memory image p q n different a = image a`;;

let lw_empty_statement =
 `!image p q. lw_reference_code image ==> lw_pre image p q 0 F /\
    (!a. lw_image_domain (val(a:int64))
         ==> lw_memory image p q 0 F a = image a)`;;

let lw_equal_misaligned_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200041) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200041) 17 F a = image a) /\
        (!i. i<17 ==>
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200001) (word i)) = word 128 /\
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200041) (word i)) = word 128)`;;

let lw_unequal_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200041) 17 T /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200041) 17 T a = image a) /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T (word 0x200001) = word 128 /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T (word 0x200041) = word 255`;;

let lw_identical_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200003) (word 0x200003) 33 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200003) (word 0x200003) 33 F a = image a)`;;

let lw_overlap_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200002) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200002) 17 F a = image a)`;;

let lw_fastpath_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200007) (word 0x200087) 16 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200007) (word 0x200087) 16 F a = image a)`;;

let lw_low_canonical_edge_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word (2 EXP 47-1)) (word 0x200001) 1 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word (2 EXP 47-1)) (word 0x200001) 1 F a = image a)`;;

let lw_top_edge_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word (2 EXP 64-1)) (word 0x200001) 1 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word (2 EXP 64-1)) (word 0x200001) 1 F a = image a)`;;

(* Ordinary low user-address page-boundary case, separately from abstract
   maximal canonical endpoints not realizable as baseline CPL3 mappings. *)
let lw_page_boundary_statement =
 `!image. lw_reference_code image
    ==> lw_pre image (word 0x200fff) (word 0x210003) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200fff) (word 0x210003) 17 F a = image a)`;;

let lw_reference_overlay_statement =
 `!background. lw_reference_code (lw_reference_overlay background)`;;

let lw_reference_exists_statement =
 `?image:int64->byte. lw_reference_code image`;;
