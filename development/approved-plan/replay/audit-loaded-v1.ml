(* Literal expected terms copied from the preserved pre-search V3 freeze.
   Theorem conclusions and the loaded ML statement variables are never used as
   their own expected terms. This is a conditional component audit only. *)
let lw_audit_json s = "\"" ^ String.escaped s ^ "\"";;
let lw_audit_axioms_unchanged () =
 let current = axioms() in
 List.length current = List.length lw_audit_axioms_before &&
 List.for_all (fun th -> List.exists
   (fun before -> hyp th = hyp before && aconv (concl th) (concl before))
   lw_audit_axioms_before) current;;
let lw_audit_one name expected th =
 if hyp th <> [] then failwith(name ^ ": theorem hypotheses");
 if not(aconv (concl th) expected) then failwith(name ^ ": exact conclusion mismatch");
 if not(lw_audit_axioms_unchanged()) then failwith(name ^ ": new foundation axiom");
 "{\"name\":" ^ lw_audit_json name ^
 ",\"statement\":" ^ lw_audit_json(string_of_term(concl th)) ^
 ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0}";;
let lw_audit_definition name expected th =
 if hyp th <> [] then failwith(name ^ ": definition hypotheses");
 if not(aconv (snd(strip_forall(concl th))) expected) then
   failwith(name ^ ": expanded definition mismatch");
 if not(lw_audit_axioms_unchanged()) then failwith(name ^ ": new foundation axiom");;
let _ = lw_audit_definition "lw_image_domain" `lw_image_domain a <=> 0x10000000 <= a /\ a < 0x1048a000` lw_image_domain;;
let _ = lw_audit_definition "lw_image_read" `lw_image_read a <=> lw_image_domain a` lw_image_read;;
let _ = lw_audit_definition "lw_image_execute" `lw_image_execute a <=> 0x100c5000 <= a /\ a < 0x10344000` lw_image_execute;;
let _ = lw_audit_definition "lw_image_write" `lw_image_write a <=> 0x10484000 <= a /\ a < 0x1048a000` lw_image_write;;
let _ = lw_audit_definition "lw_pagecover" `lw_pagecover (p:int64) n a <=>
    ~(n = 0) /\ 4096 * (val p DIV 4096) <= a /\
    a < 4096 * ((val p + n - 1) DIV 4096 + 1)` lw_pagecover;;
let _ = lw_audit_definition "lw_overlay_domain" `lw_overlay_domain p q n a <=>
    (0x300000 <= a /\ a < 0x301000) \/
    lw_pagecover p n a \/ lw_pagecover q n a` lw_overlay_domain;;
let _ = lw_audit_definition "lw_layout" `lw_layout p q n <=>
    !a. ~(lw_image_domain a /\ lw_overlay_domain p q n a)` lw_layout;;
let _ = lw_audit_definition "lw_reference_code" `lw_reference_code (image:int64->byte) <=>
    !i. i < 95 ==> image(word(0x10241840+i)) = EL i crypto_memcmp_mc` lw_reference_code;;
let _ = lw_audit_definition "lw_memory" `lw_memory (image:int64->byte) p q n different (a:int64) =
    if 0x300008 <= val a /\ val a < 0x300010
    then word (0x400000 DIV (256 EXP (val a-0x300008)))
    else if lw_overlay_domain p q n (val a)
         then if different /\ a = q then word 255 else word 128
         else image a` lw_memory;;
let _ = lw_audit_definition "lw_state" `lw_state (image:int64->byte) (p:int64) (q:int64) n different =
    x86state_RECORD (word 0x10241840)
      (\r:(4)word. if r=word 7 then p
                  else if r=word 6 then q
                  else if r=word 2 then word n
                  else if r=word 4 then word 0x300008
                  else word 0)
      (\z:(5)word. word 0) (\k:(3)word. word 0) (word 2)
      (lw_memory image p q n different) []` lw_state;;
let _ = lw_audit_definition "lw_read" `lw_read p q n a <=> lw_image_read a \/ lw_overlay_domain p q n a` lw_read;;
let _ = lw_audit_definition "lw_execute" `lw_execute a <=> lw_image_execute a` lw_execute;;
let _ = lw_audit_definition "lw_ordinary" `lw_ordinary p q n a <=> lw_image_domain a \/ lw_overlay_domain p q n a` lw_ordinary;;
let _ = lw_audit_definition "lw_pre" `lw_pre image p q n different <=>
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (lw_read p q n) lw_execute
      (lw_ordinary p q n) (lw_state image p q n different)` lw_pre;;
let _ = lw_audit_definition "lw_reference_overlay" `lw_reference_overlay (background:int64->byte) (a:int64) =
    if 0x10241840 <= val a /\ val a < 0x10241840+95
    then EL (val a-0x10241840) crypto_memcmp_mc
    else background a` lw_reference_overlay;;
let lw_audit_rows = [
 lw_audit_one "LW_PRESERVES_IMAGE" `!image p q n different. lw_layout p q n
    ==> !a. lw_image_domain (val(a:int64))
            ==> lw_memory image p q n different a = image a` LW_PRESERVES_IMAGE;
 lw_audit_one "LW_EMPTY_FAMILY" `!image p q. lw_reference_code image ==> lw_pre image p q 0 F /\
    (!a. lw_image_domain (val(a:int64))
         ==> lw_memory image p q 0 F a = image a)` LW_EMPTY_FAMILY;
 lw_audit_one "LW_EQUAL_MISALIGNED_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200041) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200041) 17 F a = image a) /\
        (!i. i<17 ==>
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200001) (word i)) = word 128 /\
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200041) (word i)) = word 128)` LW_EQUAL_MISALIGNED_FAMILY;
 lw_audit_one "LW_UNEQUAL_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200041) 17 T /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200041) 17 T a = image a) /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T (word 0x200001) = word 128 /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T (word 0x200041) = word 255` LW_UNEQUAL_FAMILY;
 lw_audit_one "LW_IDENTICAL_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200003) (word 0x200003) 33 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200003) (word 0x200003) 33 F a = image a)` LW_IDENTICAL_FAMILY;
 lw_audit_one "LW_OVERLAP_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200001) (word 0x200002) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200001) (word 0x200002) 17 F a = image a)` LW_OVERLAP_FAMILY;
 lw_audit_one "LW_FASTPATH_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200007) (word 0x200087) 16 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200007) (word 0x200087) 16 F a = image a)` LW_FASTPATH_FAMILY;
 lw_audit_one "LW_LOW_CANONICAL_EDGE_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word (2 EXP 47-1)) (word 0x200001) 1 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word (2 EXP 47-1)) (word 0x200001) 1 F a = image a)` LW_LOW_CANONICAL_EDGE_FAMILY;
 lw_audit_one "LW_TOP_EDGE_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word (2 EXP 64-1)) (word 0x200001) 1 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word (2 EXP 64-1)) (word 0x200001) 1 F a = image a)` LW_TOP_EDGE_FAMILY;
 lw_audit_one "LW_USER_PAGE_BOUNDARY_FAMILY" `!image. lw_reference_code image
    ==> lw_pre image (word 0x200fff) (word 0x210003) 17 F /\
        (!a. lw_image_domain (val(a:int64))
          ==> lw_memory image (word 0x200fff) (word 0x210003) 17 F a = image a)` LW_USER_PAGE_BOUNDARY_FAMILY;
 lw_audit_one "LW_REFERENCE_OVERLAY" `!background. lw_reference_code (lw_reference_overlay background)` LW_REFERENCE_OVERLAY;
 lw_audit_one "LW_REFERENCE_EXISTS" `?image:int64->byte. lw_reference_code image` LW_REFERENCE_EXISTS
];;
let lw_audit_output = open_out "/output/loaded-witness-theorems.json";;
output_string lw_audit_output
 ("{\"status\":\"PASS_CONDITIONAL_IMAGE_FAMILIES\",\"full_package_witness\":false,\"full_O1_pass\":false,\"human_review\":\"PENDING\",\"expanded_definition_count\":15,\"theorems\":[" ^
  String.concat "," lw_audit_rows ^ "]}\n");;
close_out lw_audit_output;;
print_endline "LOADED_WITNESS_CONDITIONAL_AUDIT_COMPLETED";;
