(* Exact expected source terms retained independently of proof results. *)
let fb_audit_json s = "\"" ^ String.escaped s ^ "\"";;
let fb_audit_axioms_unchanged () =
 let current = axioms() in
 List.length current = List.length fb_audit_axioms_before &&
 List.for_all (fun th -> List.exists
   (fun before -> hyp th = hyp before && aconv (concl th) (concl before))
   fb_audit_axioms_before) current;;
let fb_audit_one name expected th =
 if hyp th <> [] then failwith(name ^ ": theorem hypotheses");
 if not(aconv (concl th) expected) then failwith(name ^ ": exact conclusion mismatch");
 if not(fb_audit_axioms_unchanged()) then failwith(name ^ ": new foundation axiom");
 "{\"name\":" ^ fb_audit_json name ^
 ",\"statement\":" ^ fb_audit_json(string_of_term(concl th)) ^
 ",\"hypothesis_count\":0,\"conclusion_matches_expected\":true,\"new_axioms\":0}";;
let fb_audit_definition name expected th =
 if hyp th <> [] then failwith(name ^ ": definition hypotheses");
 if not(aconv (snd(strip_forall(concl th))) expected) then
   failwith(name ^ ": expanded definition mismatch");
 if not(fb_audit_axioms_unchanged()) then failwith(name ^ ": new foundation axiom");;
let _ = fb_audit_definition "fb_abi_initial_fields" `fb_abi_initial_fields (a:abi_omitted_state) <=>
    read ABI_X87_CW a = word 0x37f /\
    read ABI_X87_SW a = word 0 /\
    read ABI_X87_TAG a = word 0xffff /\
    read ABI_X87_FOP a = word 0 /\
    read ABI_X87_IP a = word 0 /\
    read ABI_X87_CS a = word 0 /\
    read ABI_X87_DP a = word 0 /\
    read ABI_X87_DS a = word 0 /\
    (!r:(3)word. read ABI_X87_REGS a r = word 0) /\
    read ABI_MXCSR a = word 0x1f80 /\
    read ABI_FS_SELECTOR a = word 0 /\
    read ABI_FS_BASE a = word 0x500000 /\
    read ABI_GS_SELECTOR a = word 0 /\
    read ABI_GS_BASE a = word 0` fb_abi_initial_fields;;
let _ = fb_audit_definition "fb_file_code" `fb_file_code (file_bytes:num->byte) <=>
    !i. i<95 ==> file_bytes(0x241840+i) = EL i crypto_memcmp_mc` fb_file_code;;
let _ = fb_audit_definition "fb_full_image" `fb_full_image file_bytes initial_rw padding (image:int64->byte) <=>
    !a. lw_image_domain (val(a:int64))
        ==> image a = fb_reference_image file_bytes initial_rw padding a` fb_full_image;;
let _ = fb_audit_definition "fb_immutable" `fb_immutable a <=>
    (0x10000000 <= a /\ a < 0x100c4bd0) \/
    (0x100c5000 <= a /\ a < 0x103434c9) \/
    (0x10344000 <= a /\ a < 0x10421a40)` fb_immutable;;
let _ = fb_audit_definition "fb_initial_abi" `fb_initial_abi = abi_omitted_state_RECORD
    (word 0x37f) (word 0) (word 0xffff) (word 0)
    (word 0) (word 0) (word 0) (word 0)
    (\r:(3)word. word 0) (word 0x1f80)
    (word 0) (word 0x500000) (word 0) (word 0)` fb_initial_abi;;
let _ = fb_audit_definition "fb_initialized_rw" `fb_initialized_rw a <=> 0x10422e50 <= a /\ a < 0x104895b0` fb_initialized_rw;;
let _ = fb_audit_definition "fb_machine" `fb_machine image p q n different =
    (lw_state image p q n different,fb_initial_abi)` fb_machine;;
let _ = fb_audit_definition "fb_ordinary" `fb_ordinary p q n a <=> lw_ordinary p q n a \/ fb_tls_page a` fb_ordinary;;
let _ = fb_audit_definition "fb_pre" `fb_pre file_bytes initial_rw padding image p q n different <=>
    fb_full_image file_bytes initial_rw padding
      (read memory (FST(fb_machine image p q n different))) /\
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (fb_read p q n) lw_execute
      (fb_ordinary p q n) (FST(fb_machine image p q n different)) /\
    fb_abi_initial_fields (SND(fb_machine image p q n different)) /\
    (!a. fb_tls_page a ==> fb_read p q n a /\ fb_ordinary p q n a) /\
    assurance_canonical48 (val(read ABI_FS_BASE
      (SND(fb_machine image p q n different))))` fb_pre;;
let _ = fb_audit_definition "fb_read" `fb_read p q n a <=> lw_read p q n a \/ fb_tls_page a` fb_read;;
let _ = fb_audit_definition "fb_reference_image" `fb_reference_image (file_bytes:num->byte) (initial_rw:int64->byte)
                     (padding:int64->byte) (a:int64) =
    if fb_immutable (val a) then file_bytes (val a-0x10000000)
    else if fb_initialized_rw (val a) then initial_rw a
    else padding a` fb_reference_image;;
let _ = fb_audit_definition "fb_tls_page" `fb_tls_page a <=> 0x500000 <= a /\ a < 0x501000` fb_tls_page;;
let fb_audit_rows = [
 fb_audit_one "FB_CODE_CORRESPONDENCE" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> lw_reference_code image` FB_CODE_CORRESPONDENCE;
 fb_audit_one "FB_EMPTY_FAMILY" `!file_bytes initial_rw padding image p q.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image p q 0 F` FB_EMPTY_FAMILY;
 fb_audit_one "FB_EQUAL_MISALIGNED_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200041) 17 F /\
        (!i. i<17 ==>
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200001) (word i)) = word 128 /\
          lw_memory image (word 0x200001) (word 0x200041) 17 F
             (word_add (word 0x200041) (word i)) = word 128)` FB_EQUAL_MISALIGNED_FAMILY;
 fb_audit_one "FB_FASTPATH_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200007) (word 0x200087) 16 F` FB_FASTPATH_FAMILY;
 fb_audit_one "FB_FULL_IMAGE_EXISTS" `!file_bytes initial_rw padding.
    fb_file_code file_bytes
    ==> ?image. fb_full_image file_bytes initial_rw padding image /\
                lw_reference_code image` FB_FULL_IMAGE_EXISTS;
 fb_audit_one "FB_IDENTICAL_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200003) (word 0x200003) 33 F` FB_IDENTICAL_FAMILY;
 fb_audit_one "FB_IMAGE_PRESERVATION" `!file_bytes initial_rw padding image p q n different.
    fb_full_image file_bytes initial_rw padding image /\ lw_layout p q n
    ==> fb_full_image file_bytes initial_rw padding
          (lw_memory image p q n different)` FB_IMAGE_PRESERVATION;
 fb_audit_one "FB_LOW_CANONICAL_EDGE_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word (2 EXP 47-1)) (word 0x200001) 1 F` FB_LOW_CANONICAL_EDGE_FAMILY;
 fb_audit_one "FB_MACHINE_WITNESS_EXISTS" `!file_bytes initial_rw padding.
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
        (word 0x200fff) (word 0x210003) 17 F` FB_MACHINE_WITNESS_EXISTS;
 fb_audit_one "FB_OVERLAP_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200002) 17 F` FB_OVERLAP_FAMILY;
 fb_audit_one "FB_USER_PAGE_BOUNDARY_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200fff) (word 0x210003) 17 F` FB_USER_PAGE_BOUNDARY_FAMILY;
 fb_audit_one "FB_PRE_LIFT" `!file_bytes initial_rw padding image p q n different.
    fb_full_image file_bytes initial_rw padding image /\ lw_layout p q n /\
    lw_pre image p q n different
    ==> fb_pre file_bytes initial_rw padding image p q n different` FB_PRE_LIFT;
 fb_audit_one "FB_REFERENCE_SATISFIES" `!file_bytes initial_rw padding.
    fb_full_image file_bytes initial_rw padding
      (fb_reference_image file_bytes initial_rw padding)` FB_REFERENCE_SATISFIES;
 fb_audit_one "FB_TOP_EDGE_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word (2 EXP 64-1)) (word 0x200001) 1 F` FB_TOP_EDGE_FAMILY;
 fb_audit_one "FB_UNEQUAL_FAMILY" `!file_bytes initial_rw padding image.
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image
    ==> fb_pre file_bytes initial_rw padding image
          (word 0x200001) (word 0x200041) 17 T /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T
          (word 0x200001) = word 128 /\
        lw_memory image (word 0x200001) (word 0x200041) 17 T
          (word 0x200041) = word 255` FB_UNEQUAL_FAMILY;
 fb_audit_one "FB_VALID_ABI" `fb_abi_initial_fields fb_initial_abi /\
    assurance_canonical48 (val(read ABI_FS_BASE fb_initial_abi)) /\
    fb_tls_page (val(read ABI_FS_BASE fb_initial_abi))` FB_VALID_ABI
];;
print_endline ("FULL_BINDING_EXACT_AUDIT_COMPLETED " ^ string_of_int(List.length fb_audit_rows));;
