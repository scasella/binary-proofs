(* Independent literal expected terms, compared against live theorem objects. *)
let clw_audit_json s="\"" ^ String.escaped s ^ "\"";;
let clw_axioms_unchanged() =
 let current=axioms() in
 List.length current=List.length clw_initial_axioms &&
 List.for_all(fun th->List.exists(fun before->hyp th=hyp before &&
   aconv(concl th)(concl before)) clw_initial_axioms) current;;
let clw_audit_one name expected th =
 if hyp th<>[] then failwith(name ^ ": hypotheses");
 if not(aconv(concl th)expected) then failwith(name ^ ": conclusion mismatch");
 if not(clw_axioms_unchanged()) then failwith(name ^ ": new axioms");
 "{\"name\":" ^ clw_audit_json name ^
 ",\"hypothesis_count\":0,\"new_axioms\":0,\"conclusion_matches_expected\":true,\"statement\":" ^
 clw_audit_json(string_of_term(concl th)) ^ "}";;
let clw_audit_definition name expected th =
 if hyp th<>[] then failwith(name ^ ": definition hypotheses");
 if not(aconv(snd(strip_forall(concl th)))expected) then
   failwith(name ^ ": expanded definition mismatch");
 if not(clw_axioms_unchanged()) then failwith(name ^ ": new axioms");;
let _=clw_audit_definition "clw_file_code" `clw_file_code (file_bytes:num->byte) <=>
    !i. i<97 ==> file_bytes(0x2417d0+i)=EL i openssl_cleanse_mc` clw_file_code;;
let _=clw_audit_definition "clw_reference_code" `clw_reference_code (image:int64->byte) <=>
    !i. i<97 ==> image(word(0x102417d0+i))=EL i openssl_cleanse_mc` clw_reference_code;;
let _=clw_audit_definition "clw_layout" `clw_layout p n <=> lw_layout p p n` clw_layout;;
let _=clw_audit_definition "clw_memory" `clw_memory image p n high_first = lw_memory image p p n high_first` clw_memory;;
let _=clw_audit_definition "clw_state" `clw_state (image:int64->byte) (p:int64) n high_first =
    x86state_RECORD (word 0x102417d0)
      (\r:(4)word. if r=word 7 then p
                  else if r=word 6 then word n
                  else if r=word 4 then word 0x300008
                  else word 0)
      (\z:(5)word. word 0) (\k:(3)word. word 0) (word 2)
      (clw_memory image p n high_first) []` clw_state;;
let _=clw_audit_definition "clw_read" `clw_read p n a <=> fb_read p p n a` clw_read;;
let _=clw_audit_definition "clw_write" `clw_write p n a <=> lw_image_write a \/ lw_pagecover p n a` clw_write;;
let _=clw_audit_definition "clw_ordinary" `clw_ordinary p n a <=> fb_ordinary p p n a` clw_ordinary;;
let _=clw_audit_definition "clw_scalar_pre" `clw_scalar_pre image p n high_first <=>
    bp_e2_cleanse_pre 0x102417d0 (word 0x300008) (word 0x400000) p n
      (clw_memory image p n high_first) (clw_read p n) (clw_write p n)
      lw_execute (clw_ordinary p n) (clw_state image p n high_first)` clw_scalar_pre;;
let _=clw_audit_definition "clw_machine" `clw_machine image p n high_first =
    (clw_state image p n high_first,fb_initial_abi)` clw_machine;;
let _=clw_audit_definition "clw_full_pre" `clw_full_pre file_bytes initial_rw padding image p n high_first <=>
    fb_full_image file_bytes initial_rw padding
      (read memory (FST(clw_machine image p n high_first))) /\
    bp_e2_cleanse_pre 0x102417d0 (word 0x300008) (word 0x400000) p n
      (clw_memory image p n high_first) (clw_read p n) (clw_write p n)
      lw_execute (clw_ordinary p n) (FST(clw_machine image p n high_first)) /\
    fb_abi_initial_fields (SND(clw_machine image p n high_first)) /\
    (!a. fb_tls_page a ==> clw_read p n a /\ clw_ordinary p n a) /\
    assurance_canonical48 (val(read ABI_FS_BASE
      (SND(clw_machine image p n high_first)))) /\
    (!a. lw_image_domain a ==> clw_read p n a /\ clw_ordinary p n a /\
          (lw_execute a <=> lw_image_execute a) /\
          (clw_write p n a <=> lw_image_write a))` clw_full_pre;;
let _=clw_audit_definition "lw_image_domain" `lw_image_domain a <=> 0x10000000 <= a /\ a < 0x1048a000` lw_image_domain;;
let _=clw_audit_definition "lw_image_read" `lw_image_read a <=> lw_image_domain a` lw_image_read;;
let _=clw_audit_definition "lw_image_execute" `lw_image_execute a <=> 0x100c5000 <= a /\ a < 0x10344000` lw_image_execute;;
let _=clw_audit_definition "lw_image_write" `lw_image_write a <=> 0x10484000 <= a /\ a < 0x1048a000` lw_image_write;;
let _=clw_audit_definition "lw_pagecover" `lw_pagecover (p:int64) n a <=>
    ~(n = 0) /\ 4096 * (val p DIV 4096) <= a /\
    a < 4096 * ((val p + n - 1) DIV 4096 + 1)` lw_pagecover;;
let _=clw_audit_definition "lw_overlay_domain" `lw_overlay_domain p q n a <=>
    (0x300000 <= a /\ a < 0x301000) \/
    lw_pagecover p n a \/ lw_pagecover q n a` lw_overlay_domain;;
let _=clw_audit_definition "lw_layout" `lw_layout p q n <=>
    !a. ~(lw_image_domain a /\ lw_overlay_domain p q n a)` lw_layout;;
let _=clw_audit_definition "lw_reference_code" `lw_reference_code (image:int64->byte) <=>
    !i. i < 95 ==> image(word(0x10241840+i)) = EL i crypto_memcmp_mc` lw_reference_code;;
let _=clw_audit_definition "lw_memory" `lw_memory (image:int64->byte) p q n different (a:int64) =
    if 0x300008 <= val a /\ val a < 0x300010
    then word (0x400000 DIV (256 EXP (val a-0x300008)))
    else if lw_overlay_domain p q n (val a)
         then if different /\ a = q then word 255 else word 128
         else image a` lw_memory;;
let _=clw_audit_definition "lw_state" `lw_state (image:int64->byte) (p:int64) (q:int64) n different =
    x86state_RECORD (word 0x10241840)
      (\r:(4)word. if r=word 7 then p
                  else if r=word 6 then q
                  else if r=word 2 then word n
                  else if r=word 4 then word 0x300008
                  else word 0)
      (\z:(5)word. word 0) (\k:(3)word. word 0) (word 2)
      (lw_memory image p q n different) []` lw_state;;
let _=clw_audit_definition "lw_read" `lw_read p q n a <=> lw_image_read a \/ lw_overlay_domain p q n a` lw_read;;
let _=clw_audit_definition "lw_execute" `lw_execute a <=> lw_image_execute a` lw_execute;;
let _=clw_audit_definition "lw_ordinary" `lw_ordinary p q n a <=> lw_image_domain a \/ lw_overlay_domain p q n a` lw_ordinary;;
let _=clw_audit_definition "lw_pre" `lw_pre image p q n different <=>
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (lw_read p q n) lw_execute
      (lw_ordinary p q n) (lw_state image p q n different)` lw_pre;;
let _=clw_audit_definition "fb_immutable" `fb_immutable a <=>
    (0x10000000 <= a /\ a < 0x100c4bd0) \/
    (0x100c5000 <= a /\ a < 0x103434c9) \/
    (0x10344000 <= a /\ a < 0x10421a40)` fb_immutable;;
let _=clw_audit_definition "fb_initialized_rw" `fb_initialized_rw a <=> 0x10422e50 <= a /\ a < 0x104895b0` fb_initialized_rw;;
let _=clw_audit_definition "fb_reference_image" `fb_reference_image (file_bytes:num->byte) (initial_rw:int64->byte)
                     (padding:int64->byte) (a:int64) =
    if fb_immutable (val a) then file_bytes (val a-0x10000000)
    else if fb_initialized_rw (val a) then initial_rw a
    else padding a` fb_reference_image;;
let _=clw_audit_definition "fb_full_image" `fb_full_image file_bytes initial_rw padding (image:int64->byte) <=>
    !a. lw_image_domain (val(a:int64))
        ==> image a = fb_reference_image file_bytes initial_rw padding a` fb_full_image;;
let _=clw_audit_definition "fb_file_code" `fb_file_code (file_bytes:num->byte) <=>
    !i. i<95 ==> file_bytes(0x241840+i) = EL i crypto_memcmp_mc` fb_file_code;;
let _=clw_audit_definition "fb_tls_page" `fb_tls_page a <=> 0x500000 <= a /\ a < 0x501000` fb_tls_page;;
let _=clw_audit_definition "fb_read" `fb_read p q n a <=> lw_read p q n a \/ fb_tls_page a` fb_read;;
let _=clw_audit_definition "fb_ordinary" `fb_ordinary p q n a <=> lw_ordinary p q n a \/ fb_tls_page a` fb_ordinary;;
let _=clw_audit_definition "fb_initial_abi" `fb_initial_abi = abi_omitted_state_RECORD
    (word 0x37f) (word 0) (word 0xffff) (word 0)
    (word 0) (word 0) (word 0) (word 0)
    (\r:(3)word. word 0) (word 0x1f80)
    (word 0) (word 0x500000) (word 0) (word 0)` fb_initial_abi;;
let _=clw_audit_definition "fb_abi_initial_fields" `fb_abi_initial_fields (a:abi_omitted_state) <=>
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
let _=clw_audit_definition "fb_machine" `fb_machine image p q n different =
    (lw_state image p q n different,fb_initial_abi)` fb_machine;;
let _=clw_audit_definition "fb_pre" `fb_pre file_bytes initial_rw padding image p q n different <=>
    fb_full_image file_bytes initial_rw padding
      (read memory (FST(fb_machine image p q n different))) /\
    bp_e2_crypto_pre 0x10241840 (word 0x300008) (word 0x400000)
      p q n (lw_memory image p q n different) (fb_read p q n) lw_execute
      (fb_ordinary p q n) (FST(fb_machine image p q n different)) /\
    fb_abi_initial_fields (SND(fb_machine image p q n different)) /\
    (!a. fb_tls_page a ==> fb_read p q n a /\ fb_ordinary p q n a) /\
    assurance_canonical48 (val(read ABI_FS_BASE
      (SND(fb_machine image p q n different))))` fb_pre;;
let _=clw_audit_definition "assurance_canonical48" `assurance_canonical48 a <=>
    a < 2 EXP 64 /\ (a < 2 EXP 47 \/ 2 EXP 64 - 2 EXP 47 <= a)` assurance_canonical48;;
let _=clw_audit_definition "assurance_region" `assurance_region (p:int64) n a <=> val p <= a /\ a < val p+n` assurance_region;;
let _=clw_audit_definition "assurance_span_ok" `assurance_span_ok perm a width <=>
    a+width <= 2 EXP 64 /\
    !j. j < width ==> assurance_canonical48 (a+j) /\ perm(a+j)` assurance_span_ok;;
let _=clw_audit_definition "bp_e2_cleanse_pre" `bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary (s:x86state) <=>
    n<2 EXP 64 /\ pc+97<=2 EXP 64 /\
    bytes_loaded s (word pc) openssl_cleanse_mc /\
    read RIP s=word pc /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;word n] s /\ read memory s=m /\
    val(stackpointer:int64) MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word pc) /\
    read DF s=F /\ ~bit 18(read rflags s) /\
    assurance_span_ok (\a. xp a /\ ordinary a) pc 97 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val(p:int64)) n /\
    (!a. ~(assurance_region p n a /\ assurance_region (word pc) 97 a)) /\
    (!a. ~(assurance_region p n a /\ assurance_region stackpointer 8 a))` bp_e2_cleanse_pre;;
let clw_audit_rows=[
 clw_audit_one "CLW_REFERENCE_SATISFIES" `!file_bytes initial_rw padding. fb_full_image file_bytes initial_rw padding (fb_reference_image file_bytes initial_rw padding)` CLW_REFERENCE_SATISFIES;
 clw_audit_one "CLW_CODE_CORRESPONDENCE" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_reference_code image` CLW_CODE_CORRESPONDENCE;
 clw_audit_one "CLW_INITIAL_IMAGE_BINDING" `!file_bytes initial_rw padding image p n high_first. fb_full_image file_bytes initial_rw padding image /\ clw_layout p n ==> fb_full_image file_bytes initial_rw padding (clw_memory image p n high_first)` CLW_INITIAL_IMAGE_BINDING;
 clw_audit_one "CLW_VALID_ABI" `fb_abi_initial_fields fb_initial_abi /\ assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi)) /\ fb_tls_page(val(read ABI_FS_BASE fb_initial_abi))` CLW_VALID_ABI;
 clw_audit_one "CLW_FULL_PRE_LIFT" `!file_bytes initial_rw padding image p n high_first. fb_full_image file_bytes initial_rw padding image /\ clw_layout p n /\ clw_scalar_pre image p n high_first ==> clw_full_pre file_bytes initial_rw padding image p n high_first` CLW_FULL_PRE_LIFT;
 clw_audit_one "CLW_EMPTY_FAMILY" `!file_bytes initial_rw padding image p. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image p 0 F /\ (!a. ~lw_pagecover p 0 a)` CLW_EMPTY_FAMILY;
 clw_audit_one "CLW_EMPTY_NO_DESTINATION_PERMISSIONS" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word(2 EXP 64-1)) 0 F /\ ~clw_read (word(2 EXP 64-1)) 0 (2 EXP 64-1) /\ ~clw_write (word(2 EXP 64-1)) 0 (2 EXP 64-1) /\ ~clw_ordinary (word(2 EXP 64-1)) 0 (2 EXP 64-1)` CLW_EMPTY_NO_DESTINATION_PERMISSIONS;
 clw_audit_one "CLW_BYTE_ONE_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200001) 1 F /\ clw_memory image (word 0x200001) 1 F (word 0x200001)=word 128` CLW_BYTE_ONE_FAMILY;
 clw_audit_one "CLW_BYTE_SEVEN_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200003) 7 T /\ clw_memory image (word 0x200003) 7 T (word 0x200003)=word 255` CLW_BYTE_SEVEN_FAMILY;
 clw_audit_one "CLW_BULK_ALIGNED_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200000) 24 F /\ clw_memory image (word 0x200000) 24 F (word 0x200000)=word 128` CLW_BULK_ALIGNED_FAMILY;
 clw_audit_one "CLW_MISALIGNED_BULK_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200001) 17 F /\ clw_memory image (word 0x200001) 17 F (word 0x200001)=word 128` CLW_MISALIGNED_BULK_FAMILY;
 clw_audit_one "CLW_MISALIGNED_TAIL_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200003) 33 T /\ clw_memory image (word 0x200003) 33 T (word 0x200003)=word 255` CLW_MISALIGNED_TAIL_FAMILY;
 clw_audit_one "CLW_USER_PAGE_BOUNDARY_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word 0x200fff) 17 F /\ clw_memory image (word 0x200fff) 17 F (word 0x200fff)=word 128` CLW_USER_PAGE_BOUNDARY_FAMILY;
 clw_audit_one "CLW_LOW_CANONICAL_EDGE_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 47-1)) 1 F /\ clw_memory image (word (2 EXP 47-1)) 1 F (word (2 EXP 47-1))=word 128` CLW_LOW_CANONICAL_EDGE_FAMILY;
 clw_audit_one "CLW_TOP_ENDPOINT_WRAP_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-1)) 1 T /\ clw_memory image (word (2 EXP 64-1)) 1 T (word (2 EXP 64-1))=word 255` CLW_TOP_ENDPOINT_WRAP_FAMILY;
 clw_audit_one "CLW_TOP_QWORD_ENDPOINT_WRAP_FAMILY" `!file_bytes initial_rw padding image. clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding image ==> clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-8)) 8 F /\ clw_memory image (word (2 EXP 64-8)) 8 F (word (2 EXP 64-8))=word 128` CLW_TOP_QWORD_ENDPOINT_WRAP_FAMILY;
 clw_audit_one "CLW_MACHINE_WITNESS_EXISTS" `!file_bytes initial_rw padding. clw_file_code file_bytes ==> ?image. fb_full_image file_bytes initial_rw padding image /\ (!p. clw_full_pre file_bytes initial_rw padding image p 0 F) /\ clw_full_pre file_bytes initial_rw padding image (word 0x200001) 1 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200003) 7 T /\ clw_full_pre file_bytes initial_rw padding image (word 0x200000) 24 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200001) 17 F /\ clw_full_pre file_bytes initial_rw padding image (word 0x200003) 33 T /\ clw_full_pre file_bytes initial_rw padding image (word 0x200fff) 17 F /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 47-1)) 1 F /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-1)) 1 T /\ clw_full_pre file_bytes initial_rw padding image (word (2 EXP 64-8)) 8 F` CLW_MACHINE_WITNESS_EXISTS
];;
print_endline("CLW_EXACT_AUDIT_PASS17_DEFINITIONS41_HYP0_NEWAXIOMS0");;
