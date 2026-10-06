(* Independent OPENSSL_cleanse initial-state witnesses. Definitions frozen
   before proof search. No output-read span, target behavior or post-state
   preservation premise. Whole image/page/TLS/14 ABI fields reuse exact V4. *)
let clw_file_code = new_definition
 `clw_file_code (file_bytes:num->byte) <=>
    !i. i<97 ==> file_bytes(0x2417d0+i)=EL i openssl_cleanse_mc`;;
let clw_reference_code = new_definition
 `clw_reference_code (image:int64->byte) <=>
    !i. i<97 ==> image(word(0x102417d0+i))=EL i openssl_cleanse_mc`;;
let clw_layout = new_definition
 `clw_layout p n <=> lw_layout p p n`;;
let clw_memory = new_definition
 `clw_memory image p n high_first = lw_memory image p p n high_first`;;
let clw_state = new_definition
 `clw_state (image:int64->byte) (p:int64) n high_first =
    x86state_RECORD (word 0x102417d0)
      (\r:(4)word. if r=word 7 then p
                  else if r=word 6 then word n
                  else if r=word 4 then word 0x300008
                  else word 0)
      (\z:(5)word. word 0) (\k:(3)word. word 0) (word 2)
      (clw_memory image p n high_first) []`;;
(* Writable amd64 pages are also readable. The unchanged entry predicate
   requires no destination read permission and no output-readability span. *)
let clw_read = new_definition
 `clw_read p n a <=> fb_read p p n a`;;
let clw_write = new_definition
 `clw_write p n a <=> lw_image_write a \/ lw_pagecover p n a`;;
let clw_ordinary = new_definition
 `clw_ordinary p n a <=> fb_ordinary p p n a`;;
let clw_scalar_pre = new_definition
 `clw_scalar_pre image p n high_first <=>
    bp_e2_cleanse_pre 0x102417d0 (word 0x300008) (word 0x400000) p n
      (clw_memory image p n high_first) (clw_read p n) (clw_write p n)
      lw_execute (clw_ordinary p n) (clw_state image p n high_first)`;;
let clw_machine = new_definition
 `clw_machine image p n high_first =
    (clw_state image p n high_first,fb_initial_abi)`;;
(* Entire initialized image is bound at entry only. No equality to this RW
   map is required after execution: generic cleanse may legally write RW. *)
let clw_full_pre = new_definition
 `clw_full_pre file_bytes initial_rw padding image p n high_first <=>
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
          (clw_write p n a <=> lw_image_write a))`;;
