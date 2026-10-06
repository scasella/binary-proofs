(* Literal admissible-entry obligations, frozen before proof source. *)
let cw_write64_outside_statement =
 `!(loc:int64) (value:int64) (addr:int64) (m:int64->byte).
    val loc+8<=2 EXP 64 /\ ~assurance_region loc 8 (val addr)
    ==> write (bytes64 loc) value m addr=m addr`;;
let cw_memory_outside_statement =
 `!lib_file client_file p k different (addr:int64).
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x21003fd8) 8 (val addr)
    ==> cw_memory lib_file client_file p k different addr=
        cw_seed lib_file client_file p k different addr`;;
let cw_memory_words_statement =
 `!lib_file client_file p k different.
    read (bytes64 (word 0x300008))
      (cw_memory lib_file client_file p k different)=word 0x400000 /\
    read (bytes64 (word 0x21003fd8))
      (cw_memory lib_file client_file p k different)=word 0x10241840`;;
let cw_state_projections_statement =
 `!lib_file client_file p q n k different.
    read RIP (cw_state lib_file client_file p q n k different)=word 0x21001110 /\
    read RSP (cw_state lib_file client_file p q n k different)=word 0x300008 /\
    C_ARGUMENTS [p;q;word n] (cw_state lib_file client_file p q n k different) /\
    read memory (cw_state lib_file client_file p q n k different)=
      cw_memory lib_file client_file p k different /\
    read DF (cw_state lib_file client_file p q n k different)=F /\
    ~bit 18(read rflags (cw_state lib_file client_file p q n k different)) /\
    e5_normal_flags (cw_state lib_file client_file p q n k different)`;;
let cw_initial_abi_statement =
 `assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi))`;;
let cw_index_value_statement =
 `!(p:int64) n i. n<2 EXP 64 /\ val p+n<=2 EXP 64 /\ i<n
    ==> val(word_add p (word i))=val p+i`;;
let cw_external_point_statement =
 `!(addr:int64). cw_external(val addr) ==>
    ~fb_immutable(val addr) /\ ~c1_immutable(val addr) /\
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x21003fd8) 8 (val addr)`;;
let cw_external_permissions_statement =
 `!addr. cw_external addr ==> cw_read addr /\ cw_write addr /\ cw_ordinary addr`;;
let cw_layout_point_statement =
 `!p q n k different i. cw_layout p q n k different /\ i<n ==>
    cw_external(val(word_add p (word i))) /\
    cw_external(val(word_add q (word i)))`;;
let cw_memory_immutable_statement =
 `!lib_file client_file p k different (addr:int64).
    (fb_immutable(val addr) ==> cw_memory lib_file client_file p k different addr=
      lib_file(val addr-0x10000000)) /\
    (c1_immutable(val addr) ==> cw_memory lib_file client_file p k different addr=
      client_file(val addr-0x21000000))`;;
let cw_memory_images_statement =
 `!lib_file client_file p k different.
    fb_full_image lib_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different) /\
    c1_full_image client_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)`;;
let cw_bytes_loaded_reads_statement =
 `!(s:x86state) (pc:int64) l.
    (!i. i<LENGTH l ==> read memory s (word_add pc (word i))=EL i l)
    ==> bytes_loaded s pc l`;;
let cw_loaded_code_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file
    ==> c1_loaded_code(cw_state lib_file client_file p q n k different)`;;
let cw_image_permissions_statement =
 `(!addr. lw_image_domain addr ==> cw_read addr /\ cw_ordinary addr /\
    (cw_execute addr <=> lw_execute addr) /\
    (cw_write addr <=> lw_image_write addr)) /\
  (!addr. c1_image_domain addr ==> cw_read addr /\ cw_ordinary addr /\
    (cw_execute addr <=> c1_image_execute addr) /\
    (cw_write addr <=> c1_image_write addr))`;;
let cw_fixed_spans_statement =
 `assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (0x300008-16) 8 /\
  assurance_span_ok (\a. cw_write a /\ cw_ordinary a) (0x300008-16) 8 /\
  assurance_span_ok (\a. cw_read a /\ cw_ordinary a) 0x300008 8 /\
  assurance_span_ok (\a. cw_read a /\ cw_ordinary a) 0x21003fd8 8 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x21001110 22 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x21001030 6 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x10241840 95`;;
let cw_layout_permissions_statement =
 `!p q n k different. cw_layout p q n k different ==>
    assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (val p) n /\
    assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (val q) n /\
    (!addr. ~(assurance_region p n addr /\ c1_call_slot(word 0x300008) addr)) /\
    (!addr. ~(assurance_region q n addr /\ c1_call_slot(word 0x300008) addr))`;;
let cw_seven_layouts_statement =
 `cw_layout (word 0) (word 0) 0 0 F /\
  cw_layout (word 0x50000000) (word 0x60000000) 1 0 F /\
  cw_layout (word 0x50000003) (word 0x60000005) 17 0 T /\
  cw_layout (word 0x50000003) (word 0x50000003) 16 0 F /\
  cw_layout (word 0x50000003) (word 0x50000004) 17 0 F /\
  cw_layout (word 0x50000fff) (word 0x60000fff) 15 14 T /\
  cw_layout (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T`;;
let cw_buffer_values_statement =
 `!lib_file client_file p q n k different. cw_layout p q n k different ==>
    (!i. i<n ==> cw_memory lib_file client_file p k different
      (word_add p (word i))=(if different /\ i=k then word 255 else word 128)) /\
    (!i. i<n ==> cw_memory lib_file client_file p k different
      (word_add q (word i))=word 128)`;;
let cw_pre_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file /\ cw_layout p q n k different
    ==> c1_pre lib_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different) client_file
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (word 0x300008) (word 0x400000) p q n
      (cw_memory lib_file client_file p k different)
      cw_read cw_write cw_execute cw_ordinary
      (cw_state lib_file client_file p q n k different,fb_initial_abi)`;;
let cw_generic_witness_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file /\ cw_layout p q n k different
    ==> c1_entry_witness lib_file client_file p q n k different`;;
let c1_admissible_entry_witnesses_statement =
 `!lib_file client_file. fb_file_code lib_file /\ c1_file_code client_file ==>
    c1_entry_witness lib_file client_file (word 0) (word 0) 0 0 F /\
    c1_entry_witness lib_file client_file
      (word 0x50000000) (word 0x60000000) 1 0 F /\
    c1_entry_witness lib_file client_file
      (word 0x50000003) (word 0x60000005) 17 0 T /\
    c1_entry_witness lib_file client_file
      (word 0x50000003) (word 0x50000003) 16 0 F /\
    c1_entry_witness lib_file client_file
      (word 0x50000003) (word 0x50000004) 17 0 F /\
    c1_entry_witness lib_file client_file
      (word 0x50000fff) (word 0x60000fff) 15 14 T /\
    c1_entry_witness lib_file client_file
      (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T`;;
