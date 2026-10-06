(* Literal admissible-entry obligations, frozen before proof source. *)
let c2w_write64_outside_statement =
 `!(loc:int64) (value:int64) (addr:int64) (m:int64->byte).
    val loc+8<=2 EXP 64 /\ ~assurance_region loc 8 (val addr)
    ==> write (bytes64 loc) value m addr=m addr`;;
let c2w_memory_outside_statement =
 `!lib_file client_file p k different (addr:int64).
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x22003fd0) 8 (val addr) /\
    ~assurance_region (word 0x22003fd8) 8 (val addr)
    ==> c2w_memory lib_file client_file p k different addr=
        c2w_seed lib_file client_file p k different addr`;;
let c2w_memory_words_statement =
 `!lib_file client_file p k different.
    read (bytes64 (word 0x300008))
      (c2w_memory lib_file client_file p k different)=word 0x400000 /\
    read (bytes64 (word 0x22003fd0))
      (c2w_memory lib_file client_file p k different)=word 0x10241840 /\
    read (bytes64 (word 0x22003fd8))
      (c2w_memory lib_file client_file p k different)=word 0x102417d0`;;
let c2w_state_projections_statement =
 `!lib_file client_file p q n k different.
    read RIP (c2w_state lib_file client_file p q n k different)=word 0x22001120 /\
    read RSP (c2w_state lib_file client_file p q n k different)=word 0x300008 /\
    C_ARGUMENTS [p;q;word n] (c2w_state lib_file client_file p q n k different) /\
    read memory (c2w_state lib_file client_file p q n k different)=
      c2w_memory lib_file client_file p k different /\
    read DF (c2w_state lib_file client_file p q n k different)=F /\
    ~bit 18(read rflags (c2w_state lib_file client_file p q n k different)) /\
    e5_normal_flags (c2w_state lib_file client_file p q n k different)`;;
let c2w_initial_abi_statement =
 `assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi))`;;
let c2w_index_value_statement =
 `!(p:int64) n i. n<2 EXP 64 /\ val p+n<=2 EXP 64 /\ i<n
    ==> val(word_add p (word i))=val p+i`;;
let c2w_external_point_statement =
 `!(addr:int64). c2w_external(val addr) ==>
    ~fb_immutable(val addr) /\ ~c2_immutable(val addr) /\
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x22003fd0) 8 (val addr) /\
    ~assurance_region (word 0x22003fd8) 8 (val addr)`;;
let c2w_external_permissions_statement =
 `!addr. c2w_external addr ==> c2w_read addr /\ c2w_write addr /\ c2w_ordinary addr`;;
let c2w_layout_point_statement =
 `!p q n k different i. c2w_layout p q n k different /\ i<n ==>
    c2w_external(val(word_add p (word i))) /\
    c2w_external(val(word_add q (word i)))`;;
let c2w_memory_immutable_statement =
 `!lib_file client_file p k different (addr:int64).
    (fb_immutable(val addr) ==> c2w_memory lib_file client_file p k different addr=
      lib_file(val addr-0x10000000)) /\
    (c2_immutable(val addr) ==> c2w_memory lib_file client_file p k different addr=
      client_file(val addr-0x22000000))`;;
let c2w_memory_images_statement =
 `!lib_file client_file p k different.
    fb_full_image lib_file (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different) /\
    c2_full_image client_file (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different)`;;
let c2w_bytes_loaded_reads_statement =
 `!(s:x86state) (pc:int64) l.
    (!i. i<LENGTH l ==> read memory s (word_add pc (word i))=EL i l)
    ==> bytes_loaded s pc l`;;
let c2w_loaded_code_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c2_file_code client_file
    ==> c2_loaded_code(c2w_state lib_file client_file p q n k different)`;;
let c2w_image_permissions_statement =
 `(!addr. lw_image_domain addr ==> c2w_read addr /\ c2w_ordinary addr /\
    (c2w_execute addr <=> lw_execute addr) /\
    (c2w_write addr <=> lw_image_write addr)) /\
  (!addr. c2_image_domain addr ==> c2w_read addr /\ c2w_ordinary addr /\
    (c2w_execute addr <=> c2_image_execute addr) /\
    (c2w_write addr <=> c2_image_write addr))`;;
let c2w_fixed_spans_statement =
 `assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) (0x300008-32) 32 /\
  assurance_span_ok (\a. c2w_write a /\ c2w_ordinary a) (0x300008-32) 32 /\
  assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) 0x300008 8 /\
  assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) 0x22003fd0 8 /\
  assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) 0x22003fd8 8 /\
  assurance_span_ok (\a. c2w_execute a /\ c2w_ordinary a) 0x22001120 59 /\
  assurance_span_ok (\a. c2w_execute a /\ c2w_ordinary a) 0x22001030 6 /\
  assurance_span_ok (\a. c2w_execute a /\ c2w_ordinary a) 0x22001040 6 /\
  assurance_span_ok (\a. c2w_execute a /\ c2w_ordinary a) 0x10241840 95 /\
  assurance_span_ok (\a. c2w_execute a /\ c2w_ordinary a) 0x102417d0 97`;;
let c2w_layout_permissions_statement =
 `!p q n k different. c2w_layout p q n k different ==>
    assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) (val p) n /\
    assurance_span_ok (\a. c2w_read a /\ c2w_ordinary a) (val q) n /\
    assurance_span_ok (\a. c2w_write a /\ c2w_ordinary a) (val p) n /\
    (!addr. ~(assurance_region p n addr /\ c2_scratch(word 0x300008) addr)) /\
    (!addr. ~(assurance_region q n addr /\ c2_scratch(word 0x300008) addr)) /\
    (!addr. ~(assurance_region p n addr /\ assurance_region (word 0x300008) 8 addr))`;;
let c2w_eight_layouts_statement =
 `c2w_layout (word 0) (word 0) 0 0 F /\
  c2w_layout (word 0x50000000) (word 0x60000000) 1 0 F /\
  c2w_layout (word 0x50000003) (word 0x60000005) 17 0 T /\
  c2w_layout (word 0x50000003) (word 0x50000003) 16 0 F /\
  c2w_layout (word 0x50000003) (word 0x50000004) 17 0 F /\
  c2w_layout (word 0x50000003) (word 0x50000004) 17 0 T /\
  c2w_layout (word 0x50000fff) (word 0x60000fff) 15 14 T /\
  c2w_layout (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T`;;
let c2w_buffer_values_statement =
 `!lib_file client_file p q n k different. c2w_layout p q n k different ==>
    (!i. i<n ==> c2w_memory lib_file client_file p k different
      (word_add p (word i))=(if different /\ i=k then word 255 else word 128)) /\
    (!i. i<n ==> c2w_memory lib_file client_file p k different
      (word_add q (word i))=word 128)`;;
let c2w_pre_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c2_file_code client_file /\ c2w_layout p q n k different
    ==> c2_pre lib_file (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different) client_file
      (c2w_memory lib_file client_file p k different)
      (c2w_memory lib_file client_file p k different)
      (word 0x300008) (word 0x400000) p q n
      (c2w_memory lib_file client_file p k different)
      c2w_read c2w_write c2w_execute c2w_ordinary
      (c2w_state lib_file client_file p q n k different,fb_initial_abi)`;;
let c2w_generic_witness_statement =
 `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ clw_file_code lib_file /\ c2_file_code client_file /\ c2w_layout p q n k different
    ==> c2_entry_witness lib_file client_file p q n k different`;;
let c2_admissible_entry_witnesses_statement =
 `!lib_file client_file. fb_file_code lib_file /\ clw_file_code lib_file /\ c2_file_code client_file ==>
    c2_entry_witness lib_file client_file (word 0) (word 0) 0 0 F /\
    c2_entry_witness lib_file client_file
      (word 0x50000000) (word 0x60000000) 1 0 F /\
    c2_entry_witness lib_file client_file
      (word 0x50000003) (word 0x60000005) 17 0 T /\
    c2_entry_witness lib_file client_file
      (word 0x50000003) (word 0x50000003) 16 0 F /\
    c2_entry_witness lib_file client_file
      (word 0x50000003) (word 0x50000004) 17 0 F /\
    c2_entry_witness lib_file client_file
      (word 0x50000003) (word 0x50000004) 17 0 T /\
    c2_entry_witness lib_file client_file
      (word 0x50000fff) (word 0x60000fff) 15 14 T /\
    c2_entry_witness lib_file client_file
      (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T`;;
