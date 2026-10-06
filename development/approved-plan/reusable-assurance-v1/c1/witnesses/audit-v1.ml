(* Literal v2 definition and target checks; no execution or isolation claim. *)
let cw_audit_definition name expected th =
 if hyp th <> [] then failwith(name^": definition hypotheses");
 if not(aconv expected (concl(SPEC_ALL th))) then failwith(name^": definition mismatch");
 Printf.printf "C1_ENTRY_DEFINITION_CHECKED %s\n%!" name;;
cw_audit_definition "c1_entry_witness" `c1_entry_witness lib_file client_file p q n k different <=>
    ?lib_rw lib_padding client_rw client_padding m rp wp xp ordinary s a.
      c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
        (word 0x300008) (word 0x400000) p q n m rp wp xp ordinary (s,a) /\
      (!i. i<n ==> m(word_add p (word i))=
        (if different /\ i=k then word 255 else word 128)) /\
      (!i. i<n ==> m(word_add q (word i))=word 128) /\
      (p=word 0 /\ q=word 0 /\ n=0 ==> ~rp 0)` c1_entry_witness;;
cw_audit_definition "cw_execute" `cw_execute a <=> lw_execute a \/ c1_image_execute a` cw_execute;;
cw_audit_definition "cw_external" `cw_external a <=> 0x50000000 <= a /\ assurance_canonical48 a` cw_external;;
cw_audit_definition "cw_layout" `cw_layout (p:int64) (q:int64) n k different <=>
    n<2 EXP 64 /\ assurance_span_ok cw_external (val p) n /\
    assurance_span_ok cw_external (val q) n /\
    (different ==> k<n /\
      !i. i<n ==> ~(word_add q (word i)=word_add p (word k)))` cw_layout;;
cw_audit_definition "cw_memory" `cw_memory lib_file client_file p k different =
    write (bytes64 (word 0x300008)) (word 0x400000)
      (write (bytes64 (word 0x21003fd8)) (word 0x10241840)
        (cw_seed lib_file client_file p k different))` cw_memory;;
cw_audit_definition "cw_ordinary" `cw_ordinary a <=> assurance_canonical48 a` cw_ordinary;;
cw_audit_definition "cw_read" `cw_read a <=> assurance_canonical48 a /\ ~(a=0)` cw_read;;
cw_audit_definition "cw_seed" `cw_seed (lib_file:num->byte) (client_file:num->byte)
    (p:int64) k different (addr:int64) =
    if fb_immutable (val addr) then lib_file(val addr-0x10000000)
    else if c1_immutable (val addr) then client_file(val addr-0x21000000)
    else if different /\ addr=word_add p (word k) then word 255 else word 128` cw_seed;;
cw_audit_definition "cw_state" `cw_state lib_file client_file p q n k different =
    x86state_RECORD (word 0x21001110)
      (\j:(4)word. if j=word 7 then p else if j=word 6 then q
                    else if j=word 2 then word n
                    else if j=word 4 then word 0x300008 else word 0)
      (\j:(5)word. word 0) (\j:(3)word. word 0) (word 2)
      (cw_memory lib_file client_file p k different) []` cw_state;;
cw_audit_definition "cw_write" `cw_write a <=>
    if lw_image_domain a then lw_image_write a
    else if c1_image_domain a then c1_image_write a
    else assurance_canonical48 a` cw_write;;
let cw_audit_target name expected th =
 if not(aconv expected (concl th)) then failwith(name^": wrong target");
 if hyp th <> [] then failwith(name^": residual hypotheses");
 if frees(concl th) <> [] then failwith(name^": free variables");
 Printf.printf "C1_ENTRY_TARGET_CHECKED %s\n%!" name;;
cw_audit_target "C1_ADMISSIBLE_ENTRY_WITNESSES" `!lib_file client_file. fb_file_code lib_file /\ c1_file_code client_file ==>
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
      (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T` C1_ADMISSIBLE_ENTRY_WITNESSES;;
cw_audit_target "CW_BUFFER_VALUES" `!lib_file client_file p q n k different. cw_layout p q n k different ==>
    (!i. i<n ==> cw_memory lib_file client_file p k different
      (word_add p (word i))=(if different /\ i=k then word 255 else word 128)) /\
    (!i. i<n ==> cw_memory lib_file client_file p k different
      (word_add q (word i))=word 128)` CW_BUFFER_VALUES;;
cw_audit_target "CW_BYTES_LOADED_READS" `!(s:x86state) (pc:int64) l.
    (!i. i<LENGTH l ==> read memory s (word_add pc (word i))=EL i l)
    ==> bytes_loaded s pc l` CW_BYTES_LOADED_READS;;
cw_audit_target "CW_EXTERNAL_PERMISSIONS" `!addr. cw_external addr ==> cw_read addr /\ cw_write addr /\ cw_ordinary addr` CW_EXTERNAL_PERMISSIONS;;
cw_audit_target "CW_EXTERNAL_POINT" `!(addr:int64). cw_external(val addr) ==>
    ~fb_immutable(val addr) /\ ~c1_immutable(val addr) /\
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x21003fd8) 8 (val addr)` CW_EXTERNAL_POINT;;
cw_audit_target "CW_FIXED_SPANS" `assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (0x300008-16) 8 /\
  assurance_span_ok (\a. cw_write a /\ cw_ordinary a) (0x300008-16) 8 /\
  assurance_span_ok (\a. cw_read a /\ cw_ordinary a) 0x300008 8 /\
  assurance_span_ok (\a. cw_read a /\ cw_ordinary a) 0x21003fd8 8 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x21001110 22 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x21001030 6 /\
  assurance_span_ok (\a. cw_execute a /\ cw_ordinary a) 0x10241840 95` CW_FIXED_SPANS;;
cw_audit_target "CW_GENERIC_WITNESS" `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file /\ cw_layout p q n k different
    ==> c1_entry_witness lib_file client_file p q n k different` CW_GENERIC_WITNESS;;
cw_audit_target "CW_IMAGE_PERMISSIONS" `(!addr. lw_image_domain addr ==> cw_read addr /\ cw_ordinary addr /\
    (cw_execute addr <=> lw_execute addr) /\
    (cw_write addr <=> lw_image_write addr)) /\
  (!addr. c1_image_domain addr ==> cw_read addr /\ cw_ordinary addr /\
    (cw_execute addr <=> c1_image_execute addr) /\
    (cw_write addr <=> c1_image_write addr))` CW_IMAGE_PERMISSIONS;;
cw_audit_target "CW_INDEX_VALUE" `!(p:int64) n i. n<2 EXP 64 /\ val p+n<=2 EXP 64 /\ i<n
    ==> val(word_add p (word i))=val p+i` CW_INDEX_VALUE;;
cw_audit_target "CW_INITIAL_ABI" `assurance_canonical48(val(read ABI_FS_BASE fb_initial_abi))` CW_INITIAL_ABI;;
cw_audit_target "CW_LAYOUT_PERMISSIONS" `!p q n k different. cw_layout p q n k different ==>
    assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (val p) n /\
    assurance_span_ok (\a. cw_read a /\ cw_ordinary a) (val q) n /\
    (!addr. ~(assurance_region p n addr /\ c1_call_slot(word 0x300008) addr)) /\
    (!addr. ~(assurance_region q n addr /\ c1_call_slot(word 0x300008) addr))` CW_LAYOUT_PERMISSIONS;;
cw_audit_target "CW_LAYOUT_POINT" `!p q n k different i. cw_layout p q n k different /\ i<n ==>
    cw_external(val(word_add p (word i))) /\
    cw_external(val(word_add q (word i)))` CW_LAYOUT_POINT;;
cw_audit_target "CW_LOADED_CODE" `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file
    ==> c1_loaded_code(cw_state lib_file client_file p q n k different)` CW_LOADED_CODE;;
cw_audit_target "CW_MEMORY_IMAGES" `!lib_file client_file p k different.
    fb_full_image lib_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different) /\
    c1_full_image client_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)` CW_MEMORY_IMAGES;;
cw_audit_target "CW_MEMORY_IMMUTABLE" `!lib_file client_file p k different (addr:int64).
    (fb_immutable(val addr) ==> cw_memory lib_file client_file p k different addr=
      lib_file(val addr-0x10000000)) /\
    (c1_immutable(val addr) ==> cw_memory lib_file client_file p k different addr=
      client_file(val addr-0x21000000))` CW_MEMORY_IMMUTABLE;;
cw_audit_target "CW_MEMORY_OUTSIDE" `!lib_file client_file p k different (addr:int64).
    ~assurance_region (word 0x300008) 8 (val addr) /\
    ~assurance_region (word 0x21003fd8) 8 (val addr)
    ==> cw_memory lib_file client_file p k different addr=
        cw_seed lib_file client_file p k different addr` CW_MEMORY_OUTSIDE;;
cw_audit_target "CW_MEMORY_WORDS" `!lib_file client_file p k different.
    read (bytes64 (word 0x300008))
      (cw_memory lib_file client_file p k different)=word 0x400000 /\
    read (bytes64 (word 0x21003fd8))
      (cw_memory lib_file client_file p k different)=word 0x10241840` CW_MEMORY_WORDS;;
cw_audit_target "CW_PRE" `!lib_file client_file p q n k different.
    fb_file_code lib_file /\ c1_file_code client_file /\ cw_layout p q n k different
    ==> c1_pre lib_file (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different) client_file
      (cw_memory lib_file client_file p k different)
      (cw_memory lib_file client_file p k different)
      (word 0x300008) (word 0x400000) p q n
      (cw_memory lib_file client_file p k different)
      cw_read cw_write cw_execute cw_ordinary
      (cw_state lib_file client_file p q n k different,fb_initial_abi)` CW_PRE;;
cw_audit_target "CW_SEVEN_LAYOUTS" `cw_layout (word 0) (word 0) 0 0 F /\
  cw_layout (word 0x50000000) (word 0x60000000) 1 0 F /\
  cw_layout (word 0x50000003) (word 0x60000005) 17 0 T /\
  cw_layout (word 0x50000003) (word 0x50000003) 16 0 F /\
  cw_layout (word 0x50000003) (word 0x50000004) 17 0 F /\
  cw_layout (word 0x50000fff) (word 0x60000fff) 15 14 T /\
  cw_layout (word 0x7fffffffffff) (word 0xffff800000000000) 1 0 T` CW_SEVEN_LAYOUTS;;
cw_audit_target "CW_STATE_PROJECTIONS" `!lib_file client_file p q n k different.
    read RIP (cw_state lib_file client_file p q n k different)=word 0x21001110 /\
    read RSP (cw_state lib_file client_file p q n k different)=word 0x300008 /\
    C_ARGUMENTS [p;q;word n] (cw_state lib_file client_file p q n k different) /\
    read memory (cw_state lib_file client_file p q n k different)=
      cw_memory lib_file client_file p k different /\
    read DF (cw_state lib_file client_file p q n k different)=F /\
    ~bit 18(read rflags (cw_state lib_file client_file p q n k different)) /\
    e5_normal_flags (cw_state lib_file client_file p q n k different)` CW_STATE_PROJECTIONS;;
cw_audit_target "CW_WRITE64_OUTSIDE" `!(loc:int64) (value:int64) (addr:int64) (m:int64->byte).
    val loc+8<=2 EXP 64 /\ ~assurance_region loc 8 (val addr)
    ==> write (bytes64 loc) value m addr=m addr` CW_WRITE64_OUTSIDE;;
