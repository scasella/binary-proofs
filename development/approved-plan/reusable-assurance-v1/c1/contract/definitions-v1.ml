(* BP-20261004-REUSE-V1 C1: exact final-linked artifact specification.
   No correctness theorem is assumed. No supplier body is loaded here. *)
let c1_crypto_caller_mc = new_definition
 `c1_crypto_caller_mc:byte list =
   [word 0x48;word 0x83;word 0xec;word 0x08;
    word 0xe8;word 0x17;word 0xff;word 0xff;word 0xff;
    word 0x85;word 0xc0;word 0x0f;word 0x94;word 0xc0;
    word 0x48;word 0x83;word 0xc4;word 0x08;
    word 0x0f;word 0xb6;word 0xc0;word 0xc3]`;;
let c1_crypto_plt_prefix = new_definition
 `c1_crypto_plt_prefix:byte list =
   [word 0xff;word 0x25;word 0xa2;word 0x2f;word 0x00;word 0x00]`;;
let c1_image_domain = new_definition
 `c1_image_domain a <=> 0x21000000 <= a /\ a < 0x21005000`;;
let c1_image_execute = new_definition
 `c1_image_execute a <=> 0x21001000 <= a /\ a < 0x21002000`;;
let c1_image_write = new_definition
 `c1_image_write a <=> 0x21004000 <= a /\ a < 0x21005000`;;
let c1_immutable = new_definition
 `c1_immutable a <=>
    (0x21000000 <= a /\ a < 0x21000508) \/
    (0x21001000 <= a /\ a < 0x21001131) \/
    (0x21002000 <= a /\ a < 0x2100209c)`;;
let c1_initialized_rw = new_definition
 `c1_initialized_rw a <=> 0x21003db0 <= a /\ a < 0x21004010`;;
let c1_reference_image = new_definition
 `c1_reference_image (file_bytes:num->byte)
     (initial_rw:int64->byte) (padding:int64->byte) (a:int64) =
    if c1_immutable (val a) then file_bytes (val a - 0x21000000)
    else if c1_initialized_rw (val a) then initial_rw a else padding a`;;
let c1_full_image = new_definition
 `c1_full_image file_bytes initial_rw padding (m:int64->byte) <=>
    !a. c1_image_domain (val a)
        ==> m a = c1_reference_image file_bytes initial_rw padding a`;;
let c1_file_code = new_definition
 `c1_file_code (file_bytes:num->byte) <=>
    (!i. i<22 ==> file_bytes(0x1110+i)=EL i c1_crypto_caller_mc) /\
    (!i. i<6 ==> file_bytes(0x1030+i)=EL i c1_crypto_plt_prefix)`;;
let c1_loaded_code = new_definition
 `c1_loaded_code (s:x86state) <=>
    bytes_loaded s (word 0x21001110) c1_crypto_caller_mc /\
    bytes_loaded s (word 0x21001030) c1_crypto_plt_prefix /\
    bytes_loaded s (word 0x10241840) crypto_memcmp_mc`;;
let c1_got = new_definition
 `c1_got (s:x86state) <=>
    read (memory :> bytes64 (word 0x21003fd8)) s=word 0x10241840`;;
let c1_call_slot = new_definition
 `c1_call_slot (stackpointer:int64) a <=>
    assurance_region (word_sub stackpointer (word 16)) 8 a`;;
let c1_allowed_read = new_definition
 `c1_allowed_read rp ordinary stackpointer p q n a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     c1_call_slot stackpointer a \/ assurance_region stackpointer 8 a \/
     assurance_region (word 0x21003fd8) 8 a)`;;
let c1_allowed_write = new_definition
 `c1_allowed_write wp ordinary stackpointer a <=>
    wp a /\ ordinary a /\ c1_call_slot stackpointer a`;;
let c1_allowed_fetch = new_definition
 `c1_allowed_fetch xp ordinary a <=>
    xp a /\ ordinary a /\
    (assurance_region (word 0x21001110) 22 a \/
     assurance_region (word 0x21001030) 6 a \/
     assurance_region (word 0x10241840) 95 a)`;;
let c1_steps = new_definition
 `c1_steps n = 8 + bp_assurance_call_steps n`;;
let c1_frame = new_definition
 `c1_frame stackpointer =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),8)] ,,
    MAYCHANGE [events]`;;
let c1_pre = new_definition
 `c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary
    (s:x86state,a:abi_omitted_state) <=>
    n<2 EXP 64 /\ 16<=val(stackpointer:int64) /\
    val stackpointer MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word 0x21001110) /\
    read RIP s=word 0x21001110 /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\
    read DF s=F /\ ~bit 18(read rflags s) /\ e5_normal_flags s /\
    assurance_canonical48(val(read ABI_FS_BASE a)) /\
    fb_file_code lib_file /\ fb_full_image lib_file lib_rw lib_padding m /\
    c1_file_code client_file /\
    c1_full_image client_file client_rw client_padding m /\
    c1_loaded_code s /\ c1_got s /\
    (!addr. lw_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
       (wp addr <=> lw_image_write addr)) /\
    (!addr. c1_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> c1_image_execute addr) /\
       (wp addr <=> c1_image_write addr)) /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val q) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer-16) 8 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val stackpointer-16) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x21003fd8 8 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x21001110 22 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x21001030 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x10241840 95 /\
    (!addr. ~(assurance_region p n addr /\ c1_call_slot stackpointer addr)) /\
    (!addr. ~(assurance_region q n addr /\ c1_call_slot stackpointer addr)) /\
    (!addr. ~(assurance_region stackpointer 8 addr /\
              c1_call_slot stackpointer addr))`;;
let c1_scalar_post = new_definition
 `c1_scalar_post stackpointer ra p q n m (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=(if (!i. i<n ==> m(word_add p (word i))=
                                  m(word_add q (word i)))
                then word 1 else word 0) /\
    (!addr. ~c1_call_slot stackpointer (val addr)
            ==> read memory t addr=m addr) /\
    read (memory :> bytes64 stackpointer) t=ra /\
    read RBX t=read RBX s /\ read RBP t=read RBP s /\
    read R12 t=read R12 s /\ read R13 t=read R13 s /\
    read R14 t=read R14 s /\ read R15 t=read R15 s /\
    read DF t=F /\ c1_loaded_code t /\ c1_got t /\
    c1_frame stackpointer s t`;;
let c1_public_post = new_definition
 `c1_public_post stackpointer ra p q n m s a
    (t:x86state#abi_omitted_state) <=>
    c1_scalar_post stackpointer ra p q n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)`;;
let c1_segment_policy = new_definition
 `c1_segment_policy stackpointer p q n rp wp xp ordinary
    remaining source target <=>
    assurance_step_policy
      (c1_allowed_read rp ordinary stackpointer p q n)
      (c1_allowed_write wp ordinary stackpointer)
      (c1_allowed_fetch xp ordinary) source target /\
    abi_all_decodes_caller_scalar source`;;
let c1_step_policy = new_definition
 `c1_step_policy stackpointer p q n rp wp xp ordinary
    remaining source target <=>
    c1_segment_policy stackpointer p q n rp wp xp ordinary
      remaining source target /\
    (remaining=1 ==> assurance_actual_ret 1 source target)`;;
let c1_prefix_frame = new_definition
 `c1_prefix_frame stackpointer =
    MAYCHANGE [RIP;RSP] ,, MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),8)] ,,
    MAYCHANGE [events]`;;
let c1_crypto_ready = new_definition
 `c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary
    (s:x86state) a (t:x86state) <=>
    bp_e2_crypto_public_pre lib_file (read memory t) (read memory t)
      (word_sub stackpointer (word 16)) (word 0x21001119) p q n
      (read memory t) rp xp ordinary (t,a) /\
    (!addr. ~c1_call_slot stackpointer (val addr)
            ==> read memory t addr=m addr) /\
    (!i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))) /\
    (!i. i<n ==> read memory t (word_add q (word i))=m(word_add q (word i))) /\
    read (memory :> bytes64 stackpointer) t=
      read (memory :> bytes64 stackpointer) s /\
    c1_loaded_code t /\ c1_got t /\ c1_prefix_frame stackpointer s t`;;
