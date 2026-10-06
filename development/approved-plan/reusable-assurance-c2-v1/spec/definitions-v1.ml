(* BP-20261004-C2-V1. Frozen interface-only specification candidate.
   New C2 predicates are definitions, not assumed target-correctness facts.
   Human formal/architectural review PENDING; no C2 proof constructed. *)
let c2_caller_mc = new_definition
 `c2_caller_mc:byte list =
   [word 0x41;word 0x54;word 0x45;word 0x31;word 0xe4;word 0x55;word 0x48;word 0x89;
    word 0xd5;word 0x53;word 0x48;word 0x89;word 0xfb;word 0xe8;word 0xfe;word 0xfe;
    word 0xff;word 0xff;word 0x85;word 0xc0;word 0x41;word 0x0f;word 0x94;word 0xc4;
    word 0x74;word 0x0e;word 0x44;word 0x89;word 0xe0;word 0x5b;word 0x5d;word 0x41;
    word 0x5c;word 0xc3;word 0x66;word 0x0f;word 0x1f;word 0x44;word 0x00;word 0x00;
    word 0x48;word 0x89;word 0xee;word 0x48;word 0x89;word 0xdf;word 0xe8;word 0xed;
    word 0xfe;word 0xff;word 0xff;word 0x44;word 0x89;word 0xe0;word 0x5b;word 0x5d;
    word 0x41;word 0x5c;word 0xc3]`;;
let c2_crypto_plt_prefix = new_definition
 `c2_crypto_plt_prefix:byte list =
   [word 0xff;word 0x25;word 0x9a;word 0x2f;word 0x00;word 0x00]`;;
let c2_cleanse_plt_prefix = new_definition
 `c2_cleanse_plt_prefix:byte list =
   [word 0xff;word 0x25;word 0x92;word 0x2f;word 0x00;word 0x00]`;;
let c2_equal = new_definition
 `c2_equal (m:int64->byte) (p:int64) (q:int64) n <=>
    !i. i<n ==> m(word_add p (word i))=m(word_add q (word i))`;;
let c2_image_domain = new_definition
 `c2_image_domain a <=> 0x22000000 <= a /\ a < 0x22005000`;;
let c2_image_execute = new_definition
 `c2_image_execute a <=> 0x22001000 <= a /\ a < 0x22002000`;;
let c2_image_write = new_definition
 `c2_image_write a <=> 0x22004000 <= a /\ a < 0x22005000`;;
let c2_immutable = new_definition
 `c2_immutable a <=>
    (0x22000000 <= a /\ a < 0x22000550) \/
    (0x22001000 <= a /\ a < 0x22001165) \/
    (0x22002000 <= a /\ a < 0x220020bc)`;;
let c2_initialized_rw = new_definition
 `c2_initialized_rw a <=> 0x22003da8 <= a /\ a < 0x22004010`;;
let c2_reference_image = new_definition
 `c2_reference_image (file_bytes:num->byte)
     (initial_rw:int64->byte) (padding:int64->byte) (a:int64) =
    if c2_immutable (val a)
    then file_bytes (val a - 0x22000000)
    else if c2_initialized_rw (val a) then initial_rw a
    else padding a`;;
let c2_full_image = new_definition
 `c2_full_image file_bytes initial_rw padding (m:int64->byte) <=>
    !a. c2_image_domain (val a)
        ==> m a = c2_reference_image file_bytes initial_rw padding a`;;
let c2_file_code = new_definition
 `c2_file_code (file_bytes:num->byte) <=>
    (!i. i<59 ==> file_bytes(0x1120+i)=EL i c2_caller_mc) /\
    (!i. i<6 ==> file_bytes(0x1030+i)=EL i c2_crypto_plt_prefix) /\
    (!i. i<6 ==> file_bytes(0x1040+i)=EL i c2_cleanse_plt_prefix)`;;
let c2_loaded_code = new_definition
 `c2_loaded_code (s:x86state) <=>
    bytes_loaded s (word 0x22001120) c2_caller_mc /\
    bytes_loaded s (word 0x22001030) c2_crypto_plt_prefix /\
    bytes_loaded s (word 0x22001040) c2_cleanse_plt_prefix /\
    bytes_loaded s (word 0x10241840) crypto_memcmp_mc /\
    bytes_loaded s (word 0x102417d0) openssl_cleanse_mc`;;
let c2_got = new_definition
 `c2_got (s:x86state) <=>
    read (memory :> bytes64 (word 0x22003fd0)) s=word 0x10241840 /\
    read (memory :> bytes64 (word 0x22003fd8)) s=word 0x102417d0`;;
let c2_scratch = new_definition
 `c2_scratch (stackpointer:int64) a <=>
    assurance_region (word_sub stackpointer (word 32)) 32 a`;;
let c2_allowed_read = new_definition
 `c2_allowed_read rp ordinary stackpointer p q n a <=>
    rp a /\ ordinary a /\
    (assurance_region p n a \/ assurance_region q n a \/
     c2_scratch stackpointer a \/
     assurance_region stackpointer 8 a \/
     assurance_region (word 0x22003fd0) 8 a \/
     assurance_region (word 0x22003fd8) 8 a)`;;
let c2_allowed_write = new_definition
 `c2_allowed_write wp ordinary stackpointer p q n m a <=>
    wp a /\ ordinary a /\
    ((c2_equal m p q n /\ assurance_region p n a) \/
     c2_scratch stackpointer a)`;;
let c2_allowed_fetch = new_definition
 `c2_allowed_fetch xp ordinary a <=>
    xp a /\ ordinary a /\
    (assurance_region (word 0x22001120) 59 a \/
     assurance_region (word 0x22001030) 6 a \/
     assurance_region (word 0x22001040) 6 a \/
     assurance_region (word 0x10241840) 95 a \/
     assurance_region (word 0x102417d0) 97 a)`;;
let c2_steps = new_definition
 `c2_steps p q n m =
    if c2_equal m p q n
    then 20 + bp_assurance_call_steps n + cleanse_functional_steps p n
    else 16 + bp_assurance_call_steps n`;;
let c2_frame = new_definition
 `c2_frame stackpointer p q n m =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(p,if c2_equal m p q n then n else 0);
               memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]`;;
let c2_pre = new_definition
 `c2_pre lib_file lib_rw lib_padding client_file client_rw
    client_padding stackpointer ra p q n m rp wp xp ordinary
    (s:x86state,a:abi_omitted_state) <=>
    n<2 EXP 64 /\ 32<=val(stackpointer:int64) /\
    val stackpointer MOD 16=8 /\ val stackpointer+8<2 EXP 64 /\
    assurance_canonical48(val(ra:int64)) /\ ~(ra=word 0x22001120) /\
    read RIP s=word 0x22001120 /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=ra /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\
    read DF s=F /\ ~bit 18(read rflags s) /\ e5_normal_flags s /\
    assurance_canonical48(val(read ABI_FS_BASE a)) /\
    fb_file_code lib_file /\ clw_file_code lib_file /\
    fb_full_image lib_file lib_rw lib_padding m /\
    c2_file_code client_file /\
    c2_full_image client_file client_rw client_padding m /\
    c2_loaded_code s /\ c2_got s /\
    (!addr. lw_image_domain addr ==>
       rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
       (wp addr <=> lw_image_write addr)) /\
    (!addr. c2_image_domain addr ==>
       rp addr /\ ordinary addr /\
       (xp addr <=> c2_image_execute addr) /\
       (wp addr <=> c2_image_write addr)) /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val q) n /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val p) n /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer-32) 32 /\
    assurance_span_ok (\a. wp a /\ ordinary a) (val stackpointer-32) 32 /\
    assurance_span_ok (\a. rp a /\ ordinary a) (val stackpointer) 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x22003fd0 8 /\
    assurance_span_ok (\a. rp a /\ ordinary a) 0x22003fd8 8 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001120 59 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001030 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x22001040 6 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x10241840 95 /\
    assurance_span_ok (\a. xp a /\ ordinary a) 0x102417d0 97 /\
    (!addr. ~(assurance_region p n addr /\
               c2_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region q n addr /\
               c2_scratch stackpointer addr)) /\
    (!addr. ~(assurance_region p n addr /\
               assurance_region stackpointer 8 addr))`;;
let c2_scalar_post = new_definition
 `c2_scalar_post stackpointer ra p q n m (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=(if c2_equal m p q n then word 1 else word 0) /\
    (c2_equal m p q n
       ==> !i. i<n ==> read memory t (word_add p (word i))=word 0) /\
    (!addr. ~((c2_equal m p q n /\ assurance_region p n (val addr)) \/
               c2_scratch stackpointer (val addr))
            ==> read memory t addr=m addr) /\
    read (memory :> bytes64 stackpointer) t=ra /\
    read RBX t=read RBX s /\ read RBP t=read RBP s /\
    read R12 t=read R12 s /\ read R13 t=read R13 s /\
    read R14 t=read R14 s /\ read R15 t=read R15 s /\
    read DF t=F /\ c2_loaded_code t /\ c2_got t /\
    c2_frame stackpointer p q n m s t`;;
let c2_public_post = new_definition
 `c2_public_post stackpointer ra p q n m s a
    (t:x86state#abi_omitted_state) <=>
    c2_scalar_post stackpointer ra p q n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)`;;
let c2_step_policy = new_definition
 `c2_step_policy stackpointer p q n m rp wp xp ordinary
    (remaining:num) (source:x86state) (target:x86state) <=>
    assurance_step_policy
      (c2_allowed_read rp ordinary stackpointer p q n)
      (c2_allowed_write wp ordinary stackpointer p q n m)
      (c2_allowed_fetch xp ordinary) source target /\
    (remaining=1 ==> assurance_actual_ret 1 source target) /\
    abi_all_decodes_caller_scalar source`;;
(* Phase predicates expose concrete handoff obligations. They are endpoints
   to prove; neither is an entry hypothesis or a substituted callee stub. *)
let c2_segment_policy = new_definition
 `c2_segment_policy stackpointer p q n m rp wp xp ordinary
    (remaining:num) (source:x86state) (target:x86state) <=>
    assurance_step_policy
      (c2_allowed_read rp ordinary stackpointer p q n)
      (c2_allowed_write wp ordinary stackpointer p q n m)
      (c2_allowed_fetch xp ordinary) source target /\
    abi_all_decodes_caller_scalar source`;;
let c2_saved_prefix = new_definition
 `c2_saved_prefix stackpointer p q n m (s:x86state) t <=>
    read RBX t=p /\ read RBP t=word n /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) t=read R12 s /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) t=read RBP s /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) t=read RBX s /\
    (!addr. ~c2_scratch stackpointer (val addr)
            ==> read memory t addr=m addr) /\
    (!i. i<n ==> read memory t (word_add p (word i))=m(word_add p (word i))) /\
    (!i. i<n ==> read memory t (word_add q (word i))=m(word_add q (word i))) /\
    c2_loaded_code t /\ c2_got t`;;
let c2_prefix_frame = new_definition
 `c2_prefix_frame stackpointer =
    MAYCHANGE [RIP;RSP;RBX;RBP;R12] ,, MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]`;;
let c2_crypto_ready = new_definition
 `c2_crypto_ready lib_file stackpointer p q n m rp (wp:num->bool) xp
    ordinary (s:x86state) a (t:x86state) <=>
    bp_e2_crypto_public_pre lib_file (read memory t) (read memory t)
      (word_sub stackpointer (word 32)) (word 0x22001132) p q n
      (read memory t) rp xp ordinary (t,a) /\
    c2_saved_prefix stackpointer p q n m s t /\
    read R12 t=word 0 /\ c2_prefix_frame stackpointer s t`;;
