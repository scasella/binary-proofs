(* Independently frozen callable interface. The initialized image is bound
   only at entry. A legal destination may overlap writable library pages.
   file_bytes denotes the acquired production ELF through an explicit trusted
   acquisition boundary. The public symbol is load_bias+0x2417d0. *)
let bp_e2_cleanse_call_post = new_definition
 `bp_e2_cleanse_call_post pc stackpointer ra p n m (s:x86state) (t:x86state) <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    (!i. i<n ==> read memory t (word_add p (word i))=word 0) /\
    (!a. ~assurance_region p n (val a) ==> read memory t a=m a) /\
    bytes_loaded t (word pc) openssl_cleanse_mc /\
    read (memory :> bytes64 stackpointer) t=ra /\
    (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t`;;
let bp_e2_cleanse_public_pre = new_definition
 `bp_e2_cleanse_public_pre file_bytes initial_rw padding stackpointer ra p n
                          m rp wp xp ordinary (s:x86state,a:abi_omitted_state) <=>
    clw_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding m /\
    bp_e2_cleanse_pre 0x102417d0 stackpointer ra p n m rp wp xp ordinary s /\
    (!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\
       (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)) /\
    assurance_canonical48 (val(read ABI_FS_BASE a))`;;
let bp_e2_cleanse_public_post = new_definition
 `bp_e2_cleanse_public_post stackpointer ra p n m s a
                           (t:x86state#abi_omitted_state) <=>
    bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s (FST t) /\
    SND t=a /\ abi_required_controls_preserved a (SND t)`;;
