(* E2 fixed post-initialization public-entry interface, definition V1.
   This narrows loading/environment state, never the universal input domain.
   file_bytes is the entire pinned production ELF's acquired byte map;
   its acquisition interpretation is an explicit trusted boundary. The
   actual public symbol is load_bias+0x241840 = 0x10241840. *)
let bp_e2_crypto_public_pre = new_definition
 `bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n
                         m rp xp ordinary (s:x86state,a:abi_omitted_state) <=>
    fb_file_code file_bytes /\ fb_full_image file_bytes initial_rw padding m /\
    bp_e2_crypto_pre 0x10241840 stackpointer ra p q n m rp xp ordinary s /\
    (!addr. lw_image_domain addr
       ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr)) /\
    assurance_canonical48 (val(read ABI_FS_BASE a))`;;
let bp_e2_crypto_public_post = new_definition
 `bp_e2_crypto_public_post file_bytes initial_rw padding stackpointer ra p q n
                          e m s a (t:x86state#abi_omitted_state) <=>
    bp_assurance_call_post 0x10241840 stackpointer ra p q n e m s (FST t) /\
    fb_full_image file_bytes initial_rw padding (read memory (FST t)) /\
    SND t = a /\ abi_required_controls_preserved a (SND t)`;;
