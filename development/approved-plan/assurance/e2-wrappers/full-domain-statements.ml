let assurance_e2_call_zero_post_statement =
 `!pc stackpointer ra p q e m s.
    bp_assurance_call_post pc stackpointer ra p q 0 e m s =
    bp_assurance_zero_post pc stackpointer ra e m s`;;
let assurance_e2_call_16_post_statement =
 `!pc stackpointer ra p q e m s.
    bp_assurance_call_post pc stackpointer ra p q 16 e m s =
    bp_assurance_16_byte_post pc stackpointer ra p q e m s`;;
let assurance_e2_generic_policy_frame_statement =
 `!pc stackpointer ra p q n m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q n m rp xp ordinary s /\
    ~(n=0) /\ ~(n=16)
    ==> assurance_checked_run (7*n+10)
      (bp_assurance_call_post pc stackpointer ra p q n (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
        bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary pc)) s`;;
let assurance_e2_all_length_policy_frame_statement =
 `!pc stackpointer ra p q n m rp xp ordinary s.
    bp_e2_crypto_pre pc stackpointer ra p q n m rp xp ordinary s
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (bp_assurance_call_post pc stackpointer ra p q n (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
        bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary pc)) s`;;
let assurance_e2_all_length_extended_abi_statement =
 `!pc stackpointer ra p q n m rp xp ordinary s a.
    bp_e2_crypto_pre pc stackpointer ra p q n m rp xp ordinary s
    ==> eventually_n abi_scalar_extended_step (bp_assurance_call_steps n)
      (\t. bp_assurance_call_post pc stackpointer ra p q n (read events s) m s
             (FST t) /\ SND t = a /\
           abi_required_controls_preserved a (SND t)) (s,a)`;;
