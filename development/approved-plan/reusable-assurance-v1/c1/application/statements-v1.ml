(* Frozen C1 supplier application and access-policy helpers.
   Uses only the public Crypto contract and generic checked-run reasoning. *)
let c1_app_event_policy_mono_statement =
 `!rp0 wp0 rp wp e:uarch_event.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    assurance_event_policy rp0 wp0 e
    ==> assurance_event_policy rp wp e`;;
let c1_app_all_policy_mono_statement =
 `!P Q d:uarch_event list.
    (!e. P e ==> Q e) /\ ALL P d ==> ALL Q d`;;
let c1_app_step_policy_mono_statement =
 `!rp0 wp0 xp0 rp wp xp source target:x86state.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    (!addr. xp0 addr ==> xp addr) /\
    assurance_step_policy rp0 wp0 xp0 source target
    ==> assurance_step_policy rp wp xp source target`;;
let c1_crypto_read_inclusion_statement =
 `!stackpointer p q:int64 n rp ordinary addr.
    bp_e2_crypto_allowed_read rp ordinary p q n
      (word_sub stackpointer (word 16)) addr
    ==> c1_allowed_read rp ordinary stackpointer p q n addr`;;
let c1_crypto_write_inclusion_statement =
 `!stackpointer:int64 wp ordinary addr.
    bp_e2_crypto_allowed_write addr
    ==> c1_allowed_write wp ordinary stackpointer addr`;;
let c1_crypto_fetch_inclusion_statement =
 `!xp ordinary addr.
    bp_e2_crypto_allowed_fetch xp ordinary 0x10241840 addr
    ==> c1_allowed_fetch xp ordinary addr`;;
let c1_crypto_interface_application_statement =
 `!lib_file stackpointer p q:int64 n m rp xp ordinary initial a entry:x86state.
    c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 16))
        (word 0x21001119) p q n (read events entry) (read memory entry) entry)
      (\k source target.
        assurance_zero_step
          (bp_e2_crypto_allowed_read rp ordinary p q n
            (word_sub stackpointer (word 16)))
          bp_e2_crypto_allowed_write
          (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
          k source target /\ abi_all_decodes_caller_scalar source) entry`;;
let c1_crypto_policy_widen_statement =
 `!stackpointer p q:int64 n rp wp xp ordinary remaining source target:x86state.
    assurance_zero_step
      (bp_e2_crypto_allowed_read rp ordinary p q n
        (word_sub stackpointer (word 16)))
      bp_e2_crypto_allowed_write
      (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
      remaining source target /\ abi_all_decodes_caller_scalar source
    ==> c1_segment_policy stackpointer p q n rp wp xp ordinary
          remaining source target`;;
let c1_crypto_segment_application_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 16))
        (word 0x21001119) p q n (read events entry) (read memory entry) entry)
      (c1_segment_policy stackpointer p q n rp wp xp ordinary) entry`;;
