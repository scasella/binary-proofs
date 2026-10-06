(* C2 O2/O4 public-interface adapters. Frozen end-theorems unchanged. *)
let c2_app_event_policy_mono_statement =
 `!rp0 wp0 rp wp e:uarch_event.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    assurance_event_policy rp0 wp0 e
    ==> assurance_event_policy rp wp e`;;
let c2_app_all_policy_mono_statement =
 `!P Q d:uarch_event list.
    (!e. P e ==> Q e) /\ ALL P d ==> ALL Q d`;;
let c2_app_step_policy_mono_statement =
 `!rp0 wp0 xp0 rp wp xp source target:x86state.
    (!addr. rp0 addr ==> rp addr) /\
    (!addr. wp0 addr ==> wp addr) /\
    (!addr. xp0 addr ==> xp addr) /\
    assurance_step_policy rp0 wp0 xp0 source target
    ==> assurance_step_policy rp wp xp source target`;;
let c2_crypto_policy_widen_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k source target:x86state.
    assurance_zero_step (bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer (word 32))) bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840) k source target /\ abi_all_decodes_caller_scalar source
    ==> c2_segment_policy stackpointer p q n m rp wp xp ordinary k source target`;;
let c2_crypto_public_policy_application_statement =
 `!lib_file stackpointer p q:int64 n rp wp xp ordinary a entry:x86state.
    bp_e2_crypto_public_pre lib_file (read memory entry) (read memory entry) (word_sub stackpointer (word 32)) (word 0x22001132) p q n (read memory entry) rp xp ordinary (entry,a)
    ==> assurance_checked_run (bp_assurance_call_steps n) (bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32)) (word 0x22001132) p q n (read events entry) (read memory entry) entry)
      ((\k source target. assurance_zero_step (bp_e2_crypto_allowed_read rp ordinary p q n (word_sub stackpointer (word 32))) bp_e2_crypto_allowed_write (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840) k source target /\ abi_all_decodes_caller_scalar source):num->x86state->x86state->bool) entry`;;
let c2_crypto_interface_application_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary a entry:x86state.
    bp_e2_crypto_public_pre lib_file (read memory entry) (read memory entry) (word_sub stackpointer (word 32)) (word 0x22001132) p q n (read memory entry) rp xp ordinary (entry,a)
    ==> assurance_checked_run (bp_assurance_call_steps n) (bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32)) (word 0x22001132) p q n (read events entry) (read memory entry) entry)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
let c2_cleanse_policy_widen_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k source target:x86state.
    c2_equal m p q n /\ cleanse_access_covered_step 0x102417d0 (bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer (word 32))) (bp_e2_cleanse_allowed_write wp ordinary p n) (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0) k source target /\ abi_all_decodes_caller_scalar source
    ==> c2_segment_policy stackpointer p q n m rp wp xp ordinary k source target`;;
let c2_cleanse_public_policy_application_statement =
 `!lib_file stackpointer p q:int64 n rp wp xp ordinary a entry:x86state.
    bp_e2_cleanse_public_pre lib_file (read memory entry) (read memory entry) (word_sub stackpointer (word 32)) (word 0x22001153) p n (read memory entry) rp wp xp ordinary (entry,a)
    ==> assurance_checked_run (cleanse_functional_steps p n) (bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer (word 32)) (word 0x22001153) p n (read memory entry) entry)
      ((\k source target. cleanse_access_covered_step 0x102417d0 (bp_e2_cleanse_allowed_read rp ordinary (word_sub stackpointer (word 32))) (bp_e2_cleanse_allowed_write wp ordinary p n) (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0) k source target /\ abi_all_decodes_caller_scalar source):num->x86state->x86state->bool) entry`;;
let c2_cleanse_interface_application_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary a entry:x86state.
    c2_equal m p q n /\ bp_e2_cleanse_public_pre lib_file (read memory entry) (read memory entry) (word_sub stackpointer (word 32)) (word 0x22001153) p n (read memory entry) rp wp xp ordinary (entry,a)
    ==> assurance_checked_run (cleanse_functional_steps p n) (bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer (word 32)) (word 0x22001153) p n (read memory entry) entry)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
