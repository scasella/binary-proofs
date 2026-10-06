(* E3-only goals, frozen before proof search. Both E2 public domains and
   endpoint predicates remain unchanged. Candidate5 supplies the only x86
   constants in this checking namespace. No caller composition is assumed. *)
let e3_scalar_qualifies_caller_statement =
 `!s:x86state. abi_all_decodes_scalar s ==> abi_all_decodes_caller_scalar s`;;
let e3_cleanse_qualifies_caller_statement =
 `!s:x86state. abi_all_decodes_cleanse_scalar s ==> abi_all_decodes_caller_scalar s`;;
let e3_run_mono_step_statement =
 `!n P C D (s:x86state).
   (!k source target. C k source target ==> D k source target) /\
   assurance_checked_run n P C s
   ==> assurance_checked_run n P D s`;;
let bp_e3_crypto_public_caller_policy_statement =
 `!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.
   bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n
     m rp xp ordinary (s,a)
   ==> assurance_checked_run (bp_assurance_call_steps n)
     (bp_assurance_call_post 0x10241840 stackpointer ra p q n
       (read events s) m s)
     (\k source target.
       assurance_zero_step
         (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
         bp_e2_crypto_allowed_write
         (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)
         k source target /\ abi_all_decodes_caller_scalar source) s`;;
let bp_e3_crypto_public_caller_interface_statement =
 `!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.
   bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n
     m rp xp ordinary (s,a)
   ==> eventually_n abi_caller_scalar_extended_step (bp_assurance_call_steps n)
     (bp_e2_crypto_public_post file_bytes initial_rw padding
       stackpointer ra p q n (read events s) m s a) (s,a)`;;
let bp_e3_cleanse_public_caller_policy_statement =
 `!file_bytes initial_rw padding stackpointer ra p n m rp wp xp ordinary s a.
   bp_e2_cleanse_public_pre file_bytes initial_rw padding stackpointer ra p n
     m rp wp xp ordinary (s,a)
   ==> assurance_checked_run (cleanse_functional_steps p n)
     (bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s)
     (\k source target.
       cleanse_access_covered_step 0x102417d0
         (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
         (bp_e2_cleanse_allowed_write wp ordinary p n)
         (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0)
         k source target /\ abi_all_decodes_caller_scalar source) s`;;
let bp_e3_cleanse_public_caller_interface_statement =
 `!file_bytes initial_rw padding stackpointer ra p n m rp wp xp ordinary s a.
   bp_e2_cleanse_public_pre file_bytes initial_rw padding stackpointer ra p n
     m rp wp xp ordinary (s,a)
   ==> eventually_n abi_caller_scalar_extended_step (cleanse_functional_steps p n)
     (bp_e2_cleanse_public_post stackpointer ra p n m s a) (s,a)`;;
