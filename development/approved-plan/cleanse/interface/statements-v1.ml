(* No callee correctness, permission invariant or preserved-state fact is an
   entry assumption. Each policy step quantifies over every original successor,
   with progress, full data/fetch footprint and the final actual RET. *)
let bp_e2_cleanse_policy_frame_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> assurance_checked_run (cleanse_functional_steps p n)
      (bp_e2_cleanse_call_post pc stackpointer ra p n m s)
      (\k source target.
        cleanse_access_covered_step pc
          (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
          (bp_e2_cleanse_allowed_write wp ordinary p n)
          (bp_e2_cleanse_allowed_fetch xp ordinary pc) k source target /\
        abi_all_decodes_cleanse_scalar source) s`;;
let bp_e2_cleanse_extended_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state) a.
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> eventually_n abi_cleanse_scalar_extended_step (cleanse_functional_steps p n)
      (\t. bp_e2_cleanse_call_post pc stackpointer ra p n m s (FST t) /\
           SND t=a /\ abi_required_controls_preserved a (SND t)) (s,a)`;;
let bp_e2_cleanse_public_policy_statement =
 `!file_bytes initial_rw padding stackpointer ra p n m rp wp xp ordinary s a.
    bp_e2_cleanse_public_pre file_bytes initial_rw padding stackpointer ra p n
      m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (cleanse_functional_steps p n)
      (bp_e2_cleanse_call_post 0x102417d0 stackpointer ra p n m s)
      (\k source target.
        cleanse_access_covered_step 0x102417d0
          (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
          (bp_e2_cleanse_allowed_write wp ordinary p n)
          (bp_e2_cleanse_allowed_fetch xp ordinary 0x102417d0) k source target /\
        abi_all_decodes_cleanse_scalar source) s`;;
let bp_e2_cleanse_public_interface_statement =
 `!file_bytes initial_rw padding stackpointer ra p n m rp wp xp ordinary s a.
    bp_e2_cleanse_public_pre file_bytes initial_rw padding stackpointer ra p n
      m rp wp xp ordinary (s,a)
    ==> eventually_n abi_cleanse_scalar_extended_step (cleanse_functional_steps p n)
      (bp_e2_cleanse_public_post stackpointer ra p n m s a) (s,a)`;;
let bp_e2_cleanse_public_witness_bridge_statement =
 `!file_bytes initial_rw padding image p n high_first.
    clw_file_code file_bytes /\
    clw_full_pre file_bytes initial_rw padding image p n high_first
    ==> bp_e2_cleanse_public_pre file_bytes initial_rw padding
      (word 0x300008) (word 0x400000) p n (clw_memory image p n high_first)
      (clw_read p n) (clw_write p n) lw_execute (clw_ordinary p n)
      (clw_machine image p n high_first)`;;
