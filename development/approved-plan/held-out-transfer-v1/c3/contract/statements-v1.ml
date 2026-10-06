(* Literal end-theorems and actual ten-step CRYPTO handoff, frozen before proof search. *)
let c3_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (c3_scalar_post stackpointer ra p q n m s)
      (c3_step_policy stackpointer p q n m rp wp xp ordinary) s`;;
let c3_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c3_steps p q n m)
      (c3_public_post stackpointer ra p q n m s a) (s,a)`;;
let c3_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c3_steps p q n m)
      (\t. c3_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c3_step_policy stackpointer p q n m rp wp xp ordinary)) s`;;
let c3_rf_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c3_steps p q n m)
      (\t. c3_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c3_step_policy stackpointer p q n m rp wp xp ordinary)) s`;;
let c3_normal_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c3_steps p q n m)
      (\t. c3_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)`;;
let c3_handoff_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 10
      (c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a)
      (c3_segment_policy stackpointer p q n m rp wp xp ordinary) s`;;
let c3_count_statement =
 `!p q n m. c3_steps p q n m =
    (if c3_equal m p q n then 34 else 31) +
    2 * (if n=0 then 6 else if n=16 then 15 else 7*n+10) +
    cleanse_functional_steps p n`;;
