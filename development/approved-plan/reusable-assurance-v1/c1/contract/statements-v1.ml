(* Literal end-theorems and actual three-step handoff, frozen before proof search. *)
let c1_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c1_steps n)
      (c1_scalar_post stackpointer ra p q n m s)
      (c1_step_policy stackpointer p q n rp wp xp ordinary) s`;;
let c1_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c1_steps n)
      (c1_public_post stackpointer ra p q n m s a) (s,a)`;;
let c1_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c1_steps n)
      (\t. c1_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c1_step_policy stackpointer p q n rp wp xp ordinary)) s`;;
let c1_rf_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c1_steps n)
      (\t. c1_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c1_step_policy stackpointer p q n rp wp xp ordinary)) s`;;
let c1_normal_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c1_steps n)
      (\t. c1_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)`;;
let c1_handoff_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 3
      (c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary s a)
      (c1_segment_policy stackpointer p q n rp wp xp ordinary) s`;;
let c1_count_statement =
 `!n. c1_steps n = 8 +
    (if n=0 then 6 else if n=16 then 15 else 7*n+10)`;;
