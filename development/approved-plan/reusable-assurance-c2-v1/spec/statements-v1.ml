(* Literal end-theorems and actual eight-step CRYPTO handoff, frozen before proof search. *)
let c2_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c2_steps p q n m)
      (c2_scalar_post stackpointer ra p q n m s)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) s`;;
let c2_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n abi_caller_scalar_extended_step (c2_steps p q n m)
      (c2_public_post stackpointer ra p q n m s a) (s,a)`;;
let c2_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run (c2_steps p q n m)
      (\t. c2_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c2_step_policy stackpointer p q n m rp wp xp ordinary)) s`;;
let c2_rf_normal_checked_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> e5_rf_checked_run (c2_steps p q n m)
      (\t. c2_scalar_post stackpointer ra p q n m s t /\ e5_normal_flags t)
      (e5_normal_step_policy
        (c2_step_policy stackpointer p q n m rp wp xp ordinary)) s`;;
let c2_normal_interface_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> eventually_n e5_rf_retired_extended_step (c2_steps p q n m)
      (\t. c2_public_post stackpointer ra p q n m s a t /\
           e5_normal_flags(FST t)) (s,a)`;;
let c2_handoff_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary s a.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (s,a)
    ==> assurance_checked_run 8
      (c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary s a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) s`;;
let c2_count_statement =
 `!p q n m. c2_steps p q n m =
    if c2_equal m p q n
    then 20 + (if n=0 then 6 else if n=16 then 15 else 7*n+10)
            + cleanse_functional_steps p n
    else 16 + (if n=0 then 6 else if n=16 then 15 else 7*n+10)`;;
