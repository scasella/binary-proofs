(* O6: every intermediate proposition is an end-to-end continuation,
   not an unproved interface stub or added initial-state assumption. *)
let c2_shifted_segment_policy_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k remaining source target:x86state.
    1<remaining /\ c2_segment_policy stackpointer p q n m rp wp xp ordinary k source target
    ==> c2_step_policy stackpointer p q n m rp wp xp ordinary remaining source target`;;
let c2_false_header_tail_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned /\
    ~c2_equal m p q n
    ==> assurance_checked_run 5 (c2_scalar_post stackpointer ra p q n m initial)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) returned`;;
let c2_true_cleanse_tail_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> assurance_checked_run 5 (c2_scalar_post stackpointer ra p q n m initial)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) returned`;;
let c2_true_header_tail_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned /\
    c2_equal m p q n
    ==> assurance_checked_run (4+(cleanse_functional_steps p n+5))
      (c2_scalar_post stackpointer ra p q n m initial)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) returned`;;
let c2_after_compare_tail_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> assurance_checked_run
      (if c2_equal m p q n then 12+cleanse_functional_steps p n else 8)
      (c2_scalar_post stackpointer ra p q n m initial)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) returned`;;
