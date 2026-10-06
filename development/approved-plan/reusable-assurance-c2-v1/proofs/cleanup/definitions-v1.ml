(* O3/O4 handoff endpoint to prove, not an added entry premise. *)
let c2_cleanse_ready = new_definition
 `c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary
    (initial:x86state) a (entry:x86state) <=>
    c2_equal m p q n /\
    bp_e2_cleanse_public_pre lib_file (read memory entry) (read memory entry)
      (word_sub stackpointer (word 32)) (word 0x22001153) p n
      (read memory entry) rp wp xp ordinary (entry,a) /\
    c2_saved_prefix stackpointer p q n m initial entry /\
    read R12 entry=word 1 /\
    read (memory :> bytes64 stackpointer) entry=
      read (memory :> bytes64 stackpointer) initial /\
    c2_before_cleanup_frame stackpointer initial entry`;;
let c2_cleanse_completed = new_definition
 `c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary
    (initial:x86state) a (returned:x86state) <=>
    ?entry:x86state.
      c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
      bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer (word 32))
        (word 0x22001153) p n (read memory entry) entry returned`;;
