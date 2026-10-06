(* O2/O3 intermediate predicate; not an added caller premise or interface stub. *)
let c2_crypto_completed = new_definition
 `c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary
    (initial:x86state) a (returned:x86state) <=>
    ?entry:x86state.
      c2_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
      bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 32))
        (word 0x22001132) p q n (read events entry) (read memory entry) entry returned`;;
