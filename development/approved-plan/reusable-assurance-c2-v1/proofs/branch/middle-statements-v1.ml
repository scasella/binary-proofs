(* O3/O4: handoff premise is a derived endpoint, not caller premise. *)
let c2_middle_handoff_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_middle_ready stackpointer p q n m initial returned
    ==> assurance_checked_run 4
      (c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) returned`;;
