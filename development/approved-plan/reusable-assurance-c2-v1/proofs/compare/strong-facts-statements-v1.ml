(* Named O3/O5 initial-snapshot/public-comparison frame consequence. *)
let c2_compare_strong_facts_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> c2_saved_prefix stackpointer p q n m initial returned /\
        read (memory :> bytes64 stackpointer) returned=
          read (memory :> bytes64 stackpointer) initial /\
        read R13 returned=read R13 initial /\ read R14 returned=read R14 initial /\
        read R15 returned=read R15 initial /\ read DF returned=F /\
        ~bit 18(read rflags returned) /\
        c2_before_cleanup_frame stackpointer initial returned`;;
