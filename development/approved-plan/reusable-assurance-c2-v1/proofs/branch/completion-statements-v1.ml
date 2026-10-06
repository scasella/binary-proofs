(* Named O3 and O5 end-to-end phase transport; no supplier instruction inputs. *)
let c2_header_completed_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_crypto_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> assurance_checked_run 3
      (c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) returned`;;
let c2_header_initial_facts_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a t
    ==> c2_saved_prefix stackpointer p q n m initial t /\
        read RIP t=(if c2_equal m p q n then word 0x22001148 else word 0x2200113a) /\
        read RSP t=word_sub stackpointer (word 24) /\
        read R12 t=(if c2_equal m p q n then word 1 else word 0) /\
        read (memory :> bytes64 stackpointer) t=ra /\
        read R13 t=read R13 initial /\ read R14 t=read R14 initial /\
        read R15 t=read R15 initial /\ read DF t=F /\ ~bit 18(read rflags t) /\
        c2_before_cleanup_frame stackpointer initial t`;;
let c2_header_true_middle_ready_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a t /\
    c2_equal m p q n
    ==> c2_middle_ready stackpointer p q n m initial t`;;
let c2_header_false_suffix_ready_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a t /\
    ~c2_equal m p q n
    ==> c2_suffix_pre stackpointer ra p q n m rp wp xp ordinary initial t`;;
let c2_cleanse_suffix_ready_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a t
    ==> c2_suffix_pre stackpointer ra p q n m rp wp xp ordinary initial t`;;
