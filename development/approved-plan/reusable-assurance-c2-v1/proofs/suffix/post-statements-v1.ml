(* O5: frozen caller postcondition from actual branch and suffix endpoints. *)
let c2_final_stack_value_statement =
 `!stackpointer:int64 t:x86state.
    val stackpointer+8<2 EXP 64 /\ read RSP t=word_add stackpointer (word 8)
    ==> val(read RSP t)=val stackpointer+8`;;
let c2_false_suffix_scalar_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    ~c2_equal m p q n /\
    c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned /\
    c2_suffix_post stackpointer ra p q n m initial returned t
    ==> c2_scalar_post stackpointer ra p q n m initial t`;;
let c2_true_suffix_scalar_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned t:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned /\
    c2_suffix_post stackpointer ra p q n m initial returned t
    ==> c2_scalar_post stackpointer ra p q n m initial t`;;
