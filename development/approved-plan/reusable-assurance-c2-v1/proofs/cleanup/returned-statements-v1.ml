(* O4/O5 required opaque-interface transport: literal goal before construction. *)
let c2_cleanse_returned_facts_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a returned
    ==> c2_equal m p q n /\ read RIP returned=word 0x22001153 /\
        read RSP returned=word_sub stackpointer (word 24) /\
        read R12 returned=word 1 /\
        read (memory :> bytes64 (word_sub stackpointer (word 8))) returned=read R12 initial /\
        read (memory :> bytes64 (word_sub stackpointer (word 16))) returned=read RBP initial /\
        read (memory :> bytes64 (word_sub stackpointer (word 24))) returned=read RBX initial /\
        read (memory :> bytes64 stackpointer) returned=ra /\
        (!i. i<n ==> read memory returned (word_add p (word i))=word 0) /\
        (!addr. ~(assurance_region p n (val addr) \/ c2_scratch stackpointer (val addr))
          ==> read memory returned addr=m addr) /\
        read R13 returned=read R13 initial /\ read R14 returned=read R14 initial /\
        read R15 returned=read R15 initial /\ read DF returned=F /\
        c2_loaded_code returned /\ c2_got returned /\
        c2_accumulated_frame stackpointer p q n m initial returned`;;
