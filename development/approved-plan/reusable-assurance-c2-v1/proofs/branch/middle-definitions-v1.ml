(* O3/O4: derived true-branch endpoint and actual four-step handoff frame.
   These are intermediate endpoints to prove, not additional C2 entry premises. *)
let c2_middle_frame = new_definition
 `c2_middle_frame stackpointer =
    MAYCHANGE [RIP;RSP;RDI;RSI] ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)] ,,
    MAYCHANGE [events]`;;
let c2_middle_ready = new_definition
 `c2_middle_ready stackpointer p q n m (initial:x86state) (returned:x86state) <=>
    c2_equal m p q n /\
    c2_saved_prefix stackpointer p q n m initial returned /\
    read RIP returned=word 0x22001148 /\
    read RSP returned=word_sub stackpointer (word 24) /\
    read R12 returned=word 1 /\
    read DF returned=F /\ ~bit 18(read rflags returned) /\
    read (memory :> bytes64 stackpointer) returned=
      read (memory :> bytes64 stackpointer) initial /\
    c2_before_cleanup_frame stackpointer initial returned`;;
