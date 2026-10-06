(* O3 proposition: all contents/lengths under actual machine endpoint facts. *)
let c2_branch_header_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary returned:x86state.
    bytes_loaded returned (word 0x22001120) c2_caller_mc /\
    read RIP returned=word 0x22001132 /\
    read RAX returned=(if c2_equal m p q n then word 0 else word 1) /\
    read R12 returned=word 0 /\
    assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001120 59
    ==> assurance_checked_run 3 (c2_branch_header_post p q n m returned)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) returned`;;
