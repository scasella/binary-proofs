(* O5 endpoint assumptions to derive from each actual branch. *)
let c2_suffix_pre = new_definition
 `c2_suffix_pre stackpointer ra p q n m rp wp xp ordinary (initial:x86state) (returned:x86state) <=>
    32<=val(stackpointer:int64) /\ val stackpointer+8<2 EXP 64 /\
    bytes_loaded returned (word 0x22001120) c2_caller_mc /\
    read RIP returned=(if c2_equal m p q n then word 0x22001153 else word 0x2200113a) /\
    read RSP returned=word_sub stackpointer (word 24) /\
    read R12 returned=(if c2_equal m p q n then word 1 else word 0) /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) returned=read RBX initial /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) returned=read RBP initial /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) returned=read R12 initial /\
    read (memory :> bytes64 stackpointer) returned=ra /\
    assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n)
      (val stackpointer-32) 32 /\
    assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n)
      (val stackpointer) 8 /\
    assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001120 59`;;
let c2_suffix_post = new_definition
 `c2_suffix_post stackpointer ra p q n m (initial:x86state) (returned:x86state) (t:x86state) <=>
    read RIP t=ra /\ read RSP t=word_add stackpointer (word 8) /\
    read RAX t=(if c2_equal m p q n then word 1 else word 0) /\
    read RBX t=read RBX initial /\ read RBP t=read RBP initial /\ read R12 t=read R12 initial /\
    read R13 t=read R13 returned /\ read R14 t=read R14 returned /\ read R15 t=read R15 returned /\
    read DF t=read DF returned /\ read memory t=read memory returned /\
    (MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events]) returned t`;;
