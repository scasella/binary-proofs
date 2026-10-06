(* Intermediate tail predicate. Derived from the original caller precondition
   and unchanged public callee post; it is not a new caller entry premise. *)
let c1_tail_pre = new_definition
 `c1_tail_pre stackpointer ra result current p q n rp wp xp ordinary
    (s:x86state) <=>
    (result:int64=word 0 \/ result=word 1) /\
    16<=val(stackpointer:int64) /\ val stackpointer+8<2 EXP 64 /\
    bytes_loaded s (word 0x21001110) c1_crypto_caller_mc /\
    read RIP s=word 0x21001119 /\
    read RSP s=word_sub stackpointer (word 8) /\ read RAX s=result /\
    read memory s=current /\ read(memory :> bytes64 stackpointer)s=ra /\
    assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
      (val stackpointer) 8 /\
    assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001110 22`;;
let c1_tail_post = new_definition
 `c1_tail_post stackpointer ra result current (s:x86state) t <=>
    read RIP t=ra /\ val(read RSP t)=val(stackpointer:int64)+8 /\
    read RAX t=(if result=word 0 then word 1 else word 0) /\
    read memory t=current /\
    (MAYCHANGE [RIP;RSP;RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s t`;;
