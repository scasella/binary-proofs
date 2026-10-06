(* All lengths, including empty and production sixteen-byte fast path. *)
let bp_assurance_call_steps = new_definition
 `bp_assurance_call_steps n = if n=0 then 6 else if n=16 then 15 else 7*n+10`;;
let bp_assurance_call_post = new_definition
 `bp_assurance_call_post pc stackpointer ra p q n e m s (s':x86state) <=>
    read RIP s' = ra /\ val(read RSP s') = val(stackpointer:int64)+8 /\
    read RAX s' = (if (!i. i<n ==> m(word_add p (word i)) =
                                  m(word_add q (word i)))
                  then word 0 else word 1) /\
    read memory s' = m /\ bytes_loaded s' (word pc) crypto_memcmp_mc /\
    read events s' = APPEND (crypto_trace_call pc p q n stackpointer ra) e /\
    (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s'`;;
