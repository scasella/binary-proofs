(* Frozen before original loop/control search. The body permits its endpoint
   pointers to wrap: spans constrain only the one byte read before increment. *)
let crypto_control_body7_statement =
 `!pc p q count m e rp xp (s:x86state).
    0<count /\ count<2 EXP 64 /\ pc+95<=2 EXP 64 /\
    assurance_span_ok xp pc 95 /\
    assurance_span_ok rp (val(p:int64)) 1 /\
    assurance_span_ok rp (val(q:int64)) 1 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word(pc+64) /\ read RDI s=p /\ read RSI s=q /\
    read RDX s=word count /\ read memory s=m /\ read events s=e
    ==> assurance_checked_run 7
      (\s'. read RIP s'=(if count=1 then word(pc+86) else word(pc+64)) /\
            read RDI s'=word_add p (word 1) /\
            read RSI s'=word_add q (word 1) /\
            read RDX s'=word(count-1) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc /\
            read events s'=APPEND
             [EventJump(word(pc+86),if count=1 then word(pc+86) else word(pc+64));
              EventLoad(q,1);EventLoad(p,1)] e)
      (\remaining a b. assurance_step_policy rp (\x. F) xp a b) s`;;
let crypto_control_generic_statement =
 `!pc stackpointer returnaddress p q n m e rp xp (s:x86state).
    0<n /\ n<2 EXP 64 /\ ~(n=16) /\ pc+95<=2 EXP 64 /\
    assurance_span_ok xp pc 95 /\
    assurance_span_ok rp (val(p:int64)) n /\
    assurance_span_ok rp (val(q:int64)) n /\
    assurance_span_ok rp (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word pc /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=returnaddress /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\ read events s=e
    ==> assurance_checked_run (7*n+10)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read RAX s'=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                        then word 0 else word 1) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc /\
            read events s'=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e)
      (assurance_zero_step rp (\x. F) xp) s`;;
