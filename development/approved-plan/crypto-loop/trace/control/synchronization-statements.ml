let crypto_control_run_post_statement =
 `!n P Q C (s:x86state).
    assurance_checked_run n P C s /\ eventually_n x86 n Q s
    ==> assurance_checked_run n (\t. P t /\ Q t) C s`;;
let crypto_control_generic_combined_statement =
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
            read events s'=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e /\
            (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s')
      (assurance_zero_scalar_step rp (\x. F) xp) s`;;
