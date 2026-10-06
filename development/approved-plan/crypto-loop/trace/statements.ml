(* Independently frozen before search. These statements concern original
   modeled load/store/jump events, not fetch coverage or all-step policy. *)
let crypto_trace_loop_statement =
 `!pc p q n m e.
    0<n /\ n<2 EXP 64 ==>
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s=word(pc+64) /\ C_ARGUMENTS [p;q;word n] s /\
           read RAX s=word 0 /\ read R10 s=word 0 /\
           read memory s=m /\ read events s=e)
      (\s. read RIP s=word(pc+93) /\
           read RAX s=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                       then word 0 else word 1) /\
           read events s=APPEND (crypto_trace_prefix pc p q n n) e)
      (MAYCHANGE [RIP;RAX;RDI;RSI;RDX;R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;
let crypto_trace_callable_statement =
 `!pc stackpointer returnaddress p q n m e.
    n<2 EXP 64 /\ ~(returnaddress=word pc) ==>
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s=word pc /\ read RSP s=stackpointer /\
           read (memory :> bytes64 stackpointer) s=returnaddress /\
           C_ARGUMENTS [p;q;word n] s /\ read memory s=m /\ read events s=e)
      (\s. read RIP s=returnaddress /\
           read RSP s=word_add stackpointer (word 8) /\
           read RAX s=(if (!j. j<n ==> m(word_add p (word j))=m(word_add q (word j)))
                       then word 0 else word 1) /\
           read events s=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e)
      (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;
let crypto_trace_prefix_access_statement =
 `!pc p q n i. i<=n ==>
    memaccess_inbounds (crypto_trace_prefix pc p q n i) [(p,n);(q,n)] []`;;
let crypto_trace_call_access_statement =
 `!pc p q n stackpointer returnaddress.
    memaccess_inbounds (crypto_trace_call pc p q n stackpointer returnaddress)
      [(p,n);(q,n);(stackpointer,8)] []`;;
