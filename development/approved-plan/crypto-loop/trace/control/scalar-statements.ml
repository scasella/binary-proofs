(* Safety/control helper is intentionally separate from the stronger frozen
   functional+event full-count target. No final full-O1 target is weakened. *)
let crypto_control_loop_scalar_statement =
 `!n pc stackpointer returnaddress p q m rp xp (s:x86state).
    0<n /\ n<2 EXP 64 /\ pc+95<=2 EXP 64 /\
    assurance_span_ok xp pc 95 /\
    assurance_span_ok rp (val(p:int64)) n /\
    assurance_span_ok rp (val(q:int64)) n /\
    assurance_span_ok rp (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word(pc+64) /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=returnaddress /\
    read RDI s=p /\ read RSI s=q /\ read RDX s=word n /\ read memory s=m
    ==> assurance_checked_run (7*n+3)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc)
      (assurance_zero_scalar_step rp (\x. F) xp) s`;;
let crypto_control_generic_scalar_statement =
 `!pc stackpointer returnaddress p q n m rp xp (s:x86state).
    0<n /\ n<2 EXP 64 /\ ~(n=16) /\ pc+95<=2 EXP 64 /\
    assurance_span_ok xp pc 95 /\
    assurance_span_ok rp (val(p:int64)) n /\
    assurance_span_ok rp (val(q:int64)) n /\
    assurance_span_ok rp (val(stackpointer:int64)) 8 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word pc /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=returnaddress /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m
    ==> assurance_checked_run (7*n+10)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc)
      (assurance_zero_scalar_step rp (\x. F) xp) s`;;
