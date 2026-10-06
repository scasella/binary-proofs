(* Independent targets, frozen before observation proof search. *)
let crypto_observation_body7_statement =
 `!pc p q count m (s:x86state).
    0<count /\ count<2 EXP 64 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word(pc+64) /\ read RDI s=p /\ read RSI s=q /\
    read RDX s=word count /\ read memory s=m
    ==> crypto_observed_run (crypto_public_body7 pc p q count)
      (\s'. read RIP s'=(if count=1 then word(pc+86) else word(pc+64)) /\
            read RDI s'=word_add p (word 1) /\
            read RSI s'=word_add q (word 1) /\
            read RDX s'=word(count-1) /\ read memory s'=m /\
            bytes_loaded s' (word pc) crypto_memcmp_mc) s`;;
let crypto_observation_loop_statement =
 `!n pc stackpointer returnaddress p q m (s:x86state).
    0<n /\ n<2 EXP 64 /\
    bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word(pc+64) /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=returnaddress /\
    read RDI s=p /\ read RSI s=q /\ read RDX s=word n /\ read memory s=m
    ==> crypto_observed_run (crypto_public_loop pc p q n stackpointer returnaddress)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc) s`;;
let crypto_observation_callable_statement =
 `!pc stackpointer returnaddress p q n m (s:x86state).
    n<2 EXP 64 /\ bytes_loaded s (word pc) crypto_memcmp_mc /\
    read RIP s=word pc /\ read RSP s=stackpointer /\
    read (memory :> bytes64 stackpointer) s=returnaddress /\
    C_ARGUMENTS [p;q;word n] s /\ read memory s=m
    ==> crypto_observed_run (crypto_public_call pc p q n stackpointer returnaddress)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc) s`;;
let crypto_observation_relational_statement =
 `!pc stackpointer returnaddress p q n m1 m2 rp xp ordinary (s1:x86state) s2.
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m1 rp xp ordinary s1 /\
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m2 rp xp ordinary s2
    ==> crypto_observed_run (crypto_public_call pc p q n stackpointer returnaddress)
          (\s'. read RIP s'=returnaddress /\
                read RSP s'=word_add stackpointer (word 8)) s1 /\
        crypto_observed_run (crypto_public_call pc p q n stackpointer returnaddress)
          (\s'. read RIP s'=returnaddress /\
                read RSP s'=word_add stackpointer (word 8)) s2`;;
let crypto_observation_all_pairs_statement =
 `!pc stackpointer returnaddress p q n m1 m2 rp xp ordinary
       (s1:x86state) s2 trace1 trace2 t1 t2.
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m1 rp xp ordinary s1 /\
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m2 rp xp ordinary s2 /\
    LENGTH trace1=(if n=0 then 6 else if n=16 then 15 else 7*n+10) /\
    LENGTH trace2=(if n=0 then 6 else if n=16 then 15 else 7*n+10) /\
    crypto_observed_execution trace1 s1 t1 /\
    crypto_observed_execution trace2 s2 t2
    ==> trace1=crypto_public_call pc p q n stackpointer returnaddress /\
        trace2=crypto_public_call pc p q n stackpointer returnaddress /\
        trace1=trace2`;;
