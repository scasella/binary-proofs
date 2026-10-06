(* Additive fixed-image O2 interface target, frozen before its recipe.
   Neither trace length nor returned equality nor mismatch position is public.
   Memory contents may vary, including initial writable-library data/padding.
   Both original first-RET executions and all nondeterministic choices count. *)
let bp_e2_crypto_public_trace_statement =
 `!file_bytes initial_rw1 padding1 initial_rw2 padding2 stackpointer ra p q n
       m1 m2 rp xp ordinary s1 a1 s2 a2 trace1 trace2 t1 t2.
    bp_e2_crypto_public_pre file_bytes initial_rw1 padding1 stackpointer ra
      p q n m1 rp xp ordinary (s1,a1) /\
    bp_e2_crypto_public_pre file_bytes initial_rw2 padding2 stackpointer ra
      p q n m2 rp xp ordinary (s2,a2) /\
    crypto_first_ret_execution trace1 s1 t1 /\
    crypto_first_ret_execution trace2 s2 t2
    ==> trace1=crypto_public_call 0x10241840 p q n stackpointer ra /\
        trace2=crypto_public_call 0x10241840 p q n stackpointer ra /\
        trace1=trace2 /\
        read RIP t1=ra /\ read RSP t1=word_add stackpointer (word 8) /\
        read RIP t2=ra /\ read RSP t2=word_add stackpointer (word 8)`;;
