(* Frozen independently before first-RET proof search. *)
let crypto_first_ret_shape_characterization_statement =
 `!trace:(int64#num#instruction#uarch_event list)list.
    crypto_ret_shape trace <=>
    ~(trace=[]) /\ crypto_observation_is_ret (LAST trace) /\
    ALL (\obs. ~crypto_observation_is_ret obs) (BUTLAST trace)`;;
let crypto_first_ret_prefix_statement =
 `!prefix suffix:(int64#num#instruction#uarch_event list)list.
    ALL (\obs. ~crypto_observation_is_ret obs) prefix /\ crypto_ret_shape suffix
    ==> crypto_ret_shape (APPEND prefix suffix)`;;
let crypto_first_ret_force_statement =
 `!public P (s:x86state) other t.
    crypto_observed_run public P s /\ crypto_ret_shape public /\
    crypto_first_ret_execution other s t
    ==> other=public /\ P t`;;
let crypto_first_ret_loop_shape_statement =
 `!n pc (p:int64) q stackpointer returnaddress.
    crypto_ret_shape (crypto_public_loop pc p q n stackpointer returnaddress)`;;
let crypto_first_ret_call_shape_statement =
 `!pc (p:int64) q n stackpointer returnaddress.
    crypto_ret_shape (crypto_public_call pc p q n stackpointer returnaddress)`;;
let crypto_first_ret_relational_statement =
 `!pc stackpointer returnaddress p q n m1 m2 rp xp ordinary
       (s1:x86state) s2 trace1 trace2 t1 t2.
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m1 rp xp ordinary s1 /\
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m2 rp xp ordinary s2 /\
    crypto_first_ret_execution trace1 s1 t1 /\
    crypto_first_ret_execution trace2 s2 t2
    ==> trace1=crypto_public_call pc p q n stackpointer returnaddress /\
        trace2=crypto_public_call pc p q n stackpointer returnaddress /\
        trace1=trace2 /\
        read RIP t1=returnaddress /\ read RSP t1=word_add stackpointer (word 8) /\
        read RIP t2=returnaddress /\ read RSP t2=word_add stackpointer (word 8)`;;
