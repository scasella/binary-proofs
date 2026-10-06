(* Frozen before search: finite all-original-successor runs have actual paths. *)
let crypto_observation_execution_exists_statement =
 `!trace P s. crypto_observed_run trace P s ==>
    ?t. crypto_observed_execution trace s t /\ P t`;;
let crypto_first_ret_execution_exists_statement =
 `!trace P s. crypto_observed_run trace P s /\ crypto_ret_shape trace ==>
    ?t. crypto_first_ret_execution trace s t /\ P t`;;
let crypto_first_ret_e2_exists_statement =
 `!pc stackpointer returnaddress p q n m rp xp ordinary s.
   bp_e2_crypto_pre pc stackpointer returnaddress p q n m rp xp ordinary s ==>
   ?t. crypto_first_ret_execution
        (crypto_public_call pc p q n stackpointer returnaddress) s t /\
       read RIP t=returnaddress /\ read RSP t=word_add stackpointer (word 8)`;;
