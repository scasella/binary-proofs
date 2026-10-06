let crypto_observation_e2_statement =
 `!pc stackpointer returnaddress p q n m rp xp ordinary (s:x86state).
    bp_e2_crypto_pre pc stackpointer returnaddress p q n m rp xp ordinary s
    ==> crypto_observed_run (crypto_public_call pc p q n stackpointer returnaddress)
          (\s'. read RIP s'=returnaddress /\
                read RSP s'=word_add stackpointer (word 8)) s`;;
