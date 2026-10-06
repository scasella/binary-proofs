let cleanse_access_pre_permissions_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> n<2 EXP 64 /\ pc+97<=2 EXP 64 /\
        assurance_span_ok (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
          (val stackpointer) 8 /\
        assurance_span_ok (bp_e2_cleanse_allowed_write wp ordinary p n) (val p) n /\
        assurance_span_ok (bp_e2_cleanse_allowed_fetch xp ordinary pc) pc 97 /\
        nonoverlapping (word pc,97) (p,n) /\
        nonoverlapping (stackpointer,8) (p,n)`;;
