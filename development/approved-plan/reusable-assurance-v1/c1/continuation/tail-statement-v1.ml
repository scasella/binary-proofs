let c1_tail_checked_statement =
 `!stackpointer ra result current p q n rp wp xp ordinary s.
    c1_tail_pre stackpointer ra result current p q n rp wp xp ordinary s
    ==> assurance_checked_run 5
      (c1_tail_post stackpointer ra result current s)
      (c1_step_policy stackpointer p q n rp wp xp ordinary) s`;;
