(* Frozen before main access/control proof search. No length cap. *)
let cleanse_access_byte_return_statement =
 `!n pc stackpointer ra p rp wp xp (s:x86state).
    0<n /\ cleanse_access_loop_pre pc 19 stackpointer ra p n rp wp xp s
    ==> assurance_checked_run (4*n+1)
      (cleanse_access_return_post pc stackpointer ra)
      (cleanse_access_covered_step pc rp wp xp) s`;;
let cleanse_access_tail_return_statement =
 `!r pc stackpointer ra p rp wp xp (s:x86state).
    r<8 /\ cleanse_access_loop_pre pc 89 stackpointer ra p r rp wp xp s
    ==> assurance_checked_run (4*r+3)
      (cleanse_access_return_post pc stackpointer ra)
      (cleanse_access_covered_step pc rp wp xp) s`;;
let cleanse_access_bulk_return_statement =
 `!k r pc stackpointer ra p rp wp xp (s:x86state).
    0<k /\ r<8 /\
    cleanse_access_loop_pre pc 69 stackpointer ra p (8*k+r) rp wp xp s
    ==> assurance_checked_run (5*k+4*r+3)
      (cleanse_access_return_post pc stackpointer ra)
      (cleanse_access_covered_step pc rp wp xp) s`;;
let cleanse_access_alignment_return_statement =
 `!a k r pc stackpointer ra p rp wp xp (s:x86state).
    a<8 /\ 0<k /\ r<8 /\ val(p:int64)+a<2 EXP 64 /\
    (val p+a) MOD 8=0 /\ (!i. i<a ==> ~((val p+i) MOD 8=0)) /\
    cleanse_access_loop_pre pc 48 stackpointer ra p (a+8*k+r) rp wp xp s
    ==> assurance_checked_run (6*a+5*k+4*r+5)
      (cleanse_access_return_post pc stackpointer ra)
      (cleanse_access_covered_step pc rp wp xp) s`;;
let cleanse_access_all_length_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary (s:x86state).
    bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary s
    ==> assurance_checked_run (cleanse_access_count p n)
      (cleanse_access_return_post pc stackpointer ra)
      (cleanse_access_covered_step pc
        (bp_e2_cleanse_allowed_read rp ordinary stackpointer)
        (bp_e2_cleanse_allowed_write wp ordinary p n)
        (bp_e2_cleanse_allowed_fetch xp ordinary pc)) s`;;
