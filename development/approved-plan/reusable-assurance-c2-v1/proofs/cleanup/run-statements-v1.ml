(* O4: opaque supplier composition from an actual caller-derived handoff. *)
let c2_cleanse_segment_application_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
    ==> assurance_checked_run (cleanse_functional_steps p n)
      (bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer (word 32))
        (word 0x22001153) p n (read memory entry) entry)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
let c2_cleanse_completed_run_statement =
 `!lib_file stackpointer p q:int64 n m rp wp xp ordinary initial a entry:x86state.
    c2_cleanse_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry
    ==> assurance_checked_run (cleanse_functional_steps p n)
      (c2_cleanse_completed lib_file stackpointer p q n m rp wp xp ordinary initial a)
      (c2_segment_policy stackpointer p q n m rp wp xp ordinary) entry`;;
