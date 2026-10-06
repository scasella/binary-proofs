(* The pre/post definitions are frozen independently of the proof recipe.
   All allowed lengths, contents, alignments and overlaps remain quantified.
   Policy includes progress, all original successors, every full-width data
   access and fetch, and the actual final RET transition. *)
let bp_e2_crypto_public_policy_statement =
 `!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.
    bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n
      m rp xp ordinary (s,a)
    ==> assurance_checked_run (bp_assurance_call_steps n)
      (bp_assurance_call_post 0x10241840 stackpointer ra p q n
         (read events s) m s)
      (assurance_zero_scalar_step
        (bp_e2_crypto_allowed_read rp ordinary p q n stackpointer)
        bp_e2_crypto_allowed_write
        (bp_e2_crypto_allowed_fetch xp ordinary 0x10241840)) s`;;
let bp_e2_crypto_public_interface_statement =
 `!file_bytes initial_rw padding stackpointer ra p q n m rp xp ordinary s a.
    bp_e2_crypto_public_pre file_bytes initial_rw padding stackpointer ra p q n
      m rp xp ordinary (s,a)
    ==> eventually_n abi_scalar_extended_step (bp_assurance_call_steps n)
      (bp_e2_crypto_public_post file_bytes initial_rw padding
        stackpointer ra p q n (read events s) m s a) (s,a)`;;
(* This implication connects every concrete family witness to exactly the
   public pre used by both checked interface results, not a weaker proxy. *)
let bp_e2_crypto_public_witness_bridge_statement =
 `!file_bytes initial_rw padding image p q n different.
    fb_pre file_bytes initial_rw padding image p q n different
    ==> bp_e2_crypto_public_pre file_bytes initial_rw padding
      (word 0x300008) (word 0x400000) p q n
      (lw_memory image p q n different) (fb_read p q n) lw_execute
      (fb_ordinary p q n) (fb_machine image p q n different)`;;
