(* Public endpoint/frame algebra only. No supplier body or execution rule. *)
let c1_crypto_public_frame = new_definition
 `c1_crypto_public_frame =
    MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;
let c1_crypto_completed = new_definition
 `c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary
    (initial:x86state) a (returned:x86state) <=>
    ?entry:x86state.
      c1_crypto_ready lib_file stackpointer p q n m rp xp ordinary initial a entry /\
      bp_assurance_call_post 0x10241840 (word_sub stackpointer (word 16))
        (word 0x21001119) p q n (read events entry) (read memory entry) entry returned`;;
