(* Public interface frame algebra only; no callee instruction semantics. *)
let c2_crypto_public_saved_preserved_statement = `!s t:x86state.
 (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
  MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s t
 ==> read RBX t=read RBX s /\ read RBP t=read RBP s /\
     read R12 t=read R12 s /\ read R13 t=read R13 s /\
     read R14 t=read R14 s /\ read R15 t=read R15 s /\
     read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`;;
let c2_prefix_frame_slot_statement =
 `!stackpointer slot:int64 s t:x86state.
    c2_prefix_frame stackpointer s t /\
    nonoverlapping(slot,8)(word_sub stackpointer (word 32),32)
    ==> read (memory :> bytes64 slot) t=read (memory :> bytes64 slot) s`;;
let c2_prefix_frame_incoming_slot_statement =
 `!stackpointer:int64 s t:x86state.
    32<=val stackpointer /\ val stackpointer+8<=2 EXP 64 /\
    c2_prefix_frame stackpointer s t
    ==> read (memory :> bytes64 stackpointer) t=
        read (memory :> bytes64 stackpointer) s`;;
