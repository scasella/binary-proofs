let bp_assurance_zero_post = new_definition
 `bp_assurance_zero_post pc stackpointer ra e m s (s':x86state) <=>
    read RIP s' = ra /\ val(read RSP s') = val(stackpointer:int64)+8 /\
    read RAX s' = word 0 /\ read memory s' = m /\
    bytes_loaded s' (word pc) crypto_memcmp_mc /\
    read events s' = APPEND
      [EventJump(word(pc+95),ra);EventLoad(stackpointer,8);
       EventJump(word(pc+16),word(pc+93))] e /\
    (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s'`;;

let bp_assurance_16_post = new_definition
 `bp_assurance_16_post pc stackpointer ra p q e m s (s':x86state) <=>
    read RIP s' = ra /\ val(read RSP s') = val(stackpointer:int64)+8 /\
    read RAX s' =
      (if read (memory :> bytes64 p) s = read (memory :> bytes64 q) s /\
          read (memory :> bytes64 (word_add p (word 8))) s =
          read (memory :> bytes64 (word_add q (word 8))) s
       then word 0 else word 1) /\
    read memory s' = m /\ bytes_loaded s' (word pc) crypto_memcmp_mc /\
    read events s' = APPEND
      [EventJump(word(pc+52),ra);EventLoad(stackpointer,8);
       EventLoad(word_add q (word 8),8);EventLoad(q,8);
       EventLoad(word_add p (word 8),8);EventLoad(p,8);
       EventJump(word(pc+22),word(pc+22));
       EventJump(word(pc+16),word(pc+16))] e /\
    (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s'`;;
