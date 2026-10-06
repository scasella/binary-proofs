let bp_assurance_16_byte_post = new_definition
 `bp_assurance_16_byte_post pc stackpointer ra p q e m s (s':x86state) <=>
    read RIP s' = ra /\ val(read RSP s') = val(stackpointer:int64)+8 /\
    read RAX s' =
      (if (!i. i<16 ==> m(word_add p (word i)) = m(word_add q (word i)))
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
