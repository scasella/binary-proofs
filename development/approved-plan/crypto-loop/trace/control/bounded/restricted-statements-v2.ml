(* Exact bounded restricted components, frozen before tactic search. *)
let crypto_bounded_zero_statement =
 `!pc stackpointer returnaddress p q e.
    ~(returnaddress = word pc) ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [p;q;word 0] s /\ read events s = e)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read RAX s = word 0 /\
           read events s = APPEND
            [EventJump(word(pc+95),returnaddress);EventLoad(stackpointer,8);
             EventJump(word(pc+16),word(pc+93))] e)
      (MAYCHANGE [RIP; RSP; RAX; R10] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events]) (\s.6)`;;
let crypto_bounded_16_statement =
 `!pc stackpointer returnaddress p q a0 a1 b0 b1 e.
    ~(returnaddress = word pc) ==>
    ensures_n x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [p;q;word 16] s /\
           read (memory :> bytes64 p) s = a0 /\
           read (memory :> bytes64 (word_add p (word 8))) s = a1 /\
           read (memory :> bytes64 q) s = b0 /\
           read (memory :> bytes64 (word_add q (word 8))) s = b1 /\
           read events s = e)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read RAX s = (if a0 = b0 /\ a1 = b1 then word 0 else word 1) /\
           read events s = APPEND
            [EventJump(word(pc+52),returnaddress);EventLoad(stackpointer,8);
             EventLoad(word_add q (word 8),8);EventLoad(q,8);
             EventLoad(word_add p (word 8),8);EventLoad(p,8);
             EventJump(word(pc+22),word(pc+22));
             EventJump(word(pc+16),word(pc+16))] e)
      (MAYCHANGE [RIP; RSP; RAX; RDX; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events]) (\s.15)`;;
