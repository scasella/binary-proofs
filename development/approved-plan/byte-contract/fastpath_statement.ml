(* Restricted n=16 actual-return helper. This adds byte-sequence meaning to
   the existing word fast-path result, not the full-domain O1 package. *)
let bp_crypto_16_bytes_statement =
 `!pc stackpointer returnaddress p q m e.
    ~(returnaddress = word pc) ==>
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [p;q;word 16] s /\ read memory s = m /\
           read events s = e)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read RAX s =
             (if (!i. i<16 ==> m(word_add p (word i)) =
                                m(word_add q (word i)))
              then word 0 else word 1) /\
           read events s = APPEND
            [EventJump(word(pc+52),returnaddress);EventLoad(stackpointer,8);
             EventLoad(word_add q (word 8),8);EventLoad(q,8);
             EventLoad(word_add p (word 8),8);EventLoad(p,8);
             EventJump(word(pc+22),word(pc+22));
             EventJump(word(pc+16),word(pc+16))] e)
      (MAYCHANGE [RIP; RSP; RAX; RDX; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events])`;;
