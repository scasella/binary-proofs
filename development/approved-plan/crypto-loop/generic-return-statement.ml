let crypto_dev_generic_return_statement =
 `!pc stackpointer returnaddress p q n m.
    0<n /\ n<2 EXP 64 /\ ~(n=16) ==>
    ensures x86
      (\s. bytes_loaded s (word pc) crypto_memcmp_mc /\
           read RIP s = word pc /\ read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [p;q;word n] s /\ read memory s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read RAX s =
             (if (!j. j<n ==> m(word_add p (word j)) = m(word_add q (word j)))
              then word 0 else word 1))
      (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`;;
