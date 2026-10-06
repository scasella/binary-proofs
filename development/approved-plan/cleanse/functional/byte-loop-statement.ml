let cleanse_functional_byte_loop_expected =
 `!pc p n.
    0<n /\ n<2 EXP 64 /\ nonoverlapping (word pc,97) (p,n) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+19) /\ read RDI s=p /\
          read RSI s=word n /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+31) /\ read RDI s=word_add p (word n) /\
          read RSI s=word 0 /\ read RAX s=word 0 /\
          read (memory :> bytes(p,n)) s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events])`;;
