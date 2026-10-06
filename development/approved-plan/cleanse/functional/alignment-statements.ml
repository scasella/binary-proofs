(* Frozen public arithmetic prefix contract before proof search. All first-hit
   conditions below refer only to the initial address and a natural count. *)
let cleanse_functional_low3_statement =
 `!p i. val(p:int64)+i<2 EXP 64 ==>
      val(word_and (word_add p (word i)) (word 7):int64)=(val p+i) MOD 8`;;
let cleanse_functional_alignment_statement =
 `!pc p n a.
    a<8 /\ a<=n /\ n<2 EXP 64 /\ val(p:int64)+a<2 EXP 64 /\
    (val p+a) MOD 8=0 /\
    (!i. i<a ==> ~((val p+i) MOD 8=0)) /\
    nonoverlapping (word pc,97) (p,a) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+48) /\ read RDI s=p /\
          read RSI s=word n /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+69) /\ read RDI s=word_add p (word a) /\
          read RSI s=word(n-a) /\ read RAX s=word 0 /\
          read(memory :> bytes(p,a))s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,a)] ,, MAYCHANGE [events])`;;
