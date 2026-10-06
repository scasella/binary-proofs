(* Independently frozen same-state arithmetic/frame composition targets. *)
needs "/work/development/approved-plan/cleanse/functional/callable-statements.ml";;
let cleanse_functional_concat_zero_statement =
 `!s p a b.
   read(memory :> bytes(p,a))s=0 /\
   read(memory :> bytes(word_add p (word a),b))s=0 ==>
   read(memory :> bytes(p,a+b))s=0`;;
let cleanse_functional_bulk_tail_statement =
 `!pc p k r.
   0<k /\ r<8 /\ 8*k+r<2 EXP 64 /\ val(p:int64)+(8*k+r)<=2 EXP 64 /\
   nonoverlapping (word pc,97) (p,8*k+r) ==>
   ensures x86
    (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
         read RIP s=word(pc+69) /\ read RDI s=p /\
         read RSI s=word(8*k+r) /\ read RAX s=word 0)
    (\s. (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
         read RDI s=word_add p (word(8*k+r)) /\
         read RSI s=word 0 /\ read RAX s=word 0 /\
         read(memory :> bytes(p,8*k+r))s=0)
    (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p,8*k+r)] ,, MAYCHANGE [events])`;;
