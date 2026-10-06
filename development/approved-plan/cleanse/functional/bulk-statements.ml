(* Frozen before all-count 8-byte bulk proof search. No alignment assumption:
   this modeled component is true for unaligned stores as well. *)
let cleanse_functional_bulk_mask_statement =
 `!k. k<2 EXP 64 ==>
      (val(word_and (word k) (word 18446744073709551608):int64)=0 <=> k<8)`;;
let cleanse_functional_prefix_read64_statement =
 `!s p i. read(memory :> bytes(p:int64,i))(s:x86state)=0 /\
           read(memory :> bytes64(word_add p (word i)))s=word 0 ==>
           read(memory :> bytes(p,i+8))s=0`;;
let cleanse_functional_bulk_loop_statement =
 `!pc p k r.
    0<k /\ r<8 /\ 8*k+r<2 EXP 64 /\ nonoverlapping (word pc,97) (p,8*k) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+69) /\ read RDI s=p /\
          read RSI s=word(8*k+r) /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+89) /\ read RDI s=word_add p (word(8*k)) /\
          read RSI s=word r /\ read RAX s=word 0 /\
          read(memory :> bytes(p,8*k))s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,8*k)] ,, MAYCHANGE [events])`;;
