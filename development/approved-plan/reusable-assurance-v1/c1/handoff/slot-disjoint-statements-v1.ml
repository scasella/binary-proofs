(* Tiny exact address obligation, frozen before its proof source.
   No caller state, policy, decoded instructions or callee semantics occur. *)
let c1_crypto_slot_region_disjoint_statement =
 `!stackpointer:int64.
    16<=val stackpointer /\ val stackpointer+8<2 EXP 64 /\
    nonoverlapping(word_sub stackpointer (word 16),8)
      (word 0x10241840,95)
    ==> !addr. ~(assurance_region (word 0x10241840) 95 addr /\
         assurance_region (word_sub stackpointer (word 16)) 8 addr)`;;
