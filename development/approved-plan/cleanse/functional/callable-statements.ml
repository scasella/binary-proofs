(* Frozen before whole callable search. The whole E2 contract remains root spec-v2. *)
let cleanse_alignment_count = new_definition
 `cleanse_alignment_count (p:int64)=(8-val p MOD 8) MOD 8`;;
let cleanse_functional_alignment_count_statement =
 `!v. let a=(8-v MOD 8) MOD 8 in
      a<8 /\ (v+a) MOD 8=0 /\ (!i. i<a ==> ~((v+i) MOD 8=0))`;;
let cleanse_functional_core_statement =
 `!pc p n.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    nonoverlapping (word pc,97) (p,n) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word pc /\ C_ARGUMENTS [p;word n] s)
     (\s. (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
          read RDI s=word_add p (word n) /\ read RSI s=word 0 /\
          read RAX s=word 0 /\ read(memory :> bytes(p,n))s=0)
     (MAYCHANGE [RIP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events])`;;
let cleanse_functional_callable_statement =
 `!pc stackpointer ra p n.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    nonoverlapping (word pc,97) (p,n) /\ nonoverlapping (stackpointer,8) (p,n) ==>
    ensures x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word pc /\ read RSP s=stackpointer /\
          read(memory :> bytes64 stackpointer)s=ra /\ C_ARGUMENTS [p;word n] s)
     (\s. read RIP s=ra /\ read RSP s=word_add stackpointer (word 8) /\
          read(memory :> bytes(p,n))s=0)
     (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events])`;;
