(* Independently frozen exact finite-count successors; original x86, unchanged functional frames. *)
needs "/work/development/approved-plan/cleanse/functional/components-v3.ml";;
needs "/work/development/approved-plan/cleanse/functional/composition-statements.ml";;
let cleanse_functional_steps = new_definition
 `cleanse_functional_steps (p:int64) n =
   if n<15 then 4*n+7 else
   let a=(8-val p MOD 8) MOD 8 in
   9+6*a+5*((n-a) DIV 8)+4*((n-a) MOD 8)`;;
let cleanse_functional_bounded_byte_statement =
 `!pc p n.
    0<n /\ n<2 EXP 64 /\ nonoverlapping (word pc,97) (p,n) ==>
    ensures_n x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+19) /\ read RDI s=p /\
          read RSI s=word n /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+31) /\ read RDI s=word_add p (word n) /\
          read RSI s=word 0 /\ read RAX s=word 0 /\
          read (memory :> bytes(p,n)) s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) (\s. 4*n)`;;
let cleanse_functional_bounded_bulk_statement =
 `!pc p k r.
    0<k /\ r<8 /\ 8*k+r<2 EXP 64 /\ nonoverlapping (word pc,97) (p,8*k) ==>
    ensures_n x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+69) /\ read RDI s=p /\
          read RSI s=word(8*k+r) /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+89) /\ read RDI s=word_add p (word(8*k)) /\
          read RSI s=word r /\ read RAX s=word 0 /\
          read(memory :> bytes(p,8*k))s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,8*k)] ,, MAYCHANGE [events]) (\s. 5*k)`;;
let cleanse_functional_bounded_alignment_statement =
 `!pc p n a.
    a<8 /\ a<=n /\ n<2 EXP 64 /\ val(p:int64)+a<2 EXP 64 /\
    (val p+a) MOD 8=0 /\
    (!i. i<a ==> ~((val p+i) MOD 8=0)) /\
    nonoverlapping (word pc,97) (p,a) ==>
    ensures_n x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word(pc+48) /\ read RDI s=p /\
          read RSI s=word n /\ read RAX s=word 0)
     (\s. read RIP s=word(pc+69) /\ read RDI s=word_add p (word a) /\
          read RSI s=word(n-a) /\ read RAX s=word 0 /\
          read(memory :> bytes(p,a))s=0)
     (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,a)] ,, MAYCHANGE [events]) (\s. 6*a+2)`;;
let cleanse_functional_bounded_bulk_tail_statement =
 `!pc p k r.
   0<k /\ r<8 /\ 8*k+r<2 EXP 64 /\ val(p:int64)+(8*k+r)<=2 EXP 64 /\
   nonoverlapping (word pc,97) (p,8*k+r) ==>
   ensures_n x86
    (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
         read RIP s=word(pc+69) /\ read RDI s=p /\
         read RSI s=word(8*k+r) /\ read RAX s=word 0)
    (\s. (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
         read RDI s=word_add p (word(8*k+r)) /\
         read RSI s=word 0 /\ read RAX s=word 0 /\
         read(memory :> bytes(p,8*k+r))s=0)
    (MAYCHANGE [RIP;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [memory :> bytes(p,8*k+r)] ,, MAYCHANGE [events]) (\s. 5*k+4*r+2)`;;
let cleanse_functional_bounded_core_statement =
 `!pc p n.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    nonoverlapping (word pc,97) (p,n) ==>
    ensures_n x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word pc /\ C_ARGUMENTS [p;word n] s)
     (\s. (read RIP s=word(pc+31) \/ read RIP s=word(pc+95)) /\
          read RDI s=word_add p (word n) /\ read RSI s=word 0 /\
          read RAX s=word 0 /\ read(memory :> bytes(p,n))s=0)
     (MAYCHANGE [RIP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) (\s. cleanse_functional_steps p n-1)`;;
let cleanse_functional_bounded_callable_statement =
 `!pc stackpointer ra p n.
    n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
    nonoverlapping (word pc,97) (p,n) /\ nonoverlapping (stackpointer,8) (p,n) ==>
    ensures_n x86
     (\s. bytes_loaded s (word pc) openssl_cleanse_mc /\
          read RIP s=word pc /\ read RSP s=stackpointer /\
          read(memory :> bytes64 stackpointer)s=ra /\ C_ARGUMENTS [p;word n] s)
     (\s. read RIP s=ra /\ read RSP s=word_add stackpointer (word 8) /\
          read(memory :> bytes(p,n))s=0)
     (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) (\s. cleanse_functional_steps p n)`;;
