(* Frozen same root E2 Pre and functional/frame post; explicit public exact count. *)
needs "/work/development/approved-plan/cleanse/functional/bounded/statements-v1.ml";;
let cleanse_functional_e2_bounded_statement =
 `!pc stackpointer ra p n m rp wp xp ordinary.
    ensures_n x86
     (bp_e2_cleanse_pre pc stackpointer ra p n m rp wp xp ordinary)
     (\s. read RIP s=ra /\ val(read RSP s)=val(stackpointer:int64)+8 /\
          (!i. i<n ==> read memory s (word_add p (word i))=word 0) /\
          (!a. ~(assurance_region p n (val a)) ==> read memory s a=m a))
     (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) (\s. cleanse_functional_steps p n)`;;
