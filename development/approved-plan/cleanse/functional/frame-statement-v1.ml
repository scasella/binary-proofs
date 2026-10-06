(* Frozen before generic modeled memory-frame discharge. *)
needs "/work/development/approved-plan/cleanse/functional/imports.ml";;
let cleanse_functional_frame_outside_statement =
 `!p n s t a.
   n<2 EXP 64 /\ val(p:int64)+n<=2 EXP 64 /\
   (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
    MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t /\
   ~(assurance_region p n (val a)) ==>
   read memory t a=read memory s a`;;
