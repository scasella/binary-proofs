(* O5 actual five-step MOV/POP/POP/POP/RET, both actual binary copies. *)
let c2_suffix_statement =
 `!stackpointer ra p q:int64 n m rp wp xp ordinary initial returned:x86state.
    c2_suffix_pre stackpointer ra p q n m rp wp xp ordinary initial returned
    ==> assurance_checked_run 5 (c2_suffix_post stackpointer ra p q n m initial returned)
      (c2_step_policy stackpointer p q n m rp wp xp ordinary) returned`;;
