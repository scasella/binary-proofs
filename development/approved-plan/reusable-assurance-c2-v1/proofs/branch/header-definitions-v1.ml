(* Named O3: actual three-instruction TEST/SET/JE header. Endpoint only. *)
let c2_branch_header_post = new_definition
 `c2_branch_header_post p q n m (returned:x86state) (t:x86state) <=>
    read RIP t=(if c2_equal m p q n then word 0x22001148 else word 0x2200113a) /\
    read R12 t=(if c2_equal m p q n then word 1 else word 0) /\
    read RSP t=read RSP returned /\ read RAX t=read RAX returned /\
    read RBX t=read RBX returned /\ read RBP t=read RBP returned /\
    read R13 t=read R13 returned /\ read R14 t=read R14 returned /\ read R15 t=read R15 returned /\
    read DF t=read DF returned /\ read memory t=read memory returned /\
    (MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) returned t`;;
