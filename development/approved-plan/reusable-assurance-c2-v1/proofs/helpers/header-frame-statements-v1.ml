(* Named O3: exact nonmodified projections required by frozen header endpoint. *)
let c2_header_frame_preserved_statement = `!s t:x86state.
 (MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s t
 ==> read RSP t=read RSP s /\ read RAX t=read RAX s /\
     read RBX t=read RBX s /\ read RBP t=read RBP s /\
     read R13 t=read R13 s /\ read R14 t=read R14 s /\
     read R15 t=read R15 s /\ read DF t=read DF s /\
     read memory t=read memory s`;;
