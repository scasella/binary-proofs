(* Named O5 projection from the exact frozen suffix frame.
   New C2-specific adapter; no code offsets, supplier bodies or changed generic rule. *)
let c2_suffix_frame_preserved_statement =
 `!returned t:x86state.
    (MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events]) returned t
    ==> read R13 t=read R13 returned /\
        read R14 t=read R14 returned /\
        read R15 t=read R15 returned /\
        read DF t=read DF returned /\
        read memory t=read memory returned`;;
