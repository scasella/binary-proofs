(* Public endpoint frame algebra only; no instruction proof or step semantics. *)
let c2_cleanse_frame_preserved_statement = `!p:int64 n s t:x86state. (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
 MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t ==> read RBX t=read RBX s /\ read RBP t=read RBP s /\ read R12 t=read R12 s /\
 read R13 t=read R13 s /\ read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`;;
let c2_cleanse_frame_slot_statement = `!p slot:int64 n s t:x86state. (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
 MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t /\ nonoverlapping(slot,8)(p,n) ==> read (memory :> bytes64 slot) t=read (memory :> bytes64 slot) s`;;
let c2_cleanse_frame_code_statement = `!p codebase:int64 n mc:byte list s t:x86state. (MAYCHANGE [RIP;RSP;RAX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS ,,
 MAYCHANGE [memory :> bytes(p,n)] ,, MAYCHANGE [events]) s t /\ nonoverlapping(codebase,LENGTH mc)(p,n) /\ bytes_loaded s codebase mc ==> bytes_loaded t codebase mc`;;
