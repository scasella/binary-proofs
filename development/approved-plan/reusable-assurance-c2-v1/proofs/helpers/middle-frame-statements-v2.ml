(* Named O3/O4 frame facts for the actual true-branch handoff. Whole scratch is a conservative permitted effect; saved slots inside it require actual step facts. *)
let c2_middle_frame_byte_statement = `!stackpointer addr:int64 s t:x86state.
 32<=val stackpointer /\ ~c2_scratch stackpointer (val addr) /\
 c2_middle_frame stackpointer s t
 ==> read memory t addr = read memory s addr`;;
let c2_middle_frame_slot_statement = `!stackpointer slot:int64 s t:x86state.
 c2_middle_frame stackpointer s t /\
 nonoverlapping(slot,8)(word_sub stackpointer (word 32),32)
 ==> read (memory :> bytes64 slot) t=read (memory :> bytes64 slot) s`;;
let c2_middle_frame_incoming_slot_statement = `!stackpointer:int64 s t:x86state.
 32<=val stackpointer /\ val stackpointer+8<=2 EXP 64 /\
 c2_middle_frame stackpointer s t
 ==> read (memory :> bytes64 stackpointer) t=read (memory :> bytes64 stackpointer) s`;;
let c2_middle_frame_saved_preserved_statement = `!stackpointer:int64 s t:x86state.
 c2_middle_frame stackpointer s t
 ==> read RBX t=read RBX s /\ read RBP t=read RBP s /\
 read R12 t=read R12 s /\ read R13 t=read R13 s /\
 read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`;;
let c2_middle_before_cleanup_included_statement = `!stackpointer.
 c2_middle_frame stackpointer subsumed c2_before_cleanup_frame stackpointer`;;
let c2_middle_before_cleanup_compose_statement = `!stackpointer (initial:x86state) returned next.
 c2_before_cleanup_frame stackpointer initial returned /\
 c2_middle_frame stackpointer returned next
 ==> c2_before_cleanup_frame stackpointer initial next`;;
