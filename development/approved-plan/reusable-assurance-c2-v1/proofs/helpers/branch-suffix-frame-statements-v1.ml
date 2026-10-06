(* Named O3/O5 pure frame obligations; no caller offsets or supplier bodies. *)
let c2_header_frame_ac_statement = `!s t:x86state. (MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s t
 ==> bit 18(read rflags t)=bit 18(read rflags s)`;;
let c2_header_frame_before_cleanup_included_statement = `!stackpointer.
 (MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) subsumed c2_before_cleanup_frame stackpointer`;;
let c2_header_before_cleanup_compose_statement = `!stackpointer (initial:x86state) returned next.
 c2_before_cleanup_frame stackpointer initial returned /\ (MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) returned next
 ==> c2_before_cleanup_frame stackpointer initial next`;;
let c2_suffix_frame_accumulated_included_statement = `!stackpointer p q n m.
 (MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events]) subsumed c2_accumulated_frame stackpointer p q n m`;;
let c2_accumulated_suffix_compose_statement = `!stackpointer p q n m (initial:x86state) returned next.
 c2_accumulated_frame stackpointer p q n m initial returned /\ (MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events]) returned next
 ==> c2_accumulated_frame stackpointer p q n m initial next`;;
let c2_before_suffix_accumulated_compose_statement = `!stackpointer p q n m (initial:x86state) returned next.
 c2_before_cleanup_frame stackpointer initial returned /\ (MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events]) returned next
 ==> c2_accumulated_frame stackpointer p q n m initial next`;;
