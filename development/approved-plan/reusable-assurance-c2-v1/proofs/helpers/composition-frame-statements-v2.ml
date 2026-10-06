(* Named O3 prefix/opaquecomparison effect composition; O5 restoration. *)
let c2_prefix_outside_saved_preserved_statement =
 `!stackpointer:int64 s t:x86state. c2_prefix_frame stackpointer s t
    ==> read R13 t=read R13 s /\ read R14 t=read R14 s /\
        read R15 t=read R15 s /\ read DF t=read DF s /\
        bit 18(read rflags t)=bit 18(read rflags s)`;;
let c2_before_cleanup_frame_idempotent_statement =
 `!stackpointer. (c2_before_cleanup_frame stackpointer ,,
    c2_before_cleanup_frame stackpointer)=c2_before_cleanup_frame stackpointer`;;
let c2_prefix_before_cleanup_included_statement =
 `!stackpointer. c2_prefix_frame stackpointer subsumed
    c2_before_cleanup_frame stackpointer`;;
let c2_crypto_before_cleanup_included_statement =
 `!stackpointer. c2_crypto_public_frame subsumed
    c2_before_cleanup_frame stackpointer`;;
let c2_before_cleanup_frame_compose_statement =
 `!stackpointer (initial:x86state) entry returned.
    c2_prefix_frame stackpointer initial entry /\
    c2_crypto_public_frame entry returned
    ==> c2_before_cleanup_frame stackpointer initial returned`;;
let c2_before_cleanup_accumulated_included_statement =
 `!stackpointer p q n m. c2_before_cleanup_frame stackpointer subsumed
    c2_accumulated_frame stackpointer p q n m`;;
let c2_frame_cancel_component_statement = `!c:(A,B)component R:A->A->bool s t.
 extensionally_valid_component c /\
 (!u v. R u v ==> read c v=read c u) /\
 (R ,, MAYCHANGE [c]) s t /\ read c t=read c s
 ==> R s t`;;
let c2_restored_frame_tail_statement = `!stackpointer p q n m. c2_accumulated_frame stackpointer p q n m =
 ((c2_frame stackpointer p q n m ,, MAYCHANGE [RBX]) ,, MAYCHANGE [RBP]) ,, MAYCHANGE [R12]`;;
let c2_main_frame_saved_preserved_statement = `!stackpointer p q n m s t. c2_frame stackpointer p q n m (s:x86state) t
 ==> read RBX t=read RBX s /\ read RBP t=read RBP s /\ read R12 t=read R12 s`;;
let c2_restored_frame_narrow_statement = `!stackpointer p q n m s t. c2_accumulated_frame stackpointer p q n m (s:x86state) t /\
 read RBX t=read RBX s /\ read RBP t=read RBP s /\ read R12 t=read R12 s
 ==> c2_frame stackpointer p q n m s t`;;
