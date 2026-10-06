(* Exact composition helpers, frozen before proof source.
   Existing caller entry and end definitions remain unchanged. *)
let c1_tail_frame_included_statement =
 `!stackpointer:int64.
    (MAYCHANGE [RIP;RSP;RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])
    subsumed c1_frame stackpointer`;;
let c1_tail_frame_compose_statement =
 `!stackpointer:int64 initial returned final:x86state.
    c1_frame stackpointer initial returned /\
    (MAYCHANGE [RIP;RSP;RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) returned final
    ==> c1_frame stackpointer initial final`;;
let c1_completed_tail_pre_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a returned
    ==> c1_tail_pre stackpointer ra (read RAX returned) (read memory returned)
      p q n rp wp xp ordinary returned`;;
let c1_completed_tail_post_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned final:x86state.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a returned /\
    c1_tail_post stackpointer ra (read RAX returned) (read memory returned) returned final
    ==> c1_scalar_post stackpointer ra p q n m initial final`;;
let c1_shifted_segment_policy_statement =
 `!stackpointer p q:int64 n rp wp xp ordinary offset k source target:x86state.
    5<=offset /\ c1_segment_policy stackpointer p q n rp wp xp ordinary k source target
    ==> c1_step_policy stackpointer p q n rp wp xp ordinary (offset+k) source target`;;
let c1_step_policy_qualified_statement =
 `!stackpointer p q:int64 n rp wp xp ordinary k source target:x86state.
    c1_step_policy stackpointer p q n rp wp xp ordinary k source target
    ==> abi_all_decodes_caller_scalar source`;;
let c1_completed_tail_run_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q:int64 n m rp wp xp ordinary initial a returned:x86state.
    c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
    c1_crypto_completed lib_file stackpointer p q n m rp xp ordinary initial a returned
    ==> assurance_checked_run 5 (c1_scalar_post stackpointer ra p q n m initial)
      (c1_step_policy stackpointer p q n rp wp xp ordinary) returned`;;
