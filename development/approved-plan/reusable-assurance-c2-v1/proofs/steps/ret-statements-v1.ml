(* Named O5 obligation: original RET transition establishes actual return.
   Statement frozen before its proof source; no caller trace theorem. *)
let c2_original_ret_statement =
 `!pc s t:x86state.
   read RIP s=word pc /\ x86_decode s (word pc) (1,RET) /\ x86 s t
   ==> assurance_actual_ret 1 s t`;;
let c2_segment_to_final_policy_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k source target:x86state.
   c2_segment_policy stackpointer p q n m rp wp xp ordinary k source target /\
   (k=1 ==> assurance_actual_ret 1 source target)
   ==> c2_step_policy stackpointer p q n m rp wp xp ordinary k source target`;;
