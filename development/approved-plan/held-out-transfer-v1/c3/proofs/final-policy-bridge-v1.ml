(* Named C3 end obligation: the actual final transition must be RET.
 This is only a local unfolding of the frozen C3 final/segment policies. *)
let C3_FINAL_POLICY_BRIDGE = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary remaining source target:x86state.
 c3_segment_policy stackpointer p q n m rp wp xp ordinary remaining source target /\
 (remaining=1 ==> assurance_actual_ret 1 source target)
 ==> c3_step_policy stackpointer p q n m rp wp xp ordinary remaining source target`,
 REWRITE_TAC[c3_segment_policy;c3_step_policy] THEN MESON_TAC[]);;
print_endline "C3_FINAL_POLICY_BRIDGE_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
