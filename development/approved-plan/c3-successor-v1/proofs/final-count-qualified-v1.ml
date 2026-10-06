(* C3 fixed literal interface/count/E5 lifts. C2 lifting recipe is instantiated
   with unchanged C3 frozen targets and frozen layer exports. Requires actual
   C3_CHECKED binding from whole-caller composition. No synthetic substitute. *)
let c3_step_policy_qualified_statement =
 `!stackpointer p q:int64 n m rp wp xp ordinary k source target:x86state.
    c3_step_policy stackpointer p q n m rp wp xp ordinary k source target
    ==> abi_all_decodes_caller_scalar source`;;
let C3_STEP_POLICY_QUALIFIED = prove
 (c3_step_policy_qualified_statement,
  REWRITE_TAC[c3_step_policy] THEN MESON_TAC[]);;
let C3_PRE_NORMAL_FLAGS = prove
 (`!lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary s a.
   c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
     stackpointer ra p q n m rp wp xp ordinary (s,a)
   ==> e5_normal_flags s`,
 REWRITE_TAC[c3_pre] THEN MESON_TAC[]);;
let C3_COUNT = prove
 (c3_count_statement,REWRITE_TAC[c3_steps;bp_assurance_call_steps]);;


print_endline "C3_SUCCESSOR_FINAL_COUNT_QUALIFIED_NORMAL_ENTRY_CHECKED";;
