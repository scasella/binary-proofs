let e5_rf_clear_identity_statement =
 `!s:x86state. ~bit 16 (read rflags s) ==> e5_rf_clear s=s`;;
let e5_scalar_operation_outside_flags_statement =
 `!inst s t:x86state k.
 k<64 /\ ~MEM k [0;2;4;6;7;11] /\
 abi_caller_scalar_instruction inst /\ x86_execute inst s t
 ==> bit k (read rflags t)=bit k (read rflags s)`;;
let e5_qualified_step_outside_flags_statement =
 `!s t:x86state k.
 k<64 /\ ~MEM k [0;2;4;6;7;11] /\
 abi_all_decodes_caller_scalar s /\ x86 s t
 ==> bit k (read rflags t)=bit k (read rflags s)`;;
let e5_qualified_step_normal_statement =
 `!s t:x86state. e5_normal_flags s /\
 abi_all_decodes_caller_scalar s /\ x86 s t ==> e5_normal_flags t`;;
let e5_rf_retired_step_normal_eq_statement =
 `!s t:x86state. e5_normal_flags s /\ abi_all_decodes_caller_scalar s
 ==> (e5_rf_retired_step s t <=> x86 s t)`;;
let e5_rf_retired_extended_normal_eq_statement =
 `!s t:x86state a b:abi_omitted_state.
 e5_normal_flags s /\ abi_all_decodes_caller_scalar s
 ==> (e5_rf_retired_extended_step (s,a) (t,b) <=>
      abi_caller_scalar_extended_step (s,a) (t,b))`;;
let e5_checked_run_normal_statement =
 `!n P C s:x86state.
 (!k source target. C k source target ==> abi_all_decodes_caller_scalar source) /\
 assurance_checked_run n P C s /\ e5_normal_flags s
 ==> assurance_checked_run n (\t. P t /\ e5_normal_flags t)
       (e5_normal_step_policy C) s`;;
let e5_rf_checked_run_normal_statement =
 `!n P C s:x86state.
 (!k source target. C k source target ==> abi_all_decodes_caller_scalar source) /\
 assurance_checked_run n P C s /\ e5_normal_flags s
 ==> e5_rf_checked_run n (\t. P t /\ e5_normal_flags t)
       (e5_normal_step_policy C) s`;;
let e5_normal_checked_run_extended_lift_statement =
 `!n P C s:x86state a:abi_omitted_state.
 (!k source target. C k source target ==> abi_all_decodes_caller_scalar source) /\
 assurance_checked_run n P C s /\ e5_normal_flags s
 ==> eventually_n e5_rf_retired_extended_step n
       (\t. P(FST t) /\ e5_normal_flags(FST t) /\ SND t=a /\
            abi_required_controls_preserved a (SND t)) (s,a)`;;
