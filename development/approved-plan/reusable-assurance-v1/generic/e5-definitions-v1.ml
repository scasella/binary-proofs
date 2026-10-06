(* E5 normal-entry/RF retirement refinement. New constants only; E2/E3 unchanged. *)
let e5_normal_flags = new_definition
 `e5_normal_flags (s:x86state) <=>
    ~bit 16 (read rflags s) /\ ~bit 8 (read rflags s)`;;
let e5_rf_clear = new_definition
 `e5_rf_clear (s:x86state) = write (rflags :> bitelement 16) F s`;;
let e5_rf_retired_step = new_definition
 `e5_rf_retired_step (s:x86state) t <=>
    ?u. x86 s u /\ t=e5_rf_clear u`;;
let e5_rf_retired_extended_step = new_definition
 `e5_rf_retired_extended_step (s:x86state,a:abi_omitted_state) t <=>
    ?u b. abi_caller_scalar_extended_step (s,a) (u,b) /\
          t=(e5_rf_clear u,b)`;;
let e5_normal_step_policy = new_definition
 `e5_normal_step_policy (C:num->x86state->x86state->bool) k s t <=>
    C k s t /\ e5_normal_flags s /\ e5_normal_flags t`;;
let e5_normal_environment = new_definition
 `e5_normal_environment long_mode cpl (dr7:int64) cet_enabled
      external_event_delivered debug_agent_modified <=>
    long_mode /\ cpl=3 /\
    (!i. i<8 ==> ~bit i dr7) /\ ~cet_enabled /\
    ~external_event_delivered /\ ~debug_agent_modified`;;
let e5_rf_checked_run = new_recursive_definition num_RECURSION
 `(e5_rf_checked_run 0 (P:x86state->bool)
      (C:num->x86state->x86state->bool) s <=> P s) /\
  (e5_rf_checked_run (SUC n) P C s <=>
     (?t. e5_rf_retired_step s t) /\
     !t. e5_rf_retired_step s t ==> C (SUC n) s t /\
                                      e5_rf_checked_run n P C t)`;;
