let crypto_control_run_mono_statement =
 `!n P Q C (s:x86state).
    (!t. P t ==> Q t) /\ assurance_checked_run n P C s
    ==> assurance_checked_run n Q C s`;;
