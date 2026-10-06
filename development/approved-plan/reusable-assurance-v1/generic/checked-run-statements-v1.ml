let ra_checked_run_append_statement =
 `!m n P C (s:x86state).
    assurance_checked_run m (\t. assurance_checked_run n P C t)
      (\k source target. C (n+k) source target) s
    ==> assurance_checked_run (m+n) P C s`;;
let ra_checked_run_post_mono_statement =
 `!n P Q C (s:x86state).
    (!t. P t ==> Q t) /\ assurance_checked_run n P C s
    ==> assurance_checked_run n Q C s`;;
let ra_checked_run_policy_mono_statement =
 `!n P C D (s:x86state).
    (!k source target. C k source target ==> D k source target) /\
    assurance_checked_run n P C s
    ==> assurance_checked_run n P D s`;;
