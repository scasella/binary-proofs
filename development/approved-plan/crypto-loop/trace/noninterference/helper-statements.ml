let crypto_observation_unique_statement =
 `!s obs1 obs2 (s':x86state).
    assurance_observed_step s obs1 s' /\ assurance_observed_step s obs2 s'
    ==> obs1=obs2`;;
let crypto_observation_mono_statement =
 `!trace P Q (s:x86state).
    (!t. P t ==> Q t) /\ crypto_observed_run trace P s
    ==> crypto_observed_run trace Q s`;;
let crypto_observation_project_statement =
 `!trace P (s:x86state).
    crypto_observed_run trace P s ==> eventually_n x86 (LENGTH trace) P s`;;
let crypto_observation_execution_exact_statement =
 `!trace P (s:x86state) other t.
    crypto_observed_run trace P s /\ LENGTH other=LENGTH trace /\
    crypto_observed_execution other s t
    ==> other=trace /\ P t`;;
let crypto_observation_loop_length_statement =
 `!n pc (p:int64) q stackpointer returnaddress.
    LENGTH(crypto_public_loop pc p q n stackpointer returnaddress)=7*n+3`;;
let crypto_observation_call_length_statement =
 `!pc (p:int64) q n stackpointer returnaddress.
    LENGTH(crypto_public_call pc p q n stackpointer returnaddress)=
      (if n=0 then 6 else if n=16 then 15 else 7*n+10)`;;
