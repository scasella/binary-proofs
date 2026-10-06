(* Same generic transition bridge as assurance/path.ml; no routine behavior. *)
let crypto_observation_actual_bridge_statement =
 `!len inst s s'.
    x86_decode s (read RIP s) (len,inst) /\ x86 s s'
    ==> assurance_observed_step s
          (assurance_observation s len inst s') s'`;;
