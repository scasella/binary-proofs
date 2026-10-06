(* Whole finite architectural observations over the ORIGINAL x86 relation.
   Each constructor demands progress and the same exact observation for EVERY
   original successor; it never guards or filters an execution to fit a trace. *)
let crypto_observed_run = new_recursive_definition list_RECURSION
 `(crypto_observed_run [] (P:x86state->bool) s <=> P s) /\
  (crypto_observed_run (CONS (obs:int64#num#instruction#uarch_event list) rest) P s <=>
     (?s'. x86 s s') /\
     !s'. x86 s s' ==> assurance_observed_step s obs s' /\
                         crypto_observed_run rest P s')`;;
(* A possibly nondeterministic actual observed path. This is used by the
   relational consequence to quantify all choices, not to pick a nice pair. *)
let crypto_observed_execution = new_recursive_definition list_RECURSION
 `(crypto_observed_execution [] (s:x86state) t <=> t=s) /\
  (crypto_observed_execution (CONS (obs:int64#num#instruction#uarch_event list) rest) s t <=>
     ?next. assurance_observed_step s obs next /\
            crypto_observed_execution rest next t)`;;
