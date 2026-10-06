(* Actual observed execution ending at its FIRST decoded RET. No step count,
   comparison-result, memory equality or convenient successor choice is assumed. *)
let crypto_observation_is_ret = new_definition
 `crypto_observation_is_ret (obs:int64#num#instruction#uarch_event list) <=>
    FST(SND(SND obs)) = RET`;;
let crypto_first_ret_execution = new_definition
 `crypto_first_ret_execution trace (s:x86state) t <=>
    ~(trace=[]) /\ crypto_observed_execution trace s t /\
    crypto_observation_is_ret (LAST trace) /\
    ALL (\obs. ~crypto_observation_is_ret obs) (BUTLAST trace)`;;
(* Recursive characterization used only to prove the explicit relation above. *)
let crypto_ret_shape = new_recursive_definition list_RECURSION
 `(crypto_ret_shape [] <=> F) /\
  (crypto_ret_shape (CONS (obs:int64#num#instruction#uarch_event list) rest) <=>
     if crypto_observation_is_ret obs then rest=[] else crypto_ret_shape rest)`;;
