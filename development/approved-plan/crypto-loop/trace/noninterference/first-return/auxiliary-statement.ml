let crypto_first_ret_execution_equivalent_statement =
 `!trace (s:x86state) t.
    crypto_first_ret_execution trace s t <=>
    crypto_observed_execution trace s t /\ crypto_ret_shape trace`;;
