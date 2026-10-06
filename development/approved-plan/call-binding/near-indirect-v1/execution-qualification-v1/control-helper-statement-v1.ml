let r1_eventually_n_one_statement =
 `!P s. eventually_n x86 1 P s <=>
   (?t. x86 s t) /\ (!t. x86 s t ==> P t)`;;
