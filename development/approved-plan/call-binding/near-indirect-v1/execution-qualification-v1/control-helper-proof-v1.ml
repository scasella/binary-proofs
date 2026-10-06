let R1_EVENTUALLY_N_ONE = prove
 (r1_eventually_n_one_statement,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x86`;`P:x86state->bool`;`0`;`s:x86state`] EVENTUALLY_N_STEP) THEN
  REWRITE_TAC[ADD_CLAUSES;EVENTUALLY_N_TRIVIAL]);;
