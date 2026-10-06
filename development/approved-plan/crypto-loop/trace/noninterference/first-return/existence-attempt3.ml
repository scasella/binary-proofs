needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/relational-attempt2.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/existence-statements.ml";;
let CRYPTO_OBSERVATION_EXECUTION_EXISTS = prove
 (crypto_observation_execution_exists_statement,
  LIST_INDUCT_TAC THEN REWRITE_TAC[crypto_observed_run;crypto_observed_execution] THEN
  ASM_MESON_TAC[]);;
let CRYPTO_FIRST_RET_EXECUTION_EXISTS = prove
 (crypto_first_ret_execution_exists_statement,
  REWRITE_TAC[CRYPTO_FIRST_RET_EXECUTION_EQUIVALENT] THEN
  MESON_TAC[CRYPTO_OBSERVATION_EXECUTION_EXISTS]);;
let CRYPTO_FIRST_RET_E2_EXISTS = prove
 (crypto_first_ret_e2_exists_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
    `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`s:x86state`] CRYPTO_OBSERVATION_E2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`crypto_public_call pc p q n stackpointer returnaddress`;
    `\t:x86state. read RIP t=returnaddress /\ read RSP t=word_add stackpointer (word 8)`;
    `s:x86state`] CRYPTO_FIRST_RET_EXECUTION_EXISTS) THEN
  ASM_REWRITE_TAC[CRYPTO_FIRST_RET_CALL_SHAPE]);;
print_endline "CRYPTO_FIRST_RET_EXISTENCE_ATTEMPT3_COMPLETE";;
