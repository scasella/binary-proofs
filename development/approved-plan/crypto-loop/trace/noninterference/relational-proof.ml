needs "/work/development/approved-plan/crypto-loop/trace/noninterference/callable-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/helpers-proof.ml";;
needs "/work/development/approved-plan/contract/crypto-pre-v2.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/e2-statement.ml";;
let CRYPTO_OBSERVATION_E2 = prove
 (crypto_observation_e2_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_crypto_pre] THEN STRIP_TAC THEN
  MATCH_MP_TAC CRYPTO_OBSERVATION_MONO THEN
  EXISTS_TAC `\s':x86state. read RIP s'=returnaddress /\
    read RSP s'=word_add stackpointer (word 8) /\
    read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN ITAUT_TAC;
    MATCH_MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`s:x86state`]
      CRYPTO_OBSERVATION_CALLABLE) THEN ASM_REWRITE_TAC[]]);;
let CRYPTO_OBSERVATION_RELATIONAL = prove
 (crypto_observation_relational_statement,
  MESON_TAC[CRYPTO_OBSERVATION_E2]);;
let CRYPTO_OBSERVATION_ALL_PAIRS = prove
 (crypto_observation_all_pairs_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
   `p:int64`;`q:int64`;`n:num`;`m1:int64->byte`;`m2:int64->byte`;
   `rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s1:x86state`;`s2:x86state`]
   CRYPTO_OBSERVATION_RELATIONAL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `trace1=crypto_public_call pc p q n stackpointer returnaddress`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`crypto_public_call pc p q n stackpointer returnaddress`;
      `\s':x86state. read RIP s'=returnaddress /\ read RSP s'=word_add stackpointer (word 8)`;
      `s1:x86state`;`trace1:(int64#num#instruction#uarch_event list)list`;`t1:x86state`]
      CRYPTO_OBSERVATION_EXECUTION_EXACT) THEN
    ASM_REWRITE_TAC[CRYPTO_OBSERVATION_CALL_LENGTH] THEN ITAUT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `trace2=crypto_public_call pc p q n stackpointer returnaddress`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`crypto_public_call pc p q n stackpointer returnaddress`;
      `\s':x86state. read RIP s'=returnaddress /\ read RSP s'=word_add stackpointer (word 8)`;
      `s2:x86state`;`trace2:(int64#num#instruction#uarch_event list)list`;`t2:x86state`]
      CRYPTO_OBSERVATION_EXECUTION_EXACT) THEN
    ASM_REWRITE_TAC[CRYPTO_OBSERVATION_CALL_LENGTH] THEN ITAUT_TAC;
    ASM_REWRITE_TAC[]]);;
print_endline "CRYPTO_OBSERVATION_RELATIONAL_COMPLETE";;
