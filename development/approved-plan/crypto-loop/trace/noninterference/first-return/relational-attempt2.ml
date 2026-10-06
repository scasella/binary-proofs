needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/force-attempt2.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/first-return/schema-attempt1.ml";;
let CRYPTO_FIRST_RET_RELATIONAL = prove
 (crypto_first_ret_relational_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
   `p:int64`;`q:int64`;`n:num`;`m1:int64->byte`;`m2:int64->byte`;
   `rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`s1:x86state`;`s2:x86state`]
   CRYPTO_OBSERVATION_RELATIONAL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`crypto_public_call pc p q n stackpointer returnaddress`;
   `\s':x86state. read RIP s'=returnaddress /\ read RSP s'=word_add stackpointer (word 8)`;
   `s1:x86state`;`trace1:(int64#num#instruction#uarch_event list)list`;`t1:x86state`]
   CRYPTO_FIRST_RET_FORCE) THEN
  ASM_REWRITE_TAC[CRYPTO_FIRST_RET_CALL_SHAPE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`crypto_public_call pc p q n stackpointer returnaddress`;
   `\s':x86state. read RIP s'=returnaddress /\ read RSP s'=word_add stackpointer (word 8)`;
   `s2:x86state`;`trace2:(int64#num#instruction#uarch_event list)list`;`t2:x86state`]
   CRYPTO_FIRST_RET_FORCE) THEN
  ASM_REWRITE_TAC[CRYPTO_FIRST_RET_CALL_SHAPE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;
print_endline "CRYPTO_FIRST_RET_RELATIONAL_ATTEMPT2_COMPLETE";;
