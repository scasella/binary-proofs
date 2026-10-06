let BP_E2_CRYPTO_PUBLIC_TRACE = prove
 (bp_e2_crypto_public_trace_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[bp_e2_crypto_public_pre] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0x10241840`; `stackpointer:int64`; `ra:int64`;
    `p:int64`; `q:int64`; `n:num`; `m1:int64->byte`; `m2:int64->byte`;
    `rp:num->bool`; `xp:num->bool`; `ordinary:num->bool`;
    `s1:x86state`; `s2:x86state`;
    `trace1:(int64#num#instruction#uarch_event list)list`;
    `trace2:(int64#num#instruction#uarch_event list)list`;
    `t1:x86state`; `t2:x86state`] CRYPTO_FIRST_RET_RELATIONAL) THEN
  ASM_REWRITE_TAC[]);;
