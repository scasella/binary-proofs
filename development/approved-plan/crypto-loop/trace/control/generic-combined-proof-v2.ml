needs "/work/development/approved-plan/crypto-loop/trace/control/exec-rule.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/schema.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/run-post-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/run-mono-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/generic-scalar-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/return-proof.ml";;
let CRYPTO_CONTROL_GENERIC_COMBINED = prove
 (crypto_control_generic_combined_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `assurance_checked_run (7*n+10)
      (\s'. read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc)
      (assurance_zero_scalar_step rp (\x. F) xp) s`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
      `xp:num->bool`;`s:x86state`] CRYPTO_CONTROL_GENERIC_SCALAR) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eventually_n x86 (7*n+10)
      (\s'. (read RIP s'=returnaddress /\
            read RSP s'=word_add stackpointer (word 8) /\
            read RAX s'=(if (!j. j<n ==> (m:int64->byte)(word_add p (word j))=(m:int64->byte)(word_add q (word j)))
                        then word 0 else word 1) /\
            read events s'=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e) /\
            (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s') s`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pc:num`;`stackpointer:int64`;`returnaddress:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`e:uarch_event list`]
      CRYPTO_BOUNDED_GENERIC_RETURN) THEN
    ASM_REWRITE_TAC[ensures_n] THEN
    DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CRYPTO_CONTROL_RUN_MONO THEN
  EXISTS_TAC
   `\s':x86state.
     (read RIP s'=returnaddress /\
      read RSP s'=word_add stackpointer (word 8) /\
      read memory s'=m /\ bytes_loaded s' (word pc) crypto_memcmp_mc) /\
     ((read RIP s'=returnaddress /\
       read RSP s'=word_add stackpointer (word 8) /\
       read RAX s'=(if (!j. j<n ==> (m:int64->byte)(word_add p (word j))=(m:int64->byte)(word_add q (word j)))
                   then word 0 else word 1) /\
       read events s'=APPEND (crypto_trace_call pc p q n stackpointer returnaddress) e) /\
       (MAYCHANGE [RIP;RSP;RAX;RDI;RSI;RDX;R10;R11] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s s')` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN ITAUT_TAC;
    MATCH_MP_TAC CRYPTO_CONTROL_RUN_POST THEN ASM_REWRITE_TAC[]]);;
print_endline "CRYPTO_CONTROL_GENERIC_COMBINED_COMPLETE";;
