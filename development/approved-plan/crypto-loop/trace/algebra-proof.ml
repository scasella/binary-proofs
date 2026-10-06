let CRYPTO_TRACE_PREFIX_POS = prove
 (`!pc p q n i. 0<i ==>
    crypto_trace_prefix pc p q n i =
    APPEND
      [EventJump(word(pc+86),if i=n then word(pc+86) else word(pc+64));
       EventLoad(word_add q (word(i-1)),1);EventLoad(word_add p (word(i-1)),1)]
      (crypto_trace_prefix pc p q n (i-1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `i=SUC(i-1)` SUBST1_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[crypto_trace_prefix;ARITH_RULE `SUC k-1=k`]);;
let CRYPTO_TRACE_PC_DISTINCT = prove
 (`!pc. ~((word(pc+64):int64)=word(pc+84)) /\
        ~((word(pc+84):int64)=word(pc+64))`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG_ADD_LCANCEL_EQ;CONG] THEN CONV_TAC NUM_REDUCE_CONV);;
print_endline "CRYPTO_TRACE_ALGEBRA_COMPLETE";;
