needs "/work/development/approved-plan/crypto-loop/trace/schema.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/statements.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/iteration-proof.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/control/bounded/sublemma-tactic.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/algebra-proof.ml";;
needs "/work/proofs/implementations/crypto_math.ml";;
needs "/work/proofs/implementations/crypto_length.ml";;
needs "/work/development/approved-plan/crypto-loop/algebra.ml";;
let CRYPTO_BOUNDED_LOOP_EVENTS = prove
 (crypto_bounded_loop_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n=0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(SPEC `pc:num` CRYPTO_TRACE_PC_DISTINCT) THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst CRYPTO_MEMCMP_EXEC] THEN
  ENSURES_N_WHILE_UP_TAC `n:num` `pc+64` `pc+84`
   `\i s. read RDI s = word_add p (word i) /\
          read RSI s = word_add q (word i) /\
          read RDX s = word(n-i) /\ read memory s = m /\
          val(read RAX s) < 256 /\ val(read R10 s) < 256 /\
          (read RAX s = word 0 <=>
             !j. j<i ==> m(word_add p (word j)) = m(word_add q (word j))) /\
          (i=0 \/ (read ZF s <=> i=n)) /\
          read events s=APPEND
           (if read RIP s=word(pc+64) then crypto_trace_prefix pc p q n i
            else crypto_trace_body_prefix pc p q n i) e`
    `\i:num.6` `0` `1` `3` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_0;WORD_ADD_0;VAL_WORD_0;LT;ARITH;crypto_trace_prefix;APPEND];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0<n-i /\ n-i<2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC;ALL_TAC] THEN
    GHOST_INTRO_TAC `x:int64` `read RAX` THEN
    GHOST_INTRO_TAC `e0:uarch_event list` `read events` THEN
    MP_TAC(ISPECL [`pc:num`; `word_add p (word i):int64`;
      `word_add q (word i):int64`; `n-i:num`;
      `word(val(x:int64) MOD 256):byte`;
      `m(word_add (p:int64) (word i)):byte`; `m(word_add (q:int64) (word i)):byte`; `e0:uarch_event list`]
      CRYPTO_BOUNDED_ITERATION) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    CRYPTO_ENSURES_N_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst CRYPTO_MEMCMP_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;BYTES8_ELEMENT;READ_ELEMENT] THEN
    ASM_SIMP_TAC[CRYPTO_BYTE_PARENT_REPRESENTATION;CRYPTO_ZX_BYTE_BOUND;
      CRYPTO_DEV_PREFIX_EQ_STEP; GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `i<n ==> n-i-1=n-(i+1)`] THEN
    ASM_REWRITE_TAC[CRYPTO_DEV_ACCUMULATE_EQ_0] THEN
    ASM_SIMP_TAC[GSYM CRYPTO_BYTE_PARENT_REPRESENTATION;
      GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `i+1=0 <=> F`;
      ARITH_RULE `i<n ==> (n-i=1 <=> i+1=n)`;
      crypto_trace_body_prefix; ARITH_RULE `(i+1)-1=i`;APPEND_ASSOC] THEN
    REWRITE_TAC[ADD_SUB];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC CRYPTO_MEMCMP_EXEC (1--1) THEN
    ASM_SIMP_TAC[CRYPTO_TRACE_PREFIX_POS;crypto_trace_body_prefix;APPEND_ASSOC] THEN
    ASM_REWRITE_TAC[APPEND];
    GHOST_INTRO_TAC `x:int64` `read RAX` THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC CRYPTO_MEMCMP_EXEC (1--3) THEN
    ASM_SIMP_TAC[NEG_SHIFT_63_BYTE] THEN
    TRY COND_CASES_TAC THEN
    ASM_SIMP_TAC[CRYPTO_TRACE_PREFIX_POS;crypto_trace_body_prefix;APPEND_ASSOC] THEN
    ASM_REWRITE_TAC[APPEND];
    ASM_SIMP_TAC[NSUM_CONST_NUMSEG;ARITH_RULE `0<n ==> n-1+1=n`] THEN ASM_ARITH_TAC]);;
print_endline "CRYPTO_TRACE_LOOP_COMPLETE";;
