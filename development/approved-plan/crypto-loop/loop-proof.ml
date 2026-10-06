needs "/work/proofs/qualification/crypto_iteration.ml";;
needs "/work/proofs/implementations/crypto_math.ml";;
needs "/work/proofs/implementations/crypto_length.ml";;
needs "/work/development/approved-plan/crypto-loop/algebra.ml";;
let CRYPTO_MEMCMP_BYTE_LOOP_CORRECT = prove
 (crypto_byte_loop_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n=0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst CRYPTO_MEMCMP_EXEC] THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc+64` `pc+84`
   `\i s. read RDI s = word_add p (word i) /\
          read RSI s = word_add q (word i) /\
          read RDX s = word(n-i) /\ read memory s = m /\
          val(read RAX s) < 256 /\ val(read R10 s) < 256 /\
          (read RAX s = word 0 <=>
             !j. j<i ==> m(word_add p (word j)) = m(word_add q (word j))) /\
          (i=0 \/ (read ZF s <=> i=n))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_0;WORD_ADD_0;VAL_WORD_0;LT;ARITH];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0<n-i /\ n-i<2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC;ALL_TAC] THEN
    GHOST_INTRO_TAC `x:int64` `read RAX` THEN
    GHOST_INTRO_TAC `e:uarch_event list` `read events` THEN
    MP_TAC(ISPECL [`pc:num`; `word_add p (word i):int64`;
      `word_add q (word i):int64`; `n-i:num`;
      `word(val(x:int64) MOD 256):byte`;
      `m(word_add (p:int64) (word i)):byte`; `m(word_add (q:int64) (word i)):byte`; `e:uarch_event list`]
      CRYPTO_MEMCMP_BYTE_ITERATION) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    ENSURES_SUBLEMMA_TAC (MATCH_MP bytes_loaded_update (fst CRYPTO_MEMCMP_EXEC)) "s0" "s1" THEN
    ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE;BYTES8_ELEMENT;READ_ELEMENT] THEN
    ASM_SIMP_TAC[CRYPTO_BYTE_PARENT_REPRESENTATION;CRYPTO_ZX_BYTE_BOUND;
      CRYPTO_DEV_PREFIX_EQ_STEP; GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `i<n ==> n-i-1=n-(i+1)`] THEN
    ASM_REWRITE_TAC[CRYPTO_DEV_ACCUMULATE_EQ_0] THEN
    ASM_SIMP_TAC[GSYM CRYPTO_BYTE_PARENT_REPRESENTATION;
      GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `i+1=0 <=> F`;
      ARITH_RULE `i<n ==> (n-i=1 <=> i+1=n)`];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC CRYPTO_MEMCMP_EXEC (1--1);
    GHOST_INTRO_TAC `x:int64` `read RAX` THEN
    ASM_REWRITE_TAC[] THEN X86_SIM_TAC CRYPTO_MEMCMP_EXEC (1--3) THEN
    ASM_SIMP_TAC[NEG_SHIFT_63_BYTE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;
print_endline "CRYPTO_DEV_LOOP_COMPLETE";;
