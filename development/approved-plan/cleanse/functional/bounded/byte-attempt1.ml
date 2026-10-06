needs "/work/development/approved-plan/cleanse/functional/prefix-proof-attempt1.ml";;
needs "/work/development/approved-plan/cleanse/functional/imports.ml";;
needs "/work/development/approved-plan/cleanse/functional/bounded/statements-v1.ml";;
let OPENSSL_CLEANSE_BOUNDED_BYTE_LOOP = prove
 (cleanse_functional_bounded_byte_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n=0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS;fst OPENSSL_CLEANSE_EXEC] THEN
  ENSURES_N_WHILE_UP_TAC `n:num` `pc+19` `pc+29`
   `\i s. read RDI s=word_add p (word i) /\
          read RSI s=word(n-i) /\ read RAX s=word 0 /\
          read(memory :> bytes(p,i))s=0 /\
          (i=0 \/ (read ZF s <=> i=n))`
    `\i:num.3` `0` `1` `1` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_0;WORD_ADD_0;READ_COMPONENT_COMPOSE;READ_BYTES_TRIVIAL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `0<n-i /\ n-i<2 EXP 64 /\ n-i-1<2 EXP 64 /\ n-(i+1)<2 EXP 64` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `(i:num)<n /\ n<b ==> 0<n-i /\ n-i<b /\ n-i-1<b /\ n-(i+1)<b`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub(word(n-i))(word 1):int64=word(n-i-1)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB;ARITH_RULE `0<k ==> 1<=k`];ALL_TAC] THEN
    X86_SIM_TAC OPENSSL_CLEANSE_EXEC (1--3) THEN
    SUBGOAL_THEN `read(memory :> bytes(p:int64,i+1))s3=0` ASSUME_TAC THENL
     [MATCH_MP_TAC CLEANSE_FUNCTIONAL_PREFIX_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `i<n ==> n-i-1=n-(i+1)`;ARITH_RULE `i+1=0 <=> F`;
      VAL_WORD;DIMINDEX_64;MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    POP_ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC
     (filter(fun th -> forall(fun v -> type_of v = `:num`) (frees(concl th))) ths)) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:
     (SUBGOAL_THEN `read ZF s0 <=> F` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC])
     OPENSSL_CLEANSE_EXEC (1--1);
    ASM_REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:
     (SUBGOAL_THEN `read ZF s0 <=> T` ASSUME_TAC THENL [ASM_MESON_TAC[];ALL_TAC])
     OPENSSL_CLEANSE_EXEC (1--1) THEN
    ASM_REWRITE_TAC[SUB_REFL];
    ASM_SIMP_TAC[NSUM_CONST_NUMSEG;ARITH_RULE `0<n ==> n-1+1=n`] THEN ASM_ARITH_TAC]);;

print_endline "CLEANSE_FUNCTIONAL_BOUNDED_BYTE_LOOP_ATTEMPT1_COMPLETE";;
