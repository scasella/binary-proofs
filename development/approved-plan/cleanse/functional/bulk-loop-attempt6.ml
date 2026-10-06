needs "/work/development/approved-plan/cleanse/functional/bulk-algebra-attempt2.ml";;
let OPENSSL_CLEANSE_BULK_LOOP = prove
 (cleanse_functional_bulk_loop_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k=0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[SOME_FLAGS;fst OPENSSL_CLEANSE_EXEC] THEN
  ENSURES_WHILE_UP_TAC `k:num` `pc+69` `pc+87`
   `\i s. read RDI s=word_add p (word(8*i)) /\
          read RSI s=word(8*(k-i)+r) /\ read RAX s=word 0 /\
          read(memory :> bytes(p,8*i))s=0 /\
          (i=0 \/ (read ZF s <=> i=k))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_0;MULT_CLAUSES;WORD_ADD_0;READ_COMPONENT_COMPOSE;READ_BYTES_TRIVIAL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `8<=8*(k-i)+r /\ 8*(k-(i+1))+r<2 EXP 64` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `(i:num)<k /\ 8*k+r<b ==> 8<=8*(k-i)+r /\ 8*(k-(i+1))+r<b`) THEN
      ASM_REWRITE_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word(8*(k-i)+r)) (word 18446744073709551608):int64=word(8*(k-(i+1))+r)`
     ASSUME_TAC THENL
     [SUBGOAL_THEN `word 18446744073709551608:int64=word_neg(word 8)` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV;ALL_TAC] THEN
      REWRITE_TAC[WORD_RULE `word_add (x:int64) (word_neg y)=word_sub x y`] THEN
      SUBGOAL_THEN `8*((k:num)-(i+1))+r=(8*(k-i)+r)-8` SUBST1_TAC THENL
       [SUBGOAL_THEN `(k:num)-i=k-(i+1)+1` SUBST1_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE `(i:num)<k ==> k-i=k-(i+1)+1`) THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES;ARITH_RULE `(((x:num)+8)+r)-8=x+r`]];
        CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[WORD_SUB]];
      ALL_TAC] THEN
    X86_SIM_TAC OPENSSL_CLEANSE_EXEC (1--4) THEN
    SUBGOAL_THEN `read(memory :> bytes(p:int64,8*i+8))s4=0` ASSUME_TAC THENL
     [MATCH_MP_TAC CLEANSE_FUNCTIONAL_PREFIX_READ64 THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `8*(i+1)=8*i+8`;ARITH_RULE `i+1=0 <=> F`;
      CLEANSE_FUNCTIONAL_BULK_MASK] THEN
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
    ASM_REWRITE_TAC[SUB_REFL;MULT_CLAUSES;ADD_CLAUSES]]);;
print_endline "CLEANSE_FUNCTIONAL_BULK_LOOP_ATTEMPT6_COMPLETE";;
