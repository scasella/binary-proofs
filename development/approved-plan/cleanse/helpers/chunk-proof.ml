let CLEANSE_PREFIX_ZERO_STORE_BYTES = prove
 (cleanse_prefix_zero_store_bytes_statement,
  REWRITE_TAC[CLEANSE_READ_BYTES_ZERO;
    REWRITE_RULE[READ_ELEMENT] READ_ELEMENT_WRITE_BYTES; LIMB_0] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(j:num)<(i:num)` THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `(i:num)<=(j:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_sub (word_add (p:int64) (word(j:num)))
               (word_add p (word(i:num))) = word(j-i)`
     ASSUME_TAC THENL
      [CONV_TAC SYM_CONV THEN REWRITE_TAC[WORD_SUB] THEN
       ASM_REWRITE_TAC[WORD_RULE
        `word_sub (word_add (p:int64) x) (word_add p y) = word_sub x y`];
       ALL_TAC] THEN
    SUBGOAL_THEN
     `val(word_sub (word_add (p:int64) (word(j:num)))
                   (word_add p (word(i:num)))) < k`
     ASSUME_TAC THENL
      [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
       MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `j-i:num` THEN
       REWRITE_TAC[MOD_LE] THEN ASM_ARITH_TAC;
       ASM_REWRITE_TAC[]]]);;
let CLEANSE_PREFIX_ZERO_STORE_BYTES64 =
 let zero_asword = prove
  (`!n:num. write asword (word 0:int64) n = 0`,
   REWRITE_TAC[asword; through; write; VAL_WORD_0]) in
 prove(cleanse_prefix_zero_store_bytes64_statement,
  REWRITE_TAC[bytes64; WRITE_COMPONENT_COMPOSE; zero_asword;
    CLEANSE_PREFIX_ZERO_STORE_BYTES]);;
