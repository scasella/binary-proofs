needs "/work/development/approved-plan/cleanse/functional/imports.ml";;
needs "/work/development/approved-plan/cleanse/functional/alignment-statements.ml";;
let CLEANSE_FUNCTIONAL_LOW3 = prove
 (cleanse_functional_low3_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(i:num)<2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `word 7:int64=word(2 EXP 3-1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_AND_MASK_WORD;VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
  CONV_TAC NUM_REDUCE_CONV);;
print_endline "CLEANSE_FUNCTIONAL_ALIGNMENT_ALGEBRA_ATTEMPT2_COMPLETE";;
