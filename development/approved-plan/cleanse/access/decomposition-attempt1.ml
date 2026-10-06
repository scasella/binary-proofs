needs "/work/development/approved-plan/cleanse/functional/callable-algebra-attempt3.ml";;
needs "/work/development/approved-plan/cleanse/access/decomposition-statement-v1.ml";;
let CLEANSE_ACCESS_LARGE_DECOMPOSITION = prove
 (cleanse_access_large_decomposition_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
  MP_TAC(SPEC `v:num` CLEANSE_FUNCTIONAL_ALIGNMENT_COUNT) THEN
  REWRITE_TAC[LET_DEF;LET_END_DEF] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n-((8-v MOD 8) MOD 8):num`;`8`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_ARITH_TAC);;
print_endline "CLEANSE_ACCESS_LARGE_DECOMPOSITION_ATTEMPT1_COMPLETE";;
