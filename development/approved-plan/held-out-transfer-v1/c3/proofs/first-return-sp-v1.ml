(* Actual first-call return stack site:48-byte call entry to40-byte caller continuation. *)
let C3_FIRST_RETURN_STACKPOINTER = prove
 (`!stackpointer:int64 returned:x86state. 48<=val stackpointer /\
 val(read RSP returned)=val(word_sub stackpointer(word 48))+8
 ==> read RSP returned=word_sub stackpointer(word 40)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 GEN_REWRITE_TAC LAND_CONV[GSYM WORD_VAL] THEN
 GEN_REWRITE_TAC RAND_CONV[GSYM WORD_VAL] THEN
 ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
 SUBGOAL_THEN `40<=val(stackpointer:int64)` ASSUME_TAC THENL[ASM_ARITH_TAC;ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;
