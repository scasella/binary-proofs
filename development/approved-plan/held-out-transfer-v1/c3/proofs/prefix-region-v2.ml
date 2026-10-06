(* First public call's concrete code/return-slot geometry, under frozen caller stackbounds. *)
let C3_PREFIX_CRYPTO_REGION_DISJOINT = prove
 (`!stackpointer:int64. 48<=val stackpointer /\
 nonoverlapping(word_sub stackpointer(word 48),48)(word 0x10241840,95)
 ==> !addr. ~(assurance_region(word_sub stackpointer(word 48))48 addr /\
 assurance_region(word 0x10241840)95 addr)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x10241840:int64`;`48`;`95`]HT_REGION_DISJOINT) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 ASM_REWRITE_TAC[] THEN MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN
 ASM_ARITH_TAC);;
let C3_PREFIX_RETURN_SLOT_REGION = prove
 (`!stackpointer:int64 addr. assurance_region(word_sub stackpointer(word 48))8 addr
 ==> c3_scratch stackpointer addr`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_scratch;assurance_region] THEN STRIP_TAC THEN ASM_ARITH_TAC);;
