(* Only three address facts occur in this frozen standalone obligation.
   All simplification/arithmetic is local and does not receive caller states. *)
let C1_CRYPTO_SLOT_REGION_DISJOINT = prove
 (c1_crypto_slot_region_disjoint_statement,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`word 0x10241840:int64`;
    `word_sub (stackpointer:int64) (word 16)`;`95`;`8`]
     C1_NONOVERLAPPING_REGION_DISJOINT) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[MATCH_MP (SPEC `stackpointer:int64` C1_STACK_SUB16_VALUE)
      (ASSUME `16<=val(stackpointer:int64)`)] THEN
    MP_TAC (ASSUME `val(stackpointer:int64)+8<2 EXP 64`) THEN ARITH_TAC;
    MP_TAC (ASSUME `nonoverlapping(word_sub (stackpointer:int64) (word 16),8)
       (word 0x10241840,95)`) THEN REWRITE_TAC[NONOVERLAPPING_SYM]]);;
