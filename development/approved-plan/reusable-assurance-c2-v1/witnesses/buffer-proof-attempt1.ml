(* New C2 entrymembership attempt. Frozen beforehand; no execution or target-correctness premise. *)

let C2W_BUFFER_VALUES = prove
 (c2w_buffer_values_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:int64`;`q:int64`;`n:num`;`k:num`;`different:bool`;`i:num`]
    C2W_LAYOUT_POINT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPEC `word_add (p:int64) (word i)` C2W_EXTERNAL_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `different:bool` THENL
     [SUBGOAL_THEN `k<n` ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[c2w_layout]
         (ASSUME `c2w_layout (p:int64) q n k different`)) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(word_add (p:int64) (word i))=val p+i /\
        val(word_add (p:int64) (word k))=val p+k`
       STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC C2W_INDEX_VALUE THEN EXISTS_TAC `n:num` THEN
        MP_TAC(REWRITE_RULE[c2w_layout;assurance_span_ok]
         (ASSUME `c2w_layout (p:int64) q n k different`)) THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(word_add (p:int64) (word i)=word_add p (word k) <=> i=k)`
       ASSUME_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_SIMP_TAC[C2W_MEMORY_OUTSIDE;c2w_seed]];
      ASM_SIMP_TAC[C2W_MEMORY_OUTSIDE;c2w_seed]];
    SUBGOAL_THEN `different ==> ~(word_add (q:int64) (word i)=word_add p (word k))`
     ASSUME_TAC THENL
     [MP_TAC(REWRITE_RULE[c2w_layout]
       (ASSUME `c2w_layout (p:int64) q n k different`)) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `word_add (q:int64) (word i)` C2W_EXTERNAL_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[C2W_MEMORY_OUTSIDE;c2w_seed] THEN ASM_MESON_TAC[]]);;
