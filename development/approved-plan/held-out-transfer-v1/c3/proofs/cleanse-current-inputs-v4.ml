(* Concrete C3 initial/current memory transport through the actual cleanse
   interface. Named obligation: second comparison observes cleansed memory,
   including partial aliases, rather than the initial comparison snapshot.
   No new generic inverse-region rule or supplier implementation is consumed. *)
let C3_CLEANSE_CURRENT_INPUTS = prove
 (`!stackpointer p q n m P initial entry returned.
 assurance_span_ok P (val(p:int64)) n /\
 c3_saved_prefix stackpointer p q n m initial entry /\
 bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> (!i. i<n ==> read memory returned(word_add p(word i))=word 0) /\
     (!i. i<n ==> read memory returned(word_add q(word i))=
         c3_cleansed_memory m p n(word_add q(word i))) /\
     (!addr. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr))
             ==> read memory returned addr=m addr)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(entry:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_call_post 0x102417d0 (word_sub(stackpointer:int64)(word 48))
   (word 0x2300114c)p n(read memory(entry:x86state))entry returned` THEN
 REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
 CONJ_TAC THENL [ASM_REWRITE_TAC[];ALL_TAC] THEN CONJ_TAC THENL
 [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[c3_cleansed_memory] THEN
  ASM_CASES_TAC `assurance_region(p:int64)n(val(word_add(q:int64)(word i)))` THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `val(p:int64)+(val(word_add(q:int64)(word i))-val p)=val(word_add q(word i)) /\
                 val(word_add q(word i))-val p<n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `assurance_region(p:int64)n(val(word_add(q:int64)(word i)))` THEN
    REWRITE_TAC[assurance_region] THEN ARITH_TAC;ALL_TAC] THEN
   SUBGOAL_THEN `word_add(p:int64)(word(val(word_add(q:int64)(word i))-val p))=word_add q(word i)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)[GSYM WORD_VAL] THEN
    GEN_REWRITE_TAC LAND_CONV[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[WORD_VAL];ALL_TAC] THEN
   MATCH_ACCEPT_TAC(REWRITE_RULE
     [ASSUME `word_add(p:int64)(word(val(word_add(q:int64)(word i))-val p))=word_add q(word i)`]
     (MATCH_MP (SPEC `val(word_add(q:int64)(word i))-val(p:int64)`
       (ASSUME `!i. i<n ==> read memory(returned:x86state)(word_add p(word i))=word 0`))
       (ASSUME `val(word_add(q:int64)(word i))-val(p:int64)<n`)));
   ASM_REWRITE_TAC[]];
  X_GEN_TAC `addr:int64` THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]]);;
print_endline "C3_CLEANSE_CURRENT_INPUTS_V4_DEVELOPMENT_CHECKED";;
