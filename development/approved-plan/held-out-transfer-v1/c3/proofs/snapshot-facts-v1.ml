(* Caller-specific C3 initial/current logical snapshots and result interpretation.
   Ordinary fixed local proofs using frozen predicates/rules. No supplier body,
   automation, generic export, changed domain or additional end-theorem premise.
   Obligations: first equality uses M0; second equality uses cleansed M0 even
   when p/q overlap; actual return value uses the correct pair of snapshots. *)
let C3_INITIAL_LOGICAL_SNAPSHOT_EQ = prove
 (`!m current p q n.
   (!i. i<n ==> current(word_add p(word i))=m(word_add p(word i))) /\
   (!i. i<n ==> current(word_add q(word i))=m(word_add q(word i)))
   ==> (c3_equal current p q n <=> c3_equal m p q n)`,
 REWRITE_TAC[c3_equal] THEN MESON_TAC[]);;

let C3_CLEANSED_P_LOGICAL_BYTES = prove
 (`!P m p:int64 n.
   assurance_span_ok P (val p) n
   ==> !i. i<n ==> c3_cleansed_memory m p n (word_add p(word i))=word 0`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 SUBGOAL_THEN `assurance_region (p:int64) n (val(word_add p(word i)))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`P:num->bool`;`p:int64`;`n:num`;`i:num`]HT_SPAN_WORD_ADD_REGION) THEN ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[c3_cleansed_memory]]);;

let C3_CURRENT_LOGICAL_SNAPSHOT_EQ = prove
 (`!P m current p:int64 q n.
   assurance_span_ok P (val p) n /\
   (!i. i<n ==> current(word_add p(word i))=word 0) /\
   (!i. i<n ==> current(word_add q(word i))=
       c3_cleansed_memory m p n (word_add q(word i)))
   ==> (c3_equal current p q n <=>
        c3_equal (c3_cleansed_memory m p n) p q n)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC C3_INITIAL_LOGICAL_SNAPSHOT_EQ THEN ASM_REWRITE_TAC[] THEN
 MP_TAC(ISPECL[`P:num->bool`;`m:int64->byte`;`p:int64`;`n:num`]C3_CLEANSED_P_LOGICAL_BYTES) THEN
 ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let C3_INITIAL_MISMATCH_RESULT = prove
 (`!m p q n. ~(c3_equal m p q n) ==> c3_result m p q n=word 2`,
 SIMP_TAC[c3_result]);;

let C3_INITIAL_EQUAL_CURRENT_RESULT = prove
 (`!P m current p:int64 q n.
   c3_equal m p q n /\ assurance_span_ok P (val p) n /\
   (!i. i<n ==> current(word_add p(word i))=word 0) /\
   (!i. i<n ==> current(word_add q(word i))=
       c3_cleansed_memory m p n (word_add q(word i)))
   ==> c3_result m p q n =
       (if c3_equal current p q n then word 1 else word 0)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `c3_equal (current:int64->byte) p q n <=>
               c3_equal (c3_cleansed_memory m p n) p q n` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`P:num->bool`;`m:int64->byte`;`current:int64->byte`;`p:int64`;`q:int64`;`n:num`]C3_CURRENT_LOGICAL_SNAPSHOT_EQ) THEN ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[c3_result]]);;

print_endline "C3_SNAPSHOT_FACTS_V1_DEVELOPMENT_CHECKED";;
