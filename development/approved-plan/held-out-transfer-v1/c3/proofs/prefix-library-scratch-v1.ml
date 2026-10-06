(* Concrete C3 scratch48/library-image fact. Discharges named firsthandoff image premise;
 no model/callee correctness claim, new address-mode callback or generic rule. *)
let C3_PREFIX_LIBRARY_SCRATCH_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary.
 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. lw_image_domain addr ==> (wp addr <=> lw_image_write addr))
 ==> !addr. fb_immutable addr ==> ~c3_scratch stackpointer addr`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `assurance_span_ok(\addr. wp addr /\ ordinary addr)(val(word_sub(stackpointer:int64)(word 48)))48` ASSUME_TAC THENL
 [ASM_SIMP_TAC[C3_STACK_SUB48_VALUE];ALL_TAC] THEN
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `(wp:num->bool)(addr:num)` ASSUME_TAC THENL
 [MP_TAC(ISPECL[`\addr:num. wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
  ASM_REWRITE_TAC[GSYM c3_scratch] THEN ASM_MESON_TAC[];
 ASM_MESON_TAC[C3_LIBRARY_IMMUTABLE_READONLY]]);;
