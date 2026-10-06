(* C3-only first-handoff image and logical-buffer implications, with minimal explicit
   premises from the same frozen caller precondition and proved prefix frame. *)
let C3_PREFIX_IMAGE_REBIND = prove
 (`!file_bytes initial_rw padding stackpointer m t:x86state.
 fb_full_image file_bytes initial_rw padding m /\
 (!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory t addr=m addr) /\
 (!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr)
 ==> fb_full_image file_bytes(read memory t)(read memory t)(read memory t)`,
 REPEAT GEN_TAC THEN REWRITE_TAC[fb_full_image;fb_reference_image] THEN STRIP_TAC THEN
 X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN ASM_CASES_TAC `fb_immutable(val(addr:int64))` THEN
 ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let C3_PREFIX_INPUT_MEMORY = prove
 (`!P (p:int64) n (stackpointer:int64) m (t:x86state).
 assurance_span_ok P(val p)n /\
 (!addr. ~(assurance_region p n addr /\ c3_scratch stackpointer addr)) /\
 (!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory t addr=m addr)
 ==> !i. i<n ==> read memory t(word_add p(word i))=m(word_add p(word i))`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
 SUBGOAL_THEN `assurance_region(p:int64)n(val(word_add p(word i)))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`P:num->bool`;`p:int64`;`n:num`;`i:num`]HT_SPAN_WORD_ADD_REGION) THEN
 ASM_REWRITE_TAC[];ALL_TAC] THEN ASM_MESON_TAC[]);;
