(* Concrete C3 actual cleanse continuation -> next comparison image fact.
   Named obligation: derive the second CRYPTO public loaded-image precondition.
   Derived from public write permissions/configuration and outside-destination
   preservation. No supplier body or new generic/exported memory law. *)
let C3_CLEANSE_LIBRARY_IMAGE = prove
 (`!lib_file stackpointer p n rp wp xp ordinary entry a returned.
 bp_e2_cleanse_public_pre lib_file (read memory entry)(read memory entry)
   (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory entry)
   rp wp xp ordinary (entry,a) /\
 bp_e2_cleanse_call_post 0x102417d0 (word_sub stackpointer(word 48))
   (word 0x2300114c)p n(read memory entry)entry returned
 ==> fb_full_image lib_file(read memory returned)(read memory returned)(read memory returned)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_public_pre lib_file (read memory(entry:x86state))(read memory entry)
   (word_sub(stackpointer:int64)(word 48))(word 0x2300114c)p n(read memory entry)
   rp wp xp ordinary (entry,a)` THEN
 REWRITE_TAC[bp_e2_cleanse_public_pre;bp_e2_cleanse_pre] THEN STRIP_TAC THEN
 UNDISCH_TAC `bp_e2_cleanse_call_post 0x102417d0 (word_sub(stackpointer:int64)(word 48))
   (word 0x2300114c)p n(read memory(entry:x86state))entry returned` THEN
 REWRITE_TAC[bp_e2_cleanse_call_post] THEN STRIP_TAC THEN
 SUBGOAL_THEN `!addr. fb_immutable addr ==> ~assurance_region(p:int64)n addr` ASSUME_TAC THENL
 [REPEAT STRIP_TAC THEN SUBGOAL_THEN `(wp:num->bool)(addr:num)` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\addr:num. wp addr /\ ordinary addr`;`p:int64`;`n:num`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   ASM_MESON_TAC[C3_LIBRARY_IMMUTABLE_READONLY]];
  RULE_ASSUM_TAC(REWRITE_RULE[fb_full_image;fb_reference_image]) THEN
  REWRITE_TAC[fb_full_image;fb_reference_image] THEN
  X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
  ASM_CASES_TAC `fb_immutable(val(addr:int64))` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]]);;
print_endline "C3_CLEANSE_LIBRARY_IMAGE_V1_DEVELOPMENT_CHECKED";;
