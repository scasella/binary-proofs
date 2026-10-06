(* Fixed C3 stack48 and actual crypto95/slot8 endpoint obligations. *)
let C3_PREFIX_SLOT_NONWRAP = prove
 (`!stackpointer:int64. 48<=val stackpointer /\ val stackpointer+8<2 EXP 64
 ==> val stackpointer-48+8<2 EXP 64`,
 GEN_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC);;
let C3_PREFIX_SLOT_READ_SPAN = prove
 (`!P (stackpointer:int64). 48<=val stackpointer /\
 assurance_span_ok P (val stackpointer-48)48
 ==> assurance_span_ok P (val stackpointer-48)8`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`P:num->bool`;`val(stackpointer:int64)-48`;`48`;`0`;`8`]R1_SECRET_SPAN_SUBSPAN) THEN
 ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;
let C3_PREFIX_SLOT_CRYPTO_DISJOINT = prove
 (`!stackpointer:int64. 48<=val stackpointer /\
 (!addr. ~(assurance_region(word_sub stackpointer(word 48))48 addr /\
 assurance_region(word 0x10241840)95 addr))
 ==> !addr. ~(assurance_region(word 0x10241840)95 addr /\
 assurance_region(word_sub stackpointer(word 48))8 addr)`,
 GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPEC `stackpointer:int64` C3_PREFIX_RETURN_SLOT_REGION) THEN
 REWRITE_TAC[c3_scratch] THEN ASM_MESON_TAC[]);;
let C3_PREFIX_IMAGE_PUBLIC_PERMISSIONS = prove
 (`!rp ordinary xp wp:num->bool.
 (!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\
 (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr))
 ==> !addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\
 (xp addr <=> lw_execute addr)`,
 MESON_TAC[]);;
