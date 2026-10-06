(* Public endpoint V2: normalized explicit facts after current-state substitution.
   Corrects only proof rewrite staging at the actual v4/v5 continuation. *)
let C3_SECOND_ENDPOINT_PUBLIC_TAC =
 (let sites=[SYM(ASSUME `587206944=pc`);SYM(ASSUME `587206704=secondpltpc`)] in
 let facts=[
 CONV_RULE NUM_REDUCE_CONV(ASSUME `n<2 EXP 64`);
 CONV_RULE NUM_REDUCE_CONV(MATCH_MP(SPEC `stackpointer:int64`C3_PREFIX_SLOT_NONWRAP)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64)+8<2 EXP 64`)));
 MATCH_MP(ISPECL[`\a:num. rp a /\ ordinary a`;`stackpointer:int64`]C3_PREFIX_SLOT_READ_SPAN)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `assurance_span_ok(\a:num. rp a /\ ordinary a)(val(stackpointer:int64)-48)48`));
 MATCH_MP(ISPECL[`rp:num->bool`;`ordinary:num->bool`;`xp:num->bool`;`wp:num->bool`]C3_PREFIX_IMAGE_PUBLIC_PERMISSIONS)(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`);
 ASSUME `read(memory :> bytes64(word 0x23003fd0))(v4:x86state)=word 0x10241840`;
 CONV_RULE NUM_REDUCE_CONV(REWRITE_RULE[HT_WORD_SUB_SUB](ASSUME `read RSP(v5:x86state)=word_sub(word_sub(stackpointer:int64)(word 40))(word 8)`));
 CONV_RULE NUM_REDUCE_CONV(REWRITE_RULE sites(REWRITE_RULE[HT_WORD_SUB_SUB](ASSUME `read(memory :> bytes64(word_sub(word_sub(stackpointer:int64)(word 40))(word 8)))(v5:x86state)=word(pc+58)`)))] in
 REWRITE_TAC[assurance_checked_run;bp_e2_crypto_public_pre;bp_e2_crypto_pre;C_ARGUMENTS;c3_loaded_code;c3_got] THEN
 REWRITE_TAC sites THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[HT_WORD_SUB_SUB] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts THEN
 REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ;CONG] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC sites THEN
 REWRITE_TAC[HT_WORD_SUB_SUB] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts);;
