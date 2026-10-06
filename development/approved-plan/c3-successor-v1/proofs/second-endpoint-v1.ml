(* Fixed second-five endpoint derivations from original pre, actual cleanse post,
   and the actual narrow local frame. No adaptation or generic integration rule. *)
let C3_SECOND_ENDPOINT_CORE_TAC =
 SUBGOAL_THEN `(MAYCHANGE[RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),8)] ,, MAYCHANGE[events])(returned:x86state)(v5:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](SPEC `stackpointer:int64`C3_SECOND_CONCRETE_FRAME_INCLUDED)) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `(MAYCHANGE[RIP;RSP;RDX;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE[events])(returned:x86state)(v5:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](SPEC `stackpointer:int64`C3_SECOND_FRAME_WIDE_INCLUDED)) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_SAVED_BINDINGS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_SAVED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`\a:num. rp a /\ ordinary a`;`initial:x86state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_CURRENT_INPUTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_CLEANSE_RETURN_WORKING_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_OUTSIDE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 SUBGOAL_THEN `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(v5:x86state)addr=read memory(returned:x86state)addr` ASSUME_TAC THENL
 [REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`addr:int64`;`returned:x86state`;`v5:x86state`]C3_SECOND_FRAME_WIDE_BYTE) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add p(word i))=read memory(returned:x86state)(word_add p(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`p:int64`;`n:num`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add q(word i))=read memory(returned:x86state)(word_add q(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`q:int64`;`n:num`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add p(word i))=word 0` ASSUME_TAC THENL
 [ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(v5:x86state)(word_add q(word i))=c3_cleansed_memory m p n(word_add q(word i))` ASSUME_TAC THENL
 [ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!addr:int64. ~(assurance_region p n(val addr) \/ c3_scratch stackpointer(val addr)) ==> read memory(v5:x86state)addr=m addr` ASSUME_TAC THENL
 [ASM_MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]C3_PREFIX_LIBRARY_SCRATCH_DISJOINT) THEN ASM_REWRITE_TAC[] THEN
 X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
 MP_TAC(MATCH_MP(SPEC `addr:num`(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`))(ASSUME `lw_image_domain(addr:num)`)) THEN MESON_TAC[];ALL_TAC] THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`n:num`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`entry:x86state`;`a:abi_omitted_state`;`returned:x86state`]C3_CLEANSE_LIBRARY_IMAGE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 SUBGOAL_THEN `fb_full_image lib_file(read memory(v5:x86state))(read memory v5)(read memory v5)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`read memory(returned:x86state)`;`read memory(returned:x86state)`;`stackpointer:int64`;`read memory(returned:x86state)`;`v5:x86state`]C3_PREFIX_IMAGE_REBIND) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(MATCH_MP(SPEC `stackpointer:int64`C3_STACK_ALIGNMENT)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64) MOD 16=8`))) THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`]C3_PREFIX_CRYPTO_REGION_DISJOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 MP_TAC(ISPECL[`stackpointer:int64`]C3_PREFIX_SLOT_CRYPTO_DISJOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let C3_SECOND_ENDPOINT_TOTAL_FRAME_TAC =
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])(initial:x86state)(v5:x86state)` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]C3_SECOND_TOTAL_FRAME_INCLUDED)) THEN
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN CONJ_TAC THENL
 [ASM_REWRITE_TAC[];
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `returned:x86state` THEN CONJ_TAC THENL
 [ACCEPT_TAC(last(CONJUNCTS(REWRITE_RULE[bp_e2_cleanse_call_post](ASSUME `bp_e2_cleanse_call_post 0x102417d0(word_sub(stackpointer:int64)(word 48))(word 0x2300114c)p n(read memory(entry:x86state))entry(returned:x86state)`))));
 ASM_REWRITE_TAC[]]];ALL_TAC];;

let C3_SECOND_ENDPOINT_PUBLIC_TAC =
 (let facts=[
 CONV_RULE NUM_REDUCE_CONV(MATCH_MP(SPEC `stackpointer:int64`C3_PREFIX_SLOT_NONWRAP)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64)+8<2 EXP 64`)));
 MATCH_MP(ISPECL[`\a:num. rp a /\ ordinary a`;`stackpointer:int64`]C3_PREFIX_SLOT_READ_SPAN)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `assurance_span_ok(\a:num. rp a /\ ordinary a)(val(stackpointer:int64)-48)48`));
 MATCH_MP(ISPECL[`rp:num->bool`;`ordinary:num->bool`;`xp:num->bool`;`wp:num->bool`]C3_PREFIX_IMAGE_PUBLIC_PERMISSIONS)(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`);
 SYM(ASSUME `587206944=pc`);SYM(ASSUME `587206704=secondpltpc`)] in
 REWRITE_TAC[assurance_checked_run;bp_e2_crypto_public_pre;bp_e2_crypto_pre;C_ARGUMENTS;c3_loaded_code;c3_got;HT_WORD_SUB_SUB] THEN
 CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ;CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
