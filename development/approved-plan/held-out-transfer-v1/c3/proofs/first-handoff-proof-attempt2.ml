(* Static exact terminal facts visible in staged-v3 actual10step endpoint.
 No global ASM rewrite/search, hidden premise, new generic selector or normalization callback. *)
let C3_PREFIX_TERMINAL_SELECTED_V3_TAC =
 (let ac=last(CONJUNCTS(MATCH_MP(ISPECL[`stackpointer:int64`;`s:x86state`;`s10:x86state`]C3_PREFIX_FRAME_OUTSIDE)
   (ASSUME `c3_prefix_frame stackpointer(s:x86state)(s10:x86state)`))) in
  let facts=[
   CONV_RULE NUM_REDUCE_CONV (MATCH_MP(SPEC `stackpointer:int64`C3_PREFIX_SLOT_NONWRAP)
    (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64)+8<2 EXP 64`)));
   MATCH_MP(ISPECL[`\a:num. rp a /\ ordinary a`;`stackpointer:int64`]C3_PREFIX_SLOT_READ_SPAN)
    (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `assurance_span_ok(\a:num. rp a /\ ordinary a)(val(stackpointer:int64)-48)48`));
   MATCH_MP(SPEC `stackpointer:int64`C3_PREFIX_SLOT_CRYPTO_DISJOINT)
    (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `!addr. ~(assurance_region(word_sub(stackpointer:int64)(word 48))48 addr /\ assurance_region(word 0x10241840)95 addr)`));
   MATCH_MP(ISPECL[`rp:num->bool`;`ordinary:num->bool`;`xp:num->bool`;`wp:num->bool`]C3_PREFIX_IMAGE_PUBLIC_PERMISSIONS)
    (ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`);SYM(ASSUME `587206944=pc`);SYM(ASSUME `587206704=pltpc`);ac;
   ASSUME `~bit 18(read rflags(s:x86state))`;
   ASSUME `fb_file_code lib_file`;
   ASSUME `fb_full_image lib_file(read memory(s10:x86state))(read memory s10)(read memory s10)`;
   ASSUME `n<2 EXP 64`;
   ASSUME `read RSP(s10:x86state)=word_sub(stackpointer:int64)(word 48)`;
   ASSUME `read RIP(s10:x86state)=read(memory :> bytes64(word(pltpc+12192)))(s9:x86state)`;
   ASSUME `read(memory :> bytes64(word 0x23003fd0))(s9:x86state)=word 0x10241840`;
   ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 48)))(s10:x86state)=word(pc+24)`;
   ASSUME `read RDI(s10:x86state)=p`;
   ASSUME `read RSI(s10:x86state)=q`;
   ASSUME `read RDX(s10:x86state)=word n`;
   ASSUME `~read DF(s10:x86state)`;
   ASSUME `val(word_sub(stackpointer:int64)(word 48))=val stackpointer-48`;
   ASSUME `val(word_sub(stackpointer:int64)(word 48)) MOD 16=8`;
   ASSUME `assurance_span_ok(\a. xp a /\ ordinary a)0x10241840 95`;
   ASSUME `assurance_span_ok(\a. rp a /\ ordinary a)(val(p:int64))n`;
   ASSUME `assurance_span_ok(\a. rp a /\ ordinary a)(val(q:int64))n`;
   ASSUME `assurance_canonical48(val(read ABI_FS_BASE(a:abi_omitted_state)))`;
   ASSUME `read RBX(s10:x86state)=p`;
   ASSUME `read RBP(s10:x86state)=word n`;
   ASSUME `read R12(s10:x86state)=q`;
   ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 8)))(s10:x86state)=r13initial`;
   ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 16)))(s10:x86state)=r12initial`;
   ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 24)))(s10:x86state)=rbpinitial`;
   ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 32)))(s10:x86state)=rbxinitial`;
   ASSUME `read R13(s:x86state)=r13initial`;
   ASSUME `read R12(s:x86state)=r12initial`;
   ASSUME `read RBP(s:x86state)=rbpinitial`;
   ASSUME `read RBX(s:x86state)=rbxinitial`;
   ASSUME `read R13(s10:x86state)=r13initial`;
   ASSUME `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(s10:x86state)addr=m addr`;
   ASSUME `!i. i<n ==> read memory(s10:x86state)(word_add p(word i))=m(word_add p(word i))`;
   ASSUME `!i. i<n ==> read memory(s10:x86state)(word_add q(word i))=m(word_add q(word i))`;
   ASSUME `bytes_loaded(s10:x86state)(word pc)c3_caller_mc`;
   ASSUME `bytes_loaded(s10:x86state)(word pltpc)c3_crypto_plt_prefix`;
   ASSUME `bytes_loaded(s10:x86state)(word 0x23001040)c3_cleanse_plt_prefix`;
   ASSUME `bytes_loaded(s10:x86state)(word 0x10241840)crypto_memcmp_mc`;
   ASSUME `bytes_loaded(s10:x86state)(word 0x102417d0)openssl_cleanse_mc`;
   ASSUME `read(memory :> bytes64(word 0x23003fd0))(s10:x86state)=word 0x10241840`;
   ASSUME `read(memory :> bytes64(word 0x23003fd8))(s10:x86state)=word 0x102417d0`;
   ASSUME `c3_prefix_frame stackpointer(s:x86state)(s10:x86state)`] in
 REWRITE_TAC[c3_loaded_code;c3_got] THEN REWRITE_TAC facts THEN
 REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ] THEN
 CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts THEN
 REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REWRITE_TAC[SYM(ASSUME `587206944=pc`);SYM(ASSUME `587206704=pltpc`)] THEN
 REWRITE_TAC[REWRITE_RULE[SYM(ASSUME `587206944=pc`)](ASSUME `bytes_loaded(s10:x86state)(word pc)c3_caller_mc`);
             REWRITE_RULE[SYM(ASSUME `587206704=pltpc`)](ASSUME `bytes_loaded(s10:x86state)(word pltpc)c3_crypto_plt_prefix`)]);;

let C3_HANDOFF = prove(c3_handoff_statement,
 C3_PREFIX_10_STEPS_TAC THEN
 (HT_STATE_NORMALIZE_TAC [] THEN
 SUBGOAL_THEN `c3_prefix_frame stackpointer (s:x86state) s10` ASSUME_TAC THENL
 [MP_TAC(SPEC `stackpointer:int64` C3_PREFIX_CONCRETE_FRAME_INCLUDED) THEN
  REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(s10:x86state)addr=m addr` ASSUME_TAC THENL
 [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
  SUBGOAL_THEN `read memory(s10:x86state)addr=read memory(s:x86state)addr`
  (fun th -> ACCEPT_TAC(TRANS th(AP_THM(ASSUME `read memory(s:x86state)=m`)`addr:int64`))) THEN
  MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`addr:int64`;`s:x86state`;`s10:x86state`]C3_PREFIX_FRAME_BYTE) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]C3_PREFIX_LIBRARY_SCRATCH_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP (SPEC `addr:num`(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`)) (ASSUME `lw_image_domain(addr:num)`)) THEN MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `fb_full_image lib_file(read memory(s10:x86state))(read memory s10)(read memory s10)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`stackpointer:int64`;`m:int64->byte`;`s10:x86state`]C3_PREFIX_IMAGE_REBIND) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(s10:x86state)(word_add p(word i))=m(word_add p(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`p:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s10:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(s10:x86state)(word_add q(word i))=m(word_add q(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`q:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s10:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC])
 THEN
 (MP_TAC(MATCH_MP(SPEC `stackpointer:int64`C3_STACK_ALIGNMENT)
 (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64) MOD 16=8`))) THEN STRIP_TAC)
 THEN
 (SUBGOAL_THEN `!addr. ~(assurance_region(word_sub(stackpointer:int64)(word 48))48 addr /\ assurance_region(word 0x10241840)95 addr)` ASSUME_TAC THENL
 [MATCH_MP_TAC(SPEC `stackpointer:int64`C3_PREFIX_CRYPTO_REGION_DISJOINT) THEN
 CONJ_TAC THENL [ACCEPT_TAC(ASSUME `48<=val(stackpointer:int64)`);
 ACCEPT_TAC(ASSUME `nonoverlapping(word_sub(stackpointer:int64)(word 48),48)(word 0x10241840,95)`)];ALL_TAC])
 THEN
 (REWRITE_TAC[assurance_checked_run;c3_crypto_ready;c3_saved_prefix;bp_e2_crypto_public_pre;bp_e2_crypto_pre;C_ARGUMENTS])
 THEN C3_PREFIX_TERMINAL_SELECTED_V3_TAC);;
if hyp C3_HANDOFF<>[] || frees(concl C3_HANDOFF)<>[] || not(aconv(concl C3_HANDOFF)c3_handoff_statement) then failwith "C3_HANDOFF live literal/closure failure";;
print_endline "C3_HANDOFF_DEVELOPMENT_CHECKED_LITERAL_NOT_ACCEPTANCE";;
