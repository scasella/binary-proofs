(* Fixed C3 cleanup-entry permission/geometry facts; unchanged frozen domain. *)
let C3_CLEANUP_P_SLOT_DISJOINT = prove
 (`!stackpointer p:int64 n.
 (!addr. ~(assurance_region p n addr /\ c3_scratch stackpointer addr))
 ==> !addr. ~(assurance_region p n addr /\ assurance_region(word_sub stackpointer(word 48))8 addr)`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 MP_TAC(SPEC `stackpointer:int64`C3_PREFIX_RETURN_SLOT_REGION) THEN MESON_TAC[]);;
let C3_CLEANUP_P_CODE_DISJOINT = prove
 (`!p:int64 n.
 (!addr. assurance_region p n addr ==>
 ~(assurance_region(word 0x23001120)89 addr \/ assurance_region(word 0x23001030)6 addr \/
 assurance_region(word 0x23001040)6 addr \/ assurance_region(word 0x23003fd0)8 addr \/
 assurance_region(word 0x23003fd8)8 addr \/ assurance_region(word 0x10241840)95 addr \/
 assurance_region(word 0x102417d0)97 addr))
 ==> !addr. ~(assurance_region p n addr /\ assurance_region(word 0x102417d0)97 addr)`,
 MESON_TAC[]);;
let C3_CLEANUP_ENDPOINT_PUBLIC_UNFOLD_TAC =
 MP_TAC(ISPECL[`stackpointer:int64`;`p:int64`;`n:num`]C3_CLEANUP_P_SLOT_DISJOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 MP_TAC(ISPECL[`p:int64`;`n:num`]C3_CLEANUP_P_CODE_DISJOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 (let facts=[
  CONV_RULE NUM_REDUCE_CONV(MATCH_MP(SPEC `stackpointer:int64`C3_PREFIX_SLOT_NONWRAP)
   (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64)+8<2 EXP 64`)));
  MATCH_MP(ISPECL[`\a:num. rp a /\ ordinary a`;`stackpointer:int64`]C3_PREFIX_SLOT_READ_SPAN)
   (CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `assurance_span_ok(\a:num. rp a /\ ordinary a)(val(stackpointer:int64)-48)48`));
  ASSUME `!addr. ~(assurance_region p n addr /\ assurance_region(word_sub(stackpointer:int64)(word 48))8 addr)`;
  ASSUME `!addr. ~(assurance_region p n addr /\ assurance_region(word 0x102417d0)97 addr)`;
  ASSUME `clw_file_code lib_file`;
  ASSUME `fb_full_image lib_file(read memory(u7:x86state))(read memory u7)(read memory u7)`;
  ASSUME `n<2 EXP 64`;
  ASSUME `read RIP(u7:x86state)=read(memory :> bytes64(word(cleansepltpc+12184)))(u6:x86state)`;
  ASSUME `read(memory :> bytes64(word 0x23003fd8))(u6:x86state)=word 0x102417d0`;
  ASSUME `read RSP(u7:x86state)=word_sub(word_sub(stackpointer:int64)(word 40))(word 8)`;
  ASSUME `read(memory :> bytes64(word_sub(word_sub(stackpointer:int64)(word 40))(word 8)))(u7:x86state)=word(pc+44)`;
  ASSUME `read RDI(u7:x86state)=p`;ASSUME `read RSI(u7:x86state)=word n`;
  ASSUME `~read DF(u7:x86state)`;ASSUME `~bit 18(read rflags(u7:x86state))`;
  ASSUME `val(word_sub(stackpointer:int64)(word 48))=val stackpointer-48`;
  ASSUME `val(word_sub(stackpointer:int64)(word 48)) MOD 16=8`;
  ASSUME `assurance_span_ok(\a. xp a /\ ordinary a)0x102417d0 97`;
  ASSUME `assurance_span_ok(\a. wp a /\ ordinary a)(val(p:int64))n`;
  ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`;
  ASSUME `assurance_canonical48(val(read ABI_FS_BASE(a:abi_omitted_state)))`;
  ASSUME `bytes_loaded(u7:x86state)(word pc)c3_caller_mc`;
  ASSUME `bytes_loaded(u7:x86state)(word 0x23001030)c3_crypto_plt_prefix`;
  ASSUME `bytes_loaded(u7:x86state)(word cleansepltpc)c3_cleanse_plt_prefix`;
  ASSUME `bytes_loaded(u7:x86state)(word 0x10241840)crypto_memcmp_mc`;
  ASSUME `bytes_loaded(u7:x86state)(word 0x102417d0)openssl_cleanse_mc`;
  ASSUME `read(memory :> bytes64(word 0x23003fd0))(u7:x86state)=word 0x10241840`;
  ASSUME `read(memory :> bytes64(word 0x23003fd8))(u7:x86state)=word 0x102417d0`;
  ASSUME `read RBX(u7:x86state)=p`;ASSUME `read RBP(u7:x86state)=word n`;ASSUME `read R12(u7:x86state)=q`;
  ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 8)))(u7:x86state)=read R13(initial:x86state)`;
  ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 16)))(u7:x86state)=read R12(initial:x86state)`;
  ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 24)))(u7:x86state)=read RBP(initial:x86state)`;
  ASSUME `read(memory :> bytes64(word_sub(stackpointer:int64)(word 32)))(u7:x86state)=read RBX(initial:x86state)`;
  ASSUME `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(u7:x86state)addr=m addr`;
  ASSUME `!i. i<n ==> read memory(u7:x86state)(word_add p(word i))=m(word_add p(word i))`;
  ASSUME `!i. i<n ==> read memory(u7:x86state)(word_add q(word i))=m(word_add q(word i))`;
  ASSUME `read R13(u7:x86state)=(if c3_equal m p q n then word 1 else word 0)`;
  ASSUME `read R14(u7:x86state)=read R14(initial:x86state)`;
  ASSUME `read R15(u7:x86state)=read R15(initial:x86state)`;
  SYM(ASSUME `587206944=pc`);SYM(ASSUME `587206720=cleansepltpc`)] in
 REWRITE_TAC[assurance_checked_run;bp_e2_cleanse_public_pre;bp_cleanse_pre;C_ARGUMENTS;c3_saved_prefix;c3_loaded_code;c3_got] THEN
 REWRITE_TAC[HT_WORD_SUB_SUB] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts THEN
 REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ;CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts);;
e C3_CLEANUP_ENDPOINT_PUBLIC_UNFOLD_TAC;;
print_endline "C3_CLEANUP_ENDPOINT_PUBLIC_UNFOLD_V1_RETURN";;
print_endline(string_of_term(snd(top_goal())));;
