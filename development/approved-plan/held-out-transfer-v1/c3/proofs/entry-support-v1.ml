(* A construction attempt: C3-specific code arrays, actual48-byte footprint and site facts.
   No supplier body execution, new generic law, decoder or callback algorithm. *)
let C3_CALLER_RAW_EXEC = X86_MK_EXEC_RULE c3_caller_mc;;
let C3_CRYPTO_PLT_RAW_EXEC = X86_MK_EXEC_RULE c3_crypto_plt_prefix;;
let C3_CLEANSE_PLT_RAW_EXEC = X86_MK_EXEC_RULE c3_cleanse_plt_prefix;;
let C3_CRYPTO_PLT_EXEC = R1_NORMALIZE_EXEC_RULE C3_CRYPTO_PLT_RAW_EXEC;;
let C3_CLEANSE_PLT_EXEC = R1_NORMALIZE_EXEC_RULE C3_CLEANSE_PLT_RAW_EXEC;;
let C3_CALLER_SUBTHS = [CONJ(fst C3_CALLER_RAW_EXEC)TRUTH;
 CONJ(fst C3_CRYPTO_PLT_RAW_EXEC)TRUTH;CONJ(fst C3_CLEANSE_PLT_RAW_EXEC)TRUTH;
 CONJ BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH TRUTH;
 CONJ BP_PUBLIC_OPENSSL_CLEANSE_CODE_LENGTH TRUTH];;
let C3_STACK_SUB48_VALUE = prove
 (`!stackpointer:int64. 48<=val stackpointer ==> val(word_sub stackpointer(word 48))=val stackpointer-48`,
 REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
let C3_STACK_SEGMENT_SPAN = prove
 (`!P (stackpointer:int64) k width. 48<=val stackpointer /\ k<=48 /\ width<=k /\ assurance_span_ok P (val stackpointer-48)48 ==> assurance_span_ok P (val(word_sub stackpointer(word k)))width`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `k<2 EXP 64` ASSUME_TAC THENL[ASM_ARITH_TAC;ALL_TAC] THEN
 SUBGOAL_THEN `val(word_sub(stackpointer:int64)(word k))=val stackpointer-k` ASSUME_TAC THENL
 [ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
  SUBGOAL_THEN `k<=val(stackpointer:int64)` ASSUME_TAC THENL[ASM_ARITH_TAC;ASM_REWRITE_TAC[]];ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN MP_TAC(SPECL[`P:num->bool`;`val(stackpointer:int64)-48`;`48`;`48-k`;`width:num`]R1_SECRET_SPAN_SUBSPAN) THEN
 ASM_SIMP_TAC[ARITH_RULE`48<=x /\ k<=48 ==> (x-48)+(48-k)=x-k`] THEN
 DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C3_EVENT_SPAN_TAC = HT_EVENT_SPAN_TAC C3_STACK_SEGMENT_SPAN;;
(* Fixed parameter instantiations only; frozen callback behavior unchanged. *)
let C3_POLICY_CHECKED_STEP_TAC rule subths name = HT_CHECKED_STEP_TAC
 (HT_PUBLIC_CODE_POLICY_TAC c3_segment_policy
  `c3_allowed_fetch (xp:num->bool)(ordinary:num->bool)` 89 "pc" (snd rule) C3_EVENT_SPAN_TAC)
 rule subths name;;
let C3_PLT_CHECKED_STEP_TAC abbreviation rule subths name = HT_CHECKED_STEP_TAC
 (HT_PUBLIC_CODE_POLICY_TAC c3_segment_policy
  `c3_allowed_fetch (xp:num->bool)(ordinary:num->bool)` 6 abbreviation (snd rule) C3_EVENT_SPAN_TAC)
 rule subths name;;
let C3_CALLER_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x23001120)89 addr ==> c3_image_domain addr /\ ~c3_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c3_image_domain;c3_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CRYPTO_PLT_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x23001030)6 addr ==> c3_image_domain addr /\ ~c3_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c3_image_domain;c3_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CLEANSE_PLT_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x23001040)6 addr ==> c3_image_domain addr /\ ~c3_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c3_image_domain;c3_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CRYPTO_GOT_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x23003fd0)8 addr ==> c3_image_domain addr /\ ~c3_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c3_image_domain;c3_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CLEANSE_GOT_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x23003fd8)8 addr ==> c3_image_domain addr /\ ~c3_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c3_image_domain;c3_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CRYPTO_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x10241840)95 addr ==> lw_image_domain addr /\ ~lw_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;lw_image_domain;lw_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_CLEANSE_READONLY_REGION = prove
 (`!addr. assurance_region(word 0x102417d0)97 addr ==> lw_image_domain addr /\ ~lw_image_write addr`,
 REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;lw_image_domain;lw_image_write] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C3_SCRATCH_READ_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. 48<=val(stackpointer:int64) /\ assurance_span_ok(\addr. rp addr /\ ordinary addr)(val(stackpointer:int64)-48)48
 ==> assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val(stackpointer:int64)-48)48`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `val(word_sub(stackpointer:int64)(word 48))=val stackpointer-48` ASSUME_TAC THENL[MATCH_MP_TAC C3_STACK_SUB48_VALUE THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(SPECL[`\(addr:num). rp addr /\ ordinary addr`;`c3_allowed_read rp ordinary stackpointer p q n`;`word_sub(stackpointer:int64)(word 48)`;`48`]HT_POLICY_SPAN) THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_read;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_SCRATCH_WRITE_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. 48<=val(stackpointer:int64) /\ assurance_span_ok(\addr. wp addr /\ ordinary addr)(val(stackpointer:int64)-48)48
 ==> assurance_span_ok(c3_allowed_write wp ordinary stackpointer p q n m)(val(stackpointer:int64)-48)48`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 SUBGOAL_THEN `val(word_sub(stackpointer:int64)(word 48))=val stackpointer-48` ASSUME_TAC THENL[MATCH_MP_TAC C3_STACK_SUB48_VALUE THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(SPECL[`\(addr:num). wp addr /\ ordinary addr`;`c3_allowed_write wp ordinary stackpointer p q n m`;`word_sub(stackpointer:int64)(word 48)`;`48`]HT_POLICY_SPAN) THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_write;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_CALLER_FETCH_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. xp addr /\ ordinary addr)(0x23001120)89
 ==> assurance_span_ok(c3_allowed_fetch xp ordinary)(0x23001120)89`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). xp addr /\ ordinary addr`;`c3_allowed_fetch xp ordinary`;`word 0x23001120:int64`;`89`]HT_POLICY_SPAN) THEN
 REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_fetch;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_CRYPTO_PLT_FETCH_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. xp addr /\ ordinary addr)(0x23001030)6
 ==> assurance_span_ok(c3_allowed_fetch xp ordinary)(0x23001030)6`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). xp addr /\ ordinary addr`;`c3_allowed_fetch xp ordinary`;`word 0x23001030:int64`;`6`]HT_POLICY_SPAN) THEN
 REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_fetch;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_CLEANSE_PLT_FETCH_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. xp addr /\ ordinary addr)(0x23001040)6
 ==> assurance_span_ok(c3_allowed_fetch xp ordinary)(0x23001040)6`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). xp addr /\ ordinary addr`;`c3_allowed_fetch xp ordinary`;`word 0x23001040:int64`;`6`]HT_POLICY_SPAN) THEN
 REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_fetch;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_CRYPTO_GOT_READ_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. rp addr /\ ordinary addr)(0x23003fd0)8
 ==> assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(0x23003fd0)8`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). rp addr /\ ordinary addr`;`c3_allowed_read rp ordinary stackpointer p q n`;`word 0x23003fd0:int64`;`8`]HT_POLICY_SPAN) THEN
 REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_read;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_CLEANSE_GOT_READ_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. rp addr /\ ordinary addr)(0x23003fd8)8
 ==> assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(0x23003fd8)8`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). rp addr /\ ordinary addr`;`c3_allowed_read rp ordinary stackpointer p q n`;`word 0x23003fd8:int64`;`8`]HT_POLICY_SPAN) THEN
 REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_read;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_INCOMING_READ_SPAN = prove
 (`!stackpointer p q:int64 n m rp wp xp ordinary. assurance_span_ok(\addr. rp addr /\ ordinary addr)(val(stackpointer:int64))8
 ==> assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)(val(stackpointer:int64))8`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(SPECL[`\(addr:num). rp addr /\ ordinary addr`;`c3_allowed_read rp ordinary stackpointer p q n`;`stackpointer:int64`;`8`]HT_POLICY_SPAN) THEN
 ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
 REWRITE_TAC[c3_allowed_read;c3_scratch;assurance_region] THEN MESON_TAC[]);;
let C3_STACK_CALLER_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. c3_image_domain addr ==> (wp addr <=> c3_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x23001120,89)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x23001120:int64`;`48`;`89`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CALLER_READONLY_REGION]]);;
let C3_STACK_CRYPTO_PLT_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. c3_image_domain addr ==> (wp addr <=> c3_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x23001030,6)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x23001030:int64`;`48`;`6`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CRYPTO_PLT_READONLY_REGION]]);;
let C3_STACK_CLEANSE_PLT_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. c3_image_domain addr ==> (wp addr <=> c3_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x23001040,6)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x23001040:int64`;`48`;`6`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CLEANSE_PLT_READONLY_REGION]]);;
let C3_STACK_CRYPTO_GOT_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. c3_image_domain addr ==> (wp addr <=> c3_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x23003fd0,8)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x23003fd0:int64`;`48`;`8`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CRYPTO_GOT_READONLY_REGION]]);;
let C3_STACK_CLEANSE_GOT_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. c3_image_domain addr ==> (wp addr <=> c3_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x23003fd8,8)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x23003fd8:int64`;`48`;`8`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CLEANSE_GOT_READONLY_REGION]]);;
let C3_STACK_CRYPTO_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. lw_image_domain addr ==> (wp addr <=> lw_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x10241840,95)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x10241840:int64`;`48`;`95`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CRYPTO_READONLY_REGION]]);;
let C3_STACK_CLEANSE_DISJOINT = prove
 (`!stackpointer:int64 wp ordinary. 48<=val stackpointer /\
 assurance_span_ok(\addr. wp addr /\ ordinary addr)(val stackpointer-48)48 /\
 (!addr. lw_image_domain addr ==> (wp addr <=> lw_image_write addr))
 ==> nonoverlapping(word_sub stackpointer(word 48),48)(word 0x102417d0,97)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MATCH_MP_TAC(ISPECL[`word_sub(stackpointer:int64)(word 48)`;`word 0x102417d0:int64`;`48`;`97`]HT_REGION_NONOVERLAPPING) THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE;VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
 REPEAT CONJ_TAC THENL
 [MP_TAC(CONV_RULE NUM_REDUCE_CONV(SPEC `stackpointer:int64`VAL_BOUND_64)) THEN ASM_ARITH_TAC;
  X_GEN_TAC `addr:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) addr` ASSUME_TAC THENL
  [MP_TAC(ISPECL[`\(addr:num). wp addr /\ ordinary addr`;`word_sub(stackpointer:int64)(word 48)`;`48`;`addr:num`]HT_SPAN_POINT) THEN
   ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  ASM_MESON_TAC[C3_CLEANSE_READONLY_REGION]]);;
let C3_SCRATCH_BYTE_NONOVERLAPPING = prove
 (`!stackpointer addr:int64. 48<=val stackpointer /\ ~c3_scratch stackpointer(val addr)
 ==> nonoverlapping(addr,1)(word_sub stackpointer(word 48),48)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HT_REGION_NONOVERLAPPING THEN
 ASM_SIMP_TAC[C3_STACK_SUB48_VALUE] THEN REPEAT CONJ_TAC THENL
 [MP_TAC(SPEC `addr:int64`VAL_BOUND_64) THEN ARITH_TAC;
  MP_TAC(SPEC `stackpointer:int64`VAL_BOUND_64) THEN ASM_ARITH_TAC;
  UNDISCH_TAC `~c3_scratch stackpointer(val(addr:int64))` THEN
  ASM_SIMP_TAC[c3_scratch;assurance_region;C3_STACK_SUB48_VALUE] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC]);;
let C3_PREFIX_FRAME_BYTE = prove
 (`!stackpointer addr:int64 s t:x86state. 48<=val stackpointer /\
 ~c3_scratch stackpointer(val addr) /\ c3_prefix_frame stackpointer s t
 ==> read memory t addr=read memory s addr`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_prefix_frame] THEN STRIP_TAC THEN
 SUBGOAL_THEN `nonoverlapping(addr:int64,1)(word_sub stackpointer(word 48),48)` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_SCRATCH_BYTE_NONOVERLAPPING THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `read(memory :> bytes8(addr:int64))(t:x86state)=read(memory :> bytes8 addr)(s:x86state)` MP_TAC THENL
 [MATCH_MP_TAC(ISPECL[`memory :> bytes8(addr:int64)`;
  `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
  `SOME_FLAGS:((x86state,bool)component)list`;
  `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
  `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
  ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
  REWRITE_TAC[BYTES8_ELEMENT;READ_COMPONENT_COMPOSE;READ_ELEMENT]]);;
let C3_PREFIX_FRAME_OUTSIDE = prove
 (`!stackpointer:int64 s t:x86state. c3_prefix_frame stackpointer s t
 ==> read R13 t=read R13 s /\ read R14 t=read R14 s /\ read R15 t=read R15 s /\
 read DF t=read DF s /\ bit 18(read rflags t)=bit 18(read rflags s)`,
 REPEAT GEN_TAC THEN REWRITE_TAC[c3_prefix_frame] THEN DISCH_TAC THEN
 REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
 REPEAT CONJ_TAC THENL
 [ MATCH_MP_TAC(ISPECL[`R13:(x86state,int64)component`;
 `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 MATCH_MP_TAC(ISPECL[`R14:(x86state,int64)component`;
 `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 MATCH_MP_TAC(ISPECL[`R15:(x86state,int64)component`;
 `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 MATCH_MP_TAC(ISPECL[`DF:(x86state,bool)component`;
 `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
 MATCH_MP_TAC(ISPECL[`rflags :> bitelement 18:(x86state,bool)component`;
 `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
 `SOME_FLAGS:((x86state,bool)component)list`;
 `[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)]`;
 `[events]:((x86state,uarch_event list)component)list`;`s:x86state`;`t:x86state`]R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
 ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC]);;
let C3_STACK_ALIGNMENT = prove
 (`!stackpointer:int64. 48<=val stackpointer /\ val stackpointer MOD16=8
 ==> val(word_sub stackpointer(word 48))=val stackpointer-48 /\
 val(word_sub stackpointer(word 48))MOD16=8`,
 REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
 MP_TAC(SPECL[`val(stackpointer:int64)-48`;`48`;`16`]MOD_ADD_MOD) THEN
 ASM_SIMP_TAC[ARITH_RULE`48<=x ==> x-48+48=x`;MOD_MOD_REFL] THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES;MOD_MOD_REFL]);;
let C3_FIRST_PLT_ADDRESS = prove
 (`(word(0x23001120+18446744073709551376):int64)=word 0x23001030`,
 GEN_REWRITE_TAC LAND_CONV[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
