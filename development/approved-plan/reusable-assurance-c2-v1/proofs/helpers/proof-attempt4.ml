(* Adapted C0 pure helper proof recipes. No C0 proof source is imported and no supplier body is unfolded. Not checked yet. *)
let C2_POLICY_SPAN = prove
 (c2_policy_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\(addr:num). P addr /\ assurance_region (p:int64) n addr` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC R1_SECRET_SPAN_REGION THEN
  ASM_REWRITE_TAC[]);;
let C2_SPAN_POINT = prove
 (c2_span_point_statement,
  REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `addr-val(p:int64)`) THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a+(b-a)=b`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;MESON_TAC[]]);;

let C2_REGION_NONOVERLAPPING = prove
 (c2_region_nonoverlapping_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(p:int64)`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(q:int64)`) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let C2_STACK_SUB32_VALUE = prove
 (`!stackpointer:int64. 32<=val stackpointer ==> val(word_sub stackpointer (word 32))=val stackpointer-32`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
let C2_SCRATCH_READ_SPAN = prove
 (c2_scratch_read_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 32))=val stackpointer-32`
    ASSUME_TAC THENL
   [MATCH_MP_TAC C2_STACK_SUB32_VALUE THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  MP_TAC (SPECL [`\(addr:num). rp addr /\ ordinary addr`;
    `c2_allowed_read rp ordinary stackpointer p q n`;`word_sub (stackpointer:int64) (word 32)`;`32`] C2_POLICY_SPAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_read;c2_scratch] THEN
  MESON_TAC[]);;
let C2_SCRATCH_WRITE_SPAN = prove
 (c2_scratch_write_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 32))=val stackpointer-32`
    ASSUME_TAC THENL
   [MATCH_MP_TAC C2_STACK_SUB32_VALUE THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  MP_TAC (SPECL [`\(addr:num). wp addr /\ ordinary addr`;
    `c2_allowed_write wp ordinary stackpointer p q n m`;`word_sub (stackpointer:int64) (word 32)`;`32`] C2_POLICY_SPAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_write;c2_scratch] THEN
  MESON_TAC[]);;
let C2_CALLER_FETCH_SPAN = prove
 (c2_caller_fetch_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`\(addr:num). xp addr /\ ordinary addr`;
    `c2_allowed_fetch xp ordinary`;
    `word 0x22001120:int64`;`59`] C2_POLICY_SPAN) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_fetch] THEN MESON_TAC[]);;
let C2_CRYPTO_PLT_FETCH_SPAN = prove
 (c2_crypto_plt_fetch_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`\(addr:num). xp addr /\ ordinary addr`;
    `c2_allowed_fetch xp ordinary`;
    `word 0x22001030:int64`;`6`] C2_POLICY_SPAN) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_fetch] THEN MESON_TAC[]);;
let C2_CLEANSE_PLT_FETCH_SPAN = prove
 (c2_cleanse_plt_fetch_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`\(addr:num). xp addr /\ ordinary addr`;
    `c2_allowed_fetch xp ordinary`;
    `word 0x22001040:int64`;`6`] C2_POLICY_SPAN) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_fetch] THEN MESON_TAC[]);;

let C2_WRITABLE_READONLY_NONOVERLAPPING = prove
 (c2_writable_readonly_nonoverlapping_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_REGION_NONOVERLAPPING THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `assurance_span_ok (\addr. wp addr /\ ordinary addr) (val(p:int64)) n` THEN
    REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[];
    ASM_MESON_TAC[C2_SPAN_POINT]]);;
let C2_CALLER_READONLY_REGION = prove
 (c2_caller_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c2_image_domain;c2_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CRYPTO_PLT_READONLY_REGION = prove
 (c2_crypto_plt_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c2_image_domain;c2_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CLEANSE_PLT_READONLY_REGION = prove
 (c2_cleanse_plt_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c2_image_domain;c2_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CRYPTO_READONLY_REGION = prove
 (c2_crypto_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;lw_image_domain;lw_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CLEANSE_READONLY_REGION = prove
 (c2_cleanse_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;lw_image_domain;lw_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CRYPTO_GOT_READONLY_REGION = prove
 (c2_crypto_got_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c2_image_domain;c2_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C2_CLEANSE_GOT_READONLY_REGION = prove
 (c2_cleanse_got_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c2_image_domain;c2_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let C2_CRYPTO_GOT_READ_SPAN = prove
 (c2_crypto_got_read_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`\(addr:num). rp addr /\ ordinary addr`;
    `c2_allowed_read rp ordinary stackpointer p q n`;
    `word 0x22003fd0:int64`;`8`] C2_POLICY_SPAN) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_read] THEN MESON_TAC[]);;
let C2_CLEANSE_GOT_READ_SPAN = prove
 (c2_cleanse_got_read_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`\(addr:num). rp addr /\ ordinary addr`;
    `c2_allowed_read rp ordinary stackpointer p q n`;
    `word 0x22003fd8:int64`;`8`] C2_POLICY_SPAN) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c2_allowed_read] THEN MESON_TAC[]);;
let C2_INCOMING_READ_SPAN = prove
 (c2_incoming_read_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL [`\(addr:num). rp addr /\ ordinary addr`;
    `c2_allowed_read rp ordinary stackpointer p q n`;
    `stackpointer:int64`;`8`] C2_POLICY_SPAN) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c2_allowed_read] THEN MESON_TAC[]);;

let C2_LIBRARY_IMMUTABLE_READONLY = prove
 (c2_library_immutable_readonly_statement,
  REWRITE_TAC[fb_immutable;lw_image_domain;lw_image_write] THEN ARITH_TAC);;
let C2_CLIENT_IMMUTABLE_READONLY = prove
 (c2_immutable_readonly_statement,
  REWRITE_TAC[c2_immutable;c2_image_domain;
              c2_image_write] THEN ARITH_TAC);;
let C2_SPAN_WORD_ADD_REGION = prove
 (c2_span_word_add_region_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `i<2 EXP 64 /\ val(p:int64)+i<2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC);;

let C2_LIBRARY_SCRATCH_DISJOINT = prove
 (c2_library_scratch_disjoint_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `assurance_span_ok (\addr. wp addr /\ ordinary addr)
     (val(word_sub (stackpointer:int64) (word 32))) 32` ASSUME_TAC THENL
   [ASM_SIMP_TAC[C2_STACK_SUB32_VALUE];ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) (addr:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[C2_SPAN_POINT;c2_scratch];
    ASM_MESON_TAC[C2_LIBRARY_IMMUTABLE_READONLY]]);;
let C2_UNCHANGED_BUFFER = prove
 (c2_unchanged_buffer_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC[C2_SPAN_WORD_ADD_REGION]);;
let C2_NONOVERLAPPING_REGION_DISJOINT = prove
 (c2_nonoverlapping_region_disjoint_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C2_SCRATCH_SLOT_REGION = prove
 (c2_scratch_slot_region_statement,
  REWRITE_TAC[c2_scratch;assurance_region] THEN ARITH_TAC);;

let C2_CLIENT_STACK_ALIGNMENT = prove
 (c2_stack_alignment_statement,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`val(stackpointer:int64)-32`;`32`;`16`] MOD_ADD_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `32 <= x ==> x-32+32=x`;MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES;MOD_MOD_REFL]);;

let c2_stack_segment_span_statement = `!P (stackpointer:int64) k width. 32<=val stackpointer /\ k<=32 /\ width<=k /\ assurance_span_ok P (val stackpointer-32) 32 ==> assurance_span_ok P (val(word_sub stackpointer (word k))) width`;;
let C2_STACK_SEGMENT_SPAN = prove
 (c2_stack_segment_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k<2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word k))=val stackpointer-k`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    SUBGOAL_THEN `k<=val(stackpointer:int64)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;ASM_REWRITE_TAC[]];ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`P:num->bool`;`val(stackpointer:int64)-32`;`32`;
                `32-k`;`width:num`] R1_SECRET_SPAN_SUBSPAN) THEN
  ASM_SIMP_TAC[ARITH_RULE `32<=x /\ k<=32 ==> (x-32)+(32-k)=x-k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let C2_SCRATCH_BYTE_NONOVERLAPPING = prove
 (c2_scratch_byte_nonoverlapping_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_REGION_NONOVERLAPPING THEN
  ASM_SIMP_TAC[C2_STACK_SUB32_VALUE] THEN
  CONJ_TAC THENL
   [MP_TAC (SPEC `addr:int64` VAL_BOUND_64) THEN ARITH_TAC;
    CONJ_TAC THENL
     [MP_TAC (SPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
      UNDISCH_TAC `~c2_scratch stackpointer (val(addr:int64))` THEN
      ASM_SIMP_TAC[c2_scratch;assurance_region;
                   C2_STACK_SUB32_VALUE] THEN
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC]]);;
let C2_PREFIX_FRAME_BYTE = prove
 (c2_prefix_frame_byte_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_prefix_frame] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping(addr:int64,1)(word_sub stackpointer (word 32),32)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C2_SCRATCH_BYTE_NONOVERLAPPING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes8 (addr:int64)) (t:x86state) =
    read (memory :> bytes8 addr) (s:x86state)` MP_TAC THENL
   [MATCH_MP_TAC (ISPECL
      [`memory :> bytes8 (addr:int64)`;
       `[RIP;RSP;RBX;RBP;R12]:((x86state,int64)component)list`;
       `SOME_FLAGS:((x86state,bool)component)list`;
       `[memory :> bytes(word_sub (stackpointer:int64) (word 32),32)]`;
       `[events]:((x86state,uarch_event list)component)list`;
       `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL] THEN REWRITE_TAC[SOME_FLAGS;ALL] THEN
    REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
    REWRITE_TAC[BYTES8_ELEMENT;READ_COMPONENT_COMPOSE;READ_ELEMENT]]);;

let C2_CLIENT_LIBRARY_REBIND = prove
 (c2_library_rebind_statement,
  REWRITE_TAC[fb_full_image;fb_reference_image] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `fb_immutable (val(a:int64))` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
