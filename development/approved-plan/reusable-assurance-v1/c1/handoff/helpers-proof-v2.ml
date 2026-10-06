(* Consolidates the 23 warm-audited helper source portions.
   Independent clean reconstruction remains pending; failed files retained. *)
(* C1 local arithmetic, permission and memory obligations. All terms were
   frozen in helper-statements-v1.ml. No supplier execution rule is built. *)
let C1_STACK_SUB16_VALUE = prove
 (c1_stack_sub16_value_statement,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
let C1_STACK_ALIGNMENT = prove
 (c1_stack_alignment_statement,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[C1_STACK_SUB16_VALUE] THEN
  MP_TAC (SPECL [`val(stackpointer:int64)-16`;`16`;`16`] MOD_ADD_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `16<=x ==> x-16+16=x`;MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[ADD_CLAUSES;MOD_MOD_REFL]);;
let C1_SPAN_POINT = prove
 (c1_span_point_statement,
  REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `addr-val(p:int64)`) THEN
  ASM_SIMP_TAC[ARITH_RULE `a<=b ==> a+(b-a)=b`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;MESON_TAC[]]);;
let C1_SPAN_WORD_ADD_REGION = prove
 (c1_span_word_add_region_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[assurance_span_ok;assurance_region] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `i<2 EXP 64 /\ val(p:int64)+i<2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;MOD_LT] THEN ASM_ARITH_TAC);;
let C1_REGION_NONOVERLAPPING = prove
 (c1_region_nonoverlapping_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(p:int64)`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `val(q:int64)`) THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C1_NONOVERLAPPING_REGION_DISJOINT = prove
 (c1_nonoverlapping_region_disjoint_statement,
  REWRITE_TAC[assurance_region;NONOVERLAPPING_QFREE;
              VAL_WORD_SUB_CASES;DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC);;
let C1_WRITABLE_READONLY_NONOVERLAPPING = prove
 (c1_writable_readonly_nonoverlapping_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1_REGION_NONOVERLAPPING THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `assurance_span_ok (\addr. wp addr /\ ordinary addr) (val(p:int64)) n` THEN
    REWRITE_TAC[assurance_span_ok] THEN MESON_TAC[];
    ASM_MESON_TAC[C1_SPAN_POINT]]);;
let C1_LIBRARY_REBIND = prove
 (c1_library_rebind_statement,
  REWRITE_TAC[fb_full_image;fb_reference_image] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `fb_immutable(val(a:int64))` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let C1_LIBRARY_IMMUTABLE_READONLY = prove
 (c1_library_immutable_readonly_statement,
  REWRITE_TAC[fb_immutable;lw_image_domain;lw_image_write] THEN ARITH_TAC);;
let C1_CALLER_READONLY_REGION = prove
 (c1_caller_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c1_image_domain;c1_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C1_PLT_READONLY_REGION = prove
 (c1_plt_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c1_image_domain;c1_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C1_GOT_READONLY_REGION = prove
 (c1_got_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;c1_image_domain;c1_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C1_CRYPTO_READONLY_REGION = prove
 (c1_crypto_readonly_region_statement,
  REWRITE_TAC[assurance_region;VAL_WORD;DIMINDEX_64;lw_image_domain;lw_image_write] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;
let C1_SLOT_READ_SPAN = prove
 (c1_slot_read_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 16))=val stackpointer-16`
   ASSUME_TAC THENL [ASM_SIMP_TAC[C1_STACK_SUB16_VALUE];ALL_TAC] THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (rp addr /\ ordinary addr) /\
    assurance_region (word_sub (stackpointer:int64) (word 16)) 8 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_read;c1_call_slot] THEN MESON_TAC[];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(ASSUME
     `val(word_sub (stackpointer:int64) (word 16))=val stackpointer-16`)] THEN
    MATCH_MP_TAC R1_SECRET_SPAN_REGION THEN ASM_REWRITE_TAC[]]);;
let C1_SLOT_WRITE_SPAN = prove
 (c1_slot_write_span_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 16))=val stackpointer-16`
   ASSUME_TAC THENL [ASM_SIMP_TAC[C1_STACK_SUB16_VALUE];ALL_TAC] THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (wp addr /\ ordinary addr) /\
    assurance_region (word_sub (stackpointer:int64) (word 16)) 8 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_write;c1_call_slot] THEN MESON_TAC[];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(ASSUME
     `val(word_sub (stackpointer:int64) (word 16))=val stackpointer-16`)] THEN
    MATCH_MP_TAC R1_SECRET_SPAN_REGION THEN ASM_REWRITE_TAC[]]);;
let C1_CALLER_FETCH_SPAN = prove
 (c1_caller_fetch_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (xp addr /\ ordinary addr) /\
    assurance_region (word 0x21001110) 22 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_fetch] THEN MESON_TAC[];
    MP_TAC (ISPECL [`\addr:num. xp addr /\ ordinary addr`;
      `word 0x21001110:int64`;`22`] R1_SECRET_SPAN_REGION) THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;
let C1_PLT_FETCH_SPAN = prove
 (c1_plt_fetch_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (xp addr /\ ordinary addr) /\
    assurance_region (word 0x21001030) 6 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_fetch] THEN MESON_TAC[];
    MP_TAC (ISPECL [`\addr:num. xp addr /\ ordinary addr`;
      `word 0x21001030:int64`;`6`] R1_SECRET_SPAN_REGION) THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;
let C1_GOT_READ_SPAN = prove
 (c1_got_read_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (rp addr /\ ordinary addr) /\
    assurance_region (word 0x21003fd8) 8 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_read] THEN MESON_TAC[];
    MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;
      `word 0x21003fd8:int64`;`8`] R1_SECRET_SPAN_REGION) THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;
let C1_LIBRARY_SLOT_DISJOINT = prove
 (c1_library_slot_disjoint_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `assurance_span_ok (\addr. wp addr /\ ordinary addr)
    (val(word_sub (stackpointer:int64) (word 16))) 8` ASSUME_TAC THENL
   [ASM_SIMP_TAC[C1_STACK_SUB16_VALUE];ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(wp:num->bool) (addr:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[C1_SPAN_POINT;c1_call_slot];
    ASM_MESON_TAC[C1_LIBRARY_IMMUTABLE_READONLY]]);;
let C1_SLOT_BYTE_NONOVERLAPPING = prove
 (c1_slot_byte_nonoverlapping_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1_REGION_NONOVERLAPPING THEN
  ASM_SIMP_TAC[C1_STACK_SUB16_VALUE] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `addr:int64` VAL_BOUND_64) THEN ARITH_TAC;
    CONJ_TAC THENL
     [MP_TAC(SPEC `stackpointer:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC;
      UNDISCH_TAC `~c1_call_slot stackpointer (val(addr:int64))` THEN
      ASM_SIMP_TAC[c1_call_slot;assurance_region;C1_STACK_SUB16_VALUE] THEN
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC]]);;
let C1_PREFIX_FRAME_BYTE = prove
 (c1_prefix_frame_byte_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_prefix_frame] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping(addr:int64,1)(word_sub stackpointer (word 16),8)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C1_SLOT_BYTE_NONOVERLAPPING THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes8 (addr:int64)) (t:x86state)=
    read (memory :> bytes8 addr) (s:x86state)` MP_TAC THENL
   [MATCH_MP_TAC (ISPECL
     [`memory :> bytes8 (addr:int64)`;
      `[RIP;RSP]:((x86state,int64)component)list`;
      `SOME_FLAGS:((x86state,bool)component)list`;
      `[memory :> bytes(word_sub (stackpointer:int64) (word 16),8)]`;
      `[events]:((x86state,uarch_event list)component)list`;
      `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;SOME_FLAGS] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC;
    REWRITE_TAC[BYTES8_ELEMENT;READ_COMPONENT_COMPOSE;READ_ELEMENT]]);;
let C1_PREFIX_FRAME_INCOMING_SLOT = prove
 (c1_prefix_frame_incoming_slot_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_prefix_frame] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping(stackpointer:int64,8)
    (word_sub stackpointer (word 16),8)` ASSUME_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_QFREE;VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (ISPECL
    [`memory :> bytes64 (stackpointer:int64)`;
     `[RIP;RSP]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[memory :> bytes(word_sub (stackpointer:int64) (word 16),8)]`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
  ASM_REWRITE_TAC[ALL;SOME_FLAGS] THEN REPEAT CONJ_TAC THEN ORTHOGONAL_COMPONENTS_TAC);;
let C1_UNCHANGED_BUFFER = prove
 (c1_unchanged_buffer_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[C1_SPAN_WORD_ADD_REGION]);;
