(* C2 caller-specific recipe adaptation, not unchanged generic infrastructure.
   Actual eight original-machine transitions; no callee body execution.
   Named obligation O1: frozen C2_INITIAL_COMPARE_HANDOFF. *)
let C2_CRYPTO_PLT_ADDRESS = prove
 (`(word (0x22001120+18446744073709551376):int64)=word 0x22001030`,
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let C2_PREFIX_PROTECTION_TAC =
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x22001120,59)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x22001120:int64`;`59`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CALLER_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x22001030,6)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x22001030:int64`;`6`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CRYPTO_PLT_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x22001040,6)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x22001040:int64`;`6`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CLEANSE_PLT_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x10241840,95)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x10241840:int64`;`95`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CRYPTO_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x102417d0,97)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x102417d0:int64`;`97`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CLEANSE_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x22003fd0,8)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x22003fd0:int64`;`8`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CRYPTO_GOT_READONLY_REGION];ALL_TAC] THEN
 SUBGOAL_THEN
  `nonoverlapping(word_sub (stackpointer:int64) (word 32),32)
                 (word 0x22003fd8,8)` ASSUME_TAC THENL
  [MATCH_MP_TAC (SPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 32)`;`32`;`word 0x22003fd8:int64`;`8`]
      C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[C2_CLEANSE_GOT_READONLY_REGION];ALL_TAC];;
let C2_PREFIX_PERMISSION_TAC =
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n)
    (val(stackpointer:int64)-32) 32` ASSUME_TAC THENL
  [MATCH_MP_TAC C2_SCRATCH_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_write wp ordinary stackpointer p q n m)
    (val(stackpointer:int64)-32) 32` ASSUME_TAC THENL
  [MATCH_MP_TAC C2_SCRATCH_WRITE_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001120 59`
  ASSUME_TAC THENL
  [MATCH_MP_TAC C2_CALLER_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001030 6`
  ASSUME_TAC THENL
  [MATCH_MP_TAC C2_CRYPTO_PLT_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n)
    0x22003fd0 8` ASSUME_TAC THENL
  [MATCH_MP_TAC C2_CRYPTO_GOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC];;
let rec C2_FINITE_FRAME_WIDEN_TAC gl =
 let left,_ = dest_binary "subsumed" (snd gl) in
 if is_binary ",," left then
  (MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    CONJ_TAC THENL [C2_FINITE_FRAME_WIDEN_TAC;
                    C2_FINITE_FRAME_WIDEN_TAC]]) gl
 else SUBSUMED_MAYCHANGE_TAC gl;;
let C2_INITIAL_COMPARE_HANDOFF = prove
 (c2_handoff_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_pre;c2_loaded_code;
              c2_got;C_ARGUMENTS] THEN
  STRIP_TAC THEN C2_PREFIX_PERMISSION_TAC THEN
  C2_PREFIX_PROTECTION_TAC THEN
  SUBGOAL_THEN `MAYCHANGE [] (s:x86state) s` ASSUME_TAC THENL
   [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
  ABBREV_TAC `r12initial=read R12 (s:x86state)` THEN
  ABBREV_TAC `rbpinitial=read RBP (s:x86state)` THEN
  ABBREV_TAC `rbxinitial=read RBX (s:x86state)` THEN
  ABBREV_TAC `pc=0x22001120` THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s1" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s2" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s3" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s4" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s5" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s6" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s7" THEN
  SUBGOAL_THEN `read RIP (s7:x86state)=word 0x22001030` ASSUME_TAC THENL
   [UNDISCH_TAC `read RIP (s7:x86state)=word(pc+18446744073709551376)` THEN
    EXPAND_TAC "pc" THEN REWRITE_TAC[C2_CRYPTO_PLT_ADDRESS];ALL_TAC] THEN
  ABBREV_TAC `pltpc=0x22001030` THEN
  C2_PLT_POLICY_CHECKED_STEP_TAC 0x22001030 "pltpc"
    C2_CRYPTO_PLT_EXEC C2_CALLER_SUBTHS "s8" THEN
  (fun gl -> print_endline "PREFIX20_NORMALIZE"; ALL_TAC gl) THEN
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV o
    REWRITE_RULE[C2_WORD_SUB_SUB]) THEN
  (fun gl -> print_endline "PREFIX20_WORD_OFFSETS"; ALL_TAC gl) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[
    WORD_RULE `word_sub (stackpointer:int64) (word 8) =
               word_add (word_sub stackpointer (word 32)) (word 24)`;
    WORD_RULE `word_sub (stackpointer:int64) (word 16) =
               word_add (word_sub stackpointer (word 32)) (word 16)`;
    WORD_RULE `word_sub (stackpointer:int64) (word 24) =
               word_add (word_sub stackpointer (word 32)) (word 8)`]) THEN
  (fun gl -> print_endline "PREFIX20_FRAME"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `c2_prefix_frame stackpointer (s:x86state) s8` ASSUME_TAC THENL
   [REWRITE_TAC[c2_prefix_frame] THEN (let pth = prove (`R (s:x86state) t ==> R subsumed D ==> D s t`,
       REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
    REWRITE_TAC[ETA_AX;SOME_FLAGS] THEN POP_ASSUM_LIST(K ALL_TAC) THEN C2_FINITE_FRAME_WIDEN_TAC;ALL_TAC] THEN
  SUBGOAL_THEN
   `!addr:int64. ~c2_scratch stackpointer (val addr)
       ==> read memory (s8:x86state) addr=m addr` ASSUME_TAC THENL
   [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `read memory (s8:x86state) addr=read memory (s:x86state) addr`
     (fun th -> ACCEPT_TAC (TRANS th
       (AP_THM (ASSUME `read memory (s:x86state)=m`) `addr:int64`))) THEN
    MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`addr:int64`;
      `s:x86state`;`s8:x86state`] C2_PREFIX_FRAME_BYTE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 immutable disjoint"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!addr. fb_immutable addr ==> ~c2_scratch stackpointer addr`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`wp:num->bool`;
     `ordinary:num->bool`] C2_LIBRARY_SCRATCH_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 image rebind"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `fb_full_image lib_file (read memory (s8:x86state))
      (read memory s8) (read memory s8)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
     `lib_padding:int64->byte`;`m:int64->byte`;`read memory (s8:x86state)`]
     C2_CLIENT_LIBRARY_REBIND) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ASSUME
     `!addr:int64. ~c2_scratch stackpointer (val addr)
       ==> read memory (s8:x86state) addr=m addr`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 p bytes"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!i. i<n ==> read memory (s8:x86state) (word_add p (word i))=
                  m(word_add p (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;
     `p:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s8:x86state`]
     C2_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 q bytes"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!i. i<n ==> read memory (s8:x86state) (word_add q (word i))=
                  m(word_add q (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;
     `q:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s8:x86state`]
     C2_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 stack align"; ALL_TAC gl) THEN
  MP_TAC (SPEC `stackpointer:int64` C2_CLIENT_STACK_ALIGNMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (fun gl -> print_endline "PREFIX26 code region"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!addr. ~(assurance_region (word_sub (stackpointer:int64) (word 32)) 32 addr /\
              assurance_region (word 0x10241840) 95 addr)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`word_sub (stackpointer:int64) (word 32)`;
      `word 0x10241840:int64`;`32`;`95`]
      C2_NONOVERLAPPING_REGION_DISJOINT) THEN
    ASM_SIMP_TAC[C2_STACK_SUB32_VALUE;VAL_WORD;DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (ARITH_RULE `32<=x /\ x<18446744073709551616 ==> x-32+32<=18446744073709551616`) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ACCEPT_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `stackpointer:int64` VAL_BOUND_64))];
    ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 endpoint unfold"; ALL_TAC gl) THEN
  REWRITE_TAC[assurance_checked_run;c2_crypto_ready;
              c2_saved_prefix;bp_e2_crypto_public_pre;
              bp_e2_crypto_pre;C_ARGUMENTS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[C2_WORD_SUB_SUB;c2_loaded_code;
                 c2_got;
    WORD_RULE `word_sub (stackpointer:int64) (word 8) =
               word_add (word_sub stackpointer (word 32)) (word 24)`;
    WORD_RULE `word_sub (stackpointer:int64) (word 16) =
               word_add (word_sub stackpointer (word 32)) (word 16)`;
    WORD_RULE `word_sub (stackpointer:int64) (word 24) =
               word_add (word_sub stackpointer (word 32)) (word 8)`] THEN
  EXPAND_TAC "pc" THEN EXPAND_TAC "pltpc" THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC (ARITH_RULE
     `32<=x /\ x<18446744073709551616 ==> x-32+8<18446744073709551616`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[];
     ACCEPT_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `stackpointer:int64` VAL_BOUND_64))];
    REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    (let kept=MATCH_MP (ISPECL [`stackpointer:int64`;`s:x86state`;`s8:x86state`]
       C2_PREFIX_OUTSIDE_SAVED_PRESERVED)
       (ASSUME `c2_prefix_frame stackpointer (s:x86state) s8`) in
     let ac=last(CONJUNCTS kept) in
     MESON_TAC[ac;ASSUME `~bit 18(read rflags (s:x86state))`]);
    MATCH_MP_TAC (REWRITE_RULE[ADD_CLAUSES] (ISPECL
      [`\addr:num. rp addr /\ ordinary addr`;
       `val(stackpointer:int64)-32`;`32`;`0`;`8`]
      R1_SECRET_SPAN_SUBSPAN)) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `addr:num` THEN
    (let disjoint=SPEC `addr:num` (ASSUME
      `!addr:num. ~(assurance_region (word_sub (stackpointer:int64) (word 32)) 32 addr /\
                    assurance_region (word 0x10241840) 95 addr)`) in
     let slot=REWRITE_RULE[c2_scratch] (ISPECL [`stackpointer:int64`;`addr:num`]
       C2_SCRATCH_SLOT_REGION) in
     MESON_TAC[disjoint;slot]);
    X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
    (let permissions=MATCH_MP (SPEC `addr:num` (ASSUME
      `!addr:num. lw_image_domain addr ==> rp addr /\ ordinary addr /\
        (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`))
      (ASSUME `lw_image_domain (addr:num)`) in
     MESON_TAC[permissions])]);;
