(* C2-only O4 caller linkage binding fact, proved from the frozen GOT.
   Constant addresses are artifact facts, not generic composition infrastructure. *)
let C2_GOT_TARGETS_CANONICAL = prove
 (`!s:x86state. c2_got s
    ==> assurance_canonical48(val(read (memory :> bytes64 (word 0x22003fd0)) s)) /\
        assurance_canonical48(val(read (memory :> bytes64 (word 0x22003fd8)) s))`,
  GEN_TAC THEN REWRITE_TAC[c2_got] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;
(* C2-specific adaptation of exposed C0 machine handoff recipe.
   O3/O4: actual true branch MOV/MOV/CALL/PLT sequence, supplier interface only.
   No old caller theorem imports, no supplier instruction semantics. *)
let C2_CLEANSE_PLT_ADDRESS = prove
 (`(word (0x22001120+18446744073709551392):int64)=word 0x22001040`,
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let C2_MIDDLE_PERMISSION_TAC =
 C2_PREFIX_PERMISSION_TAC THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_fetch xp ordinary) 0x22001040 6`
  ASSUME_TAC THENL
  [MATCH_MP_TAC C2_CLEANSE_PLT_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c2_allowed_read rp ordinary stackpointer p q n)
    0x22003fd8 8` ASSUME_TAC THENL
  [MATCH_MP_TAC C2_CLEANSE_GOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC];;
let C2_TRUE_MIDDLE_HANDOFF = prove
 (c2_middle_handoff_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary (initial,a)` THEN
  REWRITE_TAC[c2_pre] THEN STRIP_TAC THEN

  UNDISCH_TAC `c2_middle_ready stackpointer p q n m (initial:x86state) returned` THEN
  REWRITE_TAC[c2_middle_ready] THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_saved_prefix stackpointer p q n m initial (returned:x86state)` THEN
  REWRITE_TAC[c2_saved_prefix;c2_loaded_code;c2_got] THEN
  STRIP_TAC THEN
  (fun gl -> print_endline "MIDDLE9_SAVED_UNFOLDED"; ALL_TAC gl) THEN
  C2_MIDDLE_PERMISSION_TAC THEN
  (fun gl -> print_endline "MIDDLE9_PERMISSIONS_DONE"; ALL_TAC gl) THEN
  C2_PREFIX_PROTECTION_TAC THEN
  (fun gl -> print_endline "MIDDLE9_PROTECTION_DONE"; ALL_TAC gl) THEN
  SUBGOAL_THEN `MAYCHANGE [] (returned:x86state) returned` ASSUME_TAC THENL
   [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
  ABBREV_TAC `pc=0x22001120` THEN
  SUBGOAL_THEN `read RIP (returned:x86state)=word(pc+40)` ASSUME_TAC THENL
   [EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_STEP1"; ALL_TAC gl) THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s1" THEN
  (fun gl -> print_endline "MIDDLE9_AFTER_STEP1"; ALL_TAC gl) THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s2" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s3" THEN
  SUBGOAL_THEN `read RIP (s3:x86state)=word 0x22001040` ASSUME_TAC THENL
   [UNDISCH_TAC `read RIP (s3:x86state)=word(pc+18446744073709551392)` THEN
    EXPAND_TAC "pc" THEN REWRITE_TAC[C2_CLEANSE_PLT_ADDRESS];ALL_TAC] THEN
  SUBGOAL_THEN `c2_got (s3:x86state)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c2_got];ALL_TAC] THEN
  MP_TAC (SPEC `s3:x86state` C2_GOT_TARGETS_CANONICAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `pltpc=0x22001040` THEN
  C2_PLT_POLICY_CHECKED_STEP_TAC 0x22001040 "pltpc"
    C2_CLEANSE_PLT_EXEC C2_CALLER_SUBTHS "s4" THEN
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[C2_WORD_SUB_SUB]) THEN
  SUBGOAL_THEN `c2_middle_frame stackpointer (returned:x86state) s4` ASSUME_TAC THENL
   [REWRITE_TAC[c2_middle_frame] THEN
    (let pth=prove (`R (s:x86state) t ==> R subsumed D ==> D s t`,
      REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
     FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
    REWRITE_TAC[ETA_AX] THEN POP_ASSUM_LIST(K ALL_TAC) THEN C2_FINITE_FRAME_WIDEN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (initial:x86state) s4`
    ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`initial:x86state`;
     `returned:x86state`;`s4:x86state`] C2_MIDDLE_BEFORE_CLEANUP_COMPOSE) THEN
    ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN
   `!addr:int64. ~c2_scratch stackpointer (val addr)
     ==> read memory (s4:x86state) addr=m addr` ASSUME_TAC THENL
   [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `read memory (returned:x86state) addr` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`addr:int64`;`returned:x86state`;`s4:x86state`]
       C2_MIDDLE_FRAME_BYTE) THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];ALL_TAC] THEN
  SUBGOAL_THEN
   `!addr. fb_immutable addr ==> ~c2_scratch stackpointer addr`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`wp:num->bool`;
     `ordinary:num->bool`] C2_LIBRARY_SCRATCH_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 image rebind"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `fb_full_image lib_file (read memory (s4:x86state))
      (read memory s4) (read memory s4)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
     `lib_padding:int64->byte`;`m:int64->byte`;`read memory (s4:x86state)`]
     C2_CLIENT_LIBRARY_REBIND) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ASSUME
     `!addr:int64. ~c2_scratch stackpointer (val addr)
       ==> read memory (s4:x86state) addr=m addr`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 p bytes"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!i. i<n ==> read memory (s4:x86state) (word_add p (word i))=
                  m(word_add p (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;
     `p:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s4:x86state`]
     C2_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 q bytes"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!i. i<n ==> read memory (s4:x86state) (word_add q (word i))=
                  m(word_add q (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;
     `q:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`s4:x86state`]
     C2_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  (fun gl -> print_endline "PREFIX26 stack align"; ALL_TAC gl) THEN
  MP_TAC (SPEC `stackpointer:int64` C2_CLIENT_STACK_ALIGNMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_P_PROTECTION"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `nonoverlapping(p:int64,n)(word 0x102417d0,97)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`wp:num->bool`;`ordinary:num->bool`;`p:int64`;`n:num`;
      `word 0x102417d0:int64`;`97`] C2_WRITABLE_READONLY_NONOVERLAPPING) THEN
    ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_MESON_TAC[C2_CLEANSE_READONLY_REGION];ALL_TAC] THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_P_REGION"; ALL_TAC gl) THEN
  SUBGOAL_THEN
   `!addr. ~(assurance_region (p:int64) n addr /\ assurance_region (word 0x102417d0) 97 addr)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`p:int64`;`word 0x102417d0:int64`;`n:num`;`97`]
      C2_NONOVERLAPPING_REGION_DISJOINT) THEN
    ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    (fun gl -> print_endline "MIDDLE9_P_BOUND_GOAL";print_term(snd gl);print_newline();ALL_TAC gl) THEN
    ACCEPT_TAC (CONV_RULE NUM_REDUCE_CONV
     (CONJUNCT1 (REWRITE_RULE[assurance_span_ok]
      (ASSUME `assurance_span_ok (\addr:num. wp addr /\ ordinary addr) (val(p:int64)) n`))));ALL_TAC] THEN
  SUBGOAL_THEN `val(stackpointer:int64)+8<=18446744073709551616`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LT_IMP_LE THEN
    ACCEPT_TAC(ASSUME `val(stackpointer:int64)+8<18446744073709551616`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (stackpointer:int64)) (s4:x86state)=
       read (memory :> bytes64 stackpointer) initial` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `read (memory :> bytes64 (stackpointer:int64)) (returned:x86state)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC C2_MIDDLE_FRAME_INCOMING_SLOT THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];ALL_TAC] THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_ENDPOINT_UNFOLD"; ALL_TAC gl) THEN
  REWRITE_TAC[assurance_checked_run;c2_cleanse_ready;
    c2_saved_prefix;bp_e2_cleanse_public_pre;bp_e2_cleanse_pre;C_ARGUMENTS] THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_ENDPOINT_NUM"; ALL_TAC gl) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun gl -> print_endline "MIDDLE9_BEFORE_ENDPOINT_ASM"; ALL_TAC gl) THEN
  ASM_REWRITE_TAC[C2_WORD_SUB_SUB;c2_loaded_code;c2_got] THEN
  EXPAND_TAC "pc" THEN EXPAND_TAC "pltpc" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ASSUME `32<=val(stackpointer:int64)`) THEN
    MP_TAC(ASSUME `val(stackpointer:int64)+8<18446744073709551616`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;
    REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC (REWRITE_RULE[ADD_CLAUSES] (ISPECL
     [`\addr:num. rp addr /\ ordinary addr`;`val(stackpointer:int64)-32`;`32`;`0`;`8`]
      R1_SECRET_SPAN_SUBSPAN)) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `addr:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `c2_scratch (stackpointer:int64) addr` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`addr:num`] C2_SCRATCH_SLOT_REGION) THEN
      ASM_REWRITE_TAC[];ALL_TAC] THEN
    ACCEPT_TAC(MATCH_MP
     (NOT_ELIM(SPEC `addr:num` (ASSUME
      `!addr:num. ~(assurance_region (p:int64) n addr /\ c2_scratch stackpointer addr)`)))
     (CONJ (ASSUME `assurance_region (p:int64) n addr`)
       (ASSUME `c2_scratch (stackpointer:int64) addr`)))]);;
