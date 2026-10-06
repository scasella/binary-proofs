(* Complete concrete cleanup7 source reconstruction attempt. All helper/theorem dependencies must be reconstructed; no saved goal/theorem object. *)

(* Literal source fragment from cleanup-handoff-definitions-v2.ml *)
(* Concrete C3 path obligation: first comparison return to actual unconditional
 cleanup entry through six caller instructions and the actual cleanse PLT.
 These local premises must be discharged in C3 composition from the original
 frozen precondition and public comparison post. They are not new public premises. *)
let c3_cleanup_handoff_abi_local_statement =
 `!lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary initial a entry returned.
 c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary (initial,a) /\
 c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary initial a entry /\
 bp_assurance_call_post 0x10241840 (word_sub stackpointer(word 48))
   (word 0x23001138) p q n (read events entry)(read memory entry) entry returned
 ==> assurance_checked_run 7
  (\t. bp_e2_cleanse_public_pre lib_file (read memory t)(read memory t)
      (word_sub stackpointer(word 48))(word 0x2300114c)p n(read memory t)
      rp wp xp ordinary (t,a) /\
      c3_saved_prefix stackpointer p q n m initial t /\
      read R13 t=(if c3_equal m p q n then word 1 else word 0) /\
      read R14 t=read R14 initial /\ read R15 t=read R15 initial /\
      (c3_frame stackpointer p q n m ,, MAYCHANGE [RBX;RBP;R12;R13]) initial t)
  (c3_segment_policy stackpointer p q n m rp wp xp ordinary) returned`;;

let C3_CLEANUP_PLT_ADDRESS = prove
 (`(word(0x23001120+18446744073709551392):int64)=word 0x23001040`,
 GEN_REWRITE_TAC LAND_CONV[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_64] THEN
 CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let C3_CLEANUP_INITIAL_FACTS_TAC =
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_RETURN_WORKING_STATE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_RETURN_SAVED_PREFIX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
  `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]
 C3_FIRST_COMPARISON_RESULT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 UNDISCH_TAC `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48))
   (word 0x23001138) p q n (read events(entry:x86state))(read memory entry) entry returned` THEN
 DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[bp_assurance_call_post] th)) THEN STRIP_TAC THEN
 SUBGOAL_THEN `read RSP(returned:x86state)=word_sub(stackpointer:int64)(word 40)` ASSUME_TAC THENL
 [ACCEPT_TAC(MATCH_MP(ISPECL[`stackpointer:int64`;`returned:x86state`]C3_FIRST_RETURN_STACKPOINTER)
   (CONJ(CONJUNCT1(CONJUNCT2(REWRITE_RULE[c3_pre](ASSUME
    `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      stackpointer ra p q n m rp wp xp ordinary (initial,a)`))))
    (ASSUME `val(read RSP(returned:x86state))=val(word_sub(stackpointer:int64)(word 48))+8`)));ALL_TAC];;
let C3_CLEANUP_PERMISSION_FACTS_TAC = UNDISCH_TAC `c3_saved_prefix stackpointer p q n m (initial:x86state)(returned:x86state)` THEN
 REWRITE_TAC[c3_saved_prefix;c3_loaded_code;c3_got] THEN STRIP_TAC THEN
 UNDISCH_TAC `c3_pre lib_file lib_rw lib_padding client_file client_rw client_padding
   stackpointer ra p q n m rp wp xp ordinary (initial,a)` THEN
 REWRITE_TAC[c3_pre;c3_loaded_code;c3_got;C_ARGUMENTS] THEN STRIP_TAC THEN
 C3_PREFIX_PERMISSION_TAC THEN C3_PREFIX_PROTECTION_TAC THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_fetch xp ordinary)0x23001040 6` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_CLEANSE_PLT_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `assurance_span_ok(c3_allowed_read rp ordinary stackpointer p q n)0x23003fd8 8` ASSUME_TAC THENL
 [MATCH_MP_TAC C3_CLEANSE_GOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `MAYCHANGE [] (returned:x86state) returned` ASSUME_TAC THENL
 [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
 ABBREV_TAC `pc=0x23001120` THEN
 SUBGOAL_THEN `read RIP(returned:x86state)=word(pc+24)` ASSUME_TAC THENL
 [UNDISCH_TAC `read RIP(returned:x86state)=word 0x23001138` THEN
  EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];ALL_TAC];;
let C3_CLEANUP_ACTUAL_SEVEN_TAC = 
 (* Concrete backward proof weakening: discard only five obsolete initial-state
    loaded-code facts after current-returned bindings have been derived. The
    frozen FIRST_X_ASSUM updater remains unchanged and now sees current facts. *)
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word pc)c3_caller_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001030)c3_crypto_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x23001040)c3_cleanse_plt_prefix` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x10241840)crypto_memcmp_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 UNDISCH_TAC `bytes_loaded(initial:x86state)(word 0x102417d0)openssl_cleanse_mc` THEN DISCH_THEN(K ALL_TAC) THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u1" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u2" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u3" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u4" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u5" THEN
 C3_POLICY_CHECKED_STEP_TAC C3_CALLER_RAW_EXEC C3_CALLER_SUBTHS "u6" THEN
 SUBGOAL_THEN `read RIP(u6:x86state)=word 0x23001040` ASSUME_TAC THENL
 [UNDISCH_TAC `read RIP(u6:x86state)=word(pc+18446744073709551392)` THEN
  EXPAND_TAC "pc" THEN REWRITE_TAC[C3_CLEANUP_PLT_ADDRESS];ALL_TAC] THEN
 ABBREV_TAC `cleansepltpc=0x23001040` THEN
 C3_PLT_CHECKED_STEP_TAC "cleansepltpc" C3_CLEANSE_PLT_EXEC C3_CALLER_SUBTHS "u7";;


(* Literal source fragment from cleanup-endpoint-core-v6.ml *)
(* Concrete cleanup7 endpoint derivations from the unchanged original public post,
 actual local frame and frozen input-domain clauses. No new generic rule. *)
let C3_CLEANUP_ENDPOINT_CORE_TAC =
 SUBGOAL_THEN `(MAYCHANGE [RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE [events]) (returned:x86state) u7` ASSUME_TAC THENL
 [MP_TAC(SPEC `stackpointer:int64`C3_CLEANUP_CONCRETE_FRAME_INCLUDED) THEN
 REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 MP_TAC(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
 `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_FIRST_RETURN_SAVED_PREFIX) THEN
 ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
 SUBGOAL_THEN `!addr:int64. ~c3_scratch stackpointer(val addr) ==> read memory(u7:x86state)addr=m addr` ASSUME_TAC THENL
 [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
 SUBGOAL_THEN `read memory(u7:x86state)addr=read memory(returned:x86state)addr` MP_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`addr:int64`;`returned:x86state`;`u7:x86state`]C3_CLEANUP_FRAME_BYTE) THEN ASM_REWRITE_TAC[];
 DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
 (let outside=el 7(CONJUNCTS(REWRITE_RULE[c3_saved_prefix](ASSUME `c3_saved_prefix stackpointer p q n m (initial:x86state)(returned:x86state)`))) in
 ACCEPT_TAC(MATCH_MP(SPEC `addr:int64`outside)(ASSUME `~c3_scratch stackpointer(val(addr:int64))`)))];ALL_TAC] THEN
 SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c3_scratch stackpointer addr` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]C3_PREFIX_LIBRARY_SCRATCH_DISJOINT) THEN ASM_REWRITE_TAC[] THEN
 X_GEN_TAC `addr:num` THEN DISCH_TAC THEN
 MP_TAC(MATCH_MP(SPEC `addr:num`(ASSUME `!addr. lw_image_domain addr ==> rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\ (wp addr <=> lw_image_write addr)`))(ASSUME `lw_image_domain(addr:num)`)) THEN MESON_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `fb_full_image lib_file(read memory(u7:x86state))(read memory u7)(read memory u7)` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_IMAGE_REBIND) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(u7:x86state)(word_add p(word i))=m(word_add p(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`p:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN `!i. i<n ==> read memory(u7:x86state)(word_add q(word i))=m(word_add q(word i))` ASSUME_TAC THENL
 [MATCH_MP_TAC(ISPECL[`\a:num. rp a /\ ordinary a`;`q:int64`;`n:num`;`stackpointer:int64`;`m:int64->byte`;`u7:x86state`]C3_PREFIX_INPUT_MEMORY) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 (let saved=CONJUNCT1(CONJUNCT2(REWRITE_RULE[c3_crypto_ready](ASSUME
 `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a (entry:x86state)`))) in
 let cs=CONJUNCTS(REWRITE_RULE[c3_saved_prefix]saved) in
 let eq=MATCH_MP(ISPECL[`m:int64->byte`;`read memory(entry:x86state)`;`p:int64`;`q:int64`;`n:num`]C3_INITIAL_LOGICAL_SNAPSHOT_EQ)(CONJ(el 8 cs)(el 9 cs)) in
 SUBGOAL_THEN `read R13(u7:x86state)=(if c3_equal m p q n then word 1 else word 0)` ASSUME_TAC THENL
 [REWRITE_TAC[ASSUME `read R13(u7:x86state)=word_join (word 0:(56)word)
 (if val(word_zx(if !i. i<n ==> read memory(entry:x86state)(word_add p(word i))=read memory entry(word_add q(word i)) then word 0:int64 else word 1):int32)=0 then word 1:byte else word 0)`;
 GSYM c3_equal;eq] THEN ASM_CASES_TAC `c3_equal m p q n` THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[];ALL_TAC]) THEN
 (let working=MATCH_MP(ISPECL[`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
 `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
 `initial:x86state`;`a:abi_omitted_state`;`entry:x86state`;`returned:x86state`]C3_FIRST_RETURN_WORKING_STATE)
 (CONJ(ASSUME `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a (entry:x86state)`)
 (ASSUME `bp_assurance_call_post 0x10241840 (word_sub(stackpointer:int64)(word 48))(word 0x23001138)p q n(read events(entry:x86state))(read memory entry)entry(returned:x86state)`)) in
 let ac=MATCH_MP(ISPECL[`stackpointer:int64`;`returned:x86state`;`u7:x86state`]C3_CLEANUP_FRAME_AC)
 (ASSUME `(MAYCHANGE [RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE [events]) (returned:x86state) u7`) in
 ASSUME_TAC(REWRITE_RULE[GSYM ac](last(CONJUNCTS working)))) THEN
 MP_TAC(MATCH_MP(SPEC `stackpointer:int64`C3_STACK_ALIGNMENT)(CONJ(ASSUME `48<=val(stackpointer:int64)`)(ASSUME `val(stackpointer:int64) MOD 16=8`))) THEN STRIP_TAC;;

(* Literal source fragment from cleanup-endpoint-total-frame-v1.ml *)
(* Fixed three-phase C3 frame composition; no generic sequencing automation. *)
let C3_CLEANUP_ENDPOINT_TOTAL_FRAME_TAC =
 SUBGOAL_THEN `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13]) (initial:x86state)u7` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[subsumed](ISPECL[`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`]C3_CLEANUP_TOTAL_FRAME_INCLUDED)) THEN
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `entry:x86state` THEN CONJ_TAC THENL
 [ACCEPT_TAC(last(CONJUNCTS(REWRITE_RULE[c3_crypto_ready](ASSUME `c3_crypto_ready lib_file stackpointer p q n m rp wp xp ordinary(initial:x86state)a(entry:x86state)`))));
 GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)[seq] THEN BETA_TAC THEN EXISTS_TAC `returned:x86state` THEN CONJ_TAC THENL
 [ACCEPT_TAC(last(CONJUNCTS(REWRITE_RULE[bp_assurance_call_post](ASSUME `bp_assurance_call_post 0x10241840(word_sub(stackpointer:int64)(word 48))(word 0x23001138)p q n(read events(entry:x86state))(read memory entry)entry(returned:x86state)`))));
 ACCEPT_TAC(ASSUME `(MAYCHANGE[RIP;RSP;R13;RSI;RDI] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE[memory :> bytes(word_sub(stackpointer:int64)(word 48),48)] ,, MAYCHANGE[events])(returned:x86state)(u7:x86state)`)] ];ALL_TAC];;

(* Literal source fragment from cleanup-endpoint-public-v4.ml *)
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
  CONV_RULE NUM_REDUCE_CONV(REWRITE_RULE[HT_WORD_SUB_SUB](ASSUME `read RSP(u7:x86state)=word_sub(word_sub(stackpointer:int64)(word 40))(word 8)`));
  CONV_RULE NUM_REDUCE_CONV(REWRITE_RULE[HT_WORD_SUB_SUB](ASSUME `read(memory :> bytes64(word_sub(word_sub(stackpointer:int64)(word 40))(word 8)))(u7:x86state)=word(pc+44)`));
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
 REWRITE_TAC[assurance_checked_run;bp_e2_cleanse_public_pre;bp_e2_cleanse_pre;C_ARGUMENTS;c3_saved_prefix;c3_loaded_code;c3_got] THEN
 REWRITE_TAC[HT_WORD_SUB_SUB] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts THEN
 REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64;WORD_EQ;CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC facts);;
let C3_CLEANUP_HANDOFF = prove(c3_cleanup_handoff_abi_local_statement,
 C3_CLEANUP_INITIAL_FACTS_TAC THEN C3_CLEANUP_PERMISSION_FACTS_TAC THEN
 C3_CLEANUP_ACTUAL_SEVEN_TAC THEN C3_CLEANUP_ENDPOINT_CORE_TAC THEN
 C3_CLEANUP_ENDPOINT_TOTAL_FRAME_TAC THEN C3_CLEANUP_ENDPOINT_PUBLIC_UNFOLD_TAC THEN
 REWRITE_TAC[ASSUME `(c3_frame stackpointer p q n m ,, MAYCHANGE[RBX;RBP;R12;R13])(initial:x86state)(u7:x86state)`]);;
if hyp C3_CLEANUP_HANDOFF<>[] || frees(concl C3_CLEANUP_HANDOFF)<>[] || not(aconv(concl C3_CLEANUP_HANDOFF)c3_cleanup_handoff_abi_local_statement) then failwith "C3_CLEANUP_HANDOFF literal/closure mismatch";;
print_endline "C3_CLEANUP_HANDOFF_DEVELOPMENT_CHECKED_NOT_ACCEPTANCE";;
