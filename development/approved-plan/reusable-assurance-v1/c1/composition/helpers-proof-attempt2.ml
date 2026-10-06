(* Preserves helpers1 interrupted before first object. Use the checked
   direct public frame adapter, without SUBSUMED_TRANS or recursive widening. *)
(* Composition of already checked public endpoint/frame facts only.
   No caller or callee execution rule is created in this source. *)
let C1_TAIL_FRAME_INCLUDED = prove
 (c1_tail_frame_included_statement,
  GEN_TAC THEN REWRITE_TAC[c1_frame;SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC);;
let C1_TAIL_FRAME_COMPOSE = prove
 (c1_tail_frame_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV)
    [GSYM(SPEC `stackpointer:int64` C1_FRAME_IDEMPOTENT)] THEN
  REWRITE_TAC[SEQ] THEN EXISTS_TAC `returned:x86state` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[subsumed]
    (SPEC `stackpointer:int64` C1_TAIL_FRAME_INCLUDED)) THEN ASM_REWRITE_TAC[]);;
let C1_COMPOSITION_ACCESS_TAC =
 MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
   `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
   `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
   `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
   `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;
   `a:abi_omitted_state`;`returned:x86state`] C1_CRYPTO_COMPLETED_ACCESS) THEN
 ANTS_TAC THENL [ASM_REWRITE_TAC[];STRIP_TAC];;
let C1_COMPLETED_TAIL_PRE = prove
 (c1_completed_tail_pre_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1_COMPOSITION_ACCESS_TAC THEN
  REWRITE_TAC[c1_tail_pre] THEN ASM_REWRITE_TAC[]);;
let C1_COMPLETED_TAIL_POST = prove
 (c1_completed_tail_post_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1_COMPOSITION_ACCESS_TAC THEN
  UNDISCH_TAC `c1_tail_post stackpointer ra (read RAX (returned:x86state))
     (read memory returned) returned (final:x86state)` THEN
  REWRITE_TAC[c1_tail_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1_frame stackpointer (initial:x86state) final` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`initial:x86state`;
      `returned:x86state`;`final:x86state`] C1_TAIL_FRAME_COMPOSE) THEN
    ASM_REWRITE_TAC[];ALL_TAC] THEN
  MP_TAC (MATCH_MP (ISPECL [`stackpointer:int64`;`initial:x86state`;
    `final:x86state`] C1_FRAME_SAVED_PRESERVED)
    (ASSUME `c1_frame stackpointer (initial:x86state) final`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `read DF (final:x86state)=F` ASSUME_TAC THENL
   [let tail_frame=ASSUME
      `(MAYCHANGE [RIP;RSP;RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])
         (returned:x86state) final` in
    let tail_full=MATCH_MP (REWRITE_RULE[subsumed]
      (SPEC `stackpointer:int64` C1_TAIL_FRAME_INCLUDED)) tail_frame in
    let facts=MATCH_MP (ISPECL [`stackpointer:int64`;`returned:x86state`;
      `final:x86state`] C1_FRAME_SAVED_PRESERVED) tail_full in
    let df_eq=el 6 (CONJUNCTS facts) in
    REWRITE_TAC[df_eq] THEN ACCEPT_TAC(ASSUME `read DF (returned:x86state)=F`);
    ALL_TAC] THEN
  (let memory=ASSUME `read memory (final:x86state)=read memory (returned:x86state)` in
   let slot=MATCH_MP (ISPECL [`returned:x86state`;`final:x86state`;
     `stackpointer:int64`] C1_COMPLETION_MEMORY_SLOT_TRANSPORT) memory in
   let code_got=MATCH_MP (ISPECL [`returned:x86state`;`final:x86state`]
     C1_COMPLETION_MEMORY_CODE_GOT_TRANSPORT) memory in
   REWRITE_TAC[c1_scalar_post] THEN ASM_REWRITE_TAC[slot;code_got] THEN
   REPEAT CONJ_TAC THEN
   (fun (asl,w) -> print_endline "C1_COMPOSITION_POST_RESIDUAL";
      print_term w;print_newline();FAIL_TAC "C1 composition post residual" (asl,w))));;
let C1_SHIFTED_SEGMENT_POLICY = prove
 (c1_shifted_segment_policy_statement,
  REWRITE_TAC[c1_step_policy;c1_segment_policy] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C1_STEP_POLICY_QUALIFIED = prove
 (c1_step_policy_qualified_statement,
  REWRITE_TAC[c1_step_policy;c1_segment_policy] THEN MESON_TAC[]);;
let C1_COMPLETED_TAIL_RUN = prove
 (c1_completed_tail_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`5`;
    `c1_tail_post stackpointer ra (read RAX (returned:x86state))
       (read memory returned) returned`;
    `c1_scalar_post stackpointer ra p q n m (initial:x86state)`;
    `c1_step_policy stackpointer p q n rp wp xp ordinary`;
    `returned:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `final:x86state` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
      `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
      `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
      `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;
      `a:abi_omitted_state`;`returned:x86state`;`final:x86state`]
       C1_COMPLETED_TAIL_POST) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1_TAIL_CHECKED THEN
    MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
      `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
      `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
      `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;
      `wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;
      `a:abi_omitted_state`;`returned:x86state`] C1_COMPLETED_TAIL_PRE) THEN
    ASM_REWRITE_TAC[]]);;
