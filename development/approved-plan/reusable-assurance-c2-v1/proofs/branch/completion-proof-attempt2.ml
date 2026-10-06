(* Named O3/O5 endpoint transport. Public postconditions and explicit frames
   only; no target-specific supplier instruction theorem or callee decoder. *)
let C2_PRE_FACT_TAC (asl,w) =
 let expanded=REWRITE_RULE[c2_pre] (ASSUME
  `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
    stackpointer ra p q n m rp wp xp ordinary (initial:x86state,a)`) in
 ACCEPT_TAC(find(fun th -> aconv w (concl th)) (CONJUNCTS expanded)) (asl,w);;
let C2_COMPARE_PHASE_FACTS_TAC =
 MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
  `lib_padding:int64->byte`;`client_file:num->byte`;`client_rw:int64->byte`;
  `client_padding:int64->byte`;`stackpointer:int64`;`ra:int64`;
  `p:int64`;`q:int64`;`n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;
  `xp:num->bool`;`ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
  `returned:x86state`] C2_COMPARE_STRONG_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
 MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
  `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
  `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
  `returned:x86state`] C2_COMPARE_INITIAL_FACTS) THEN
 ANTS_TAC THENL
  [CONJ_TAC THENL [C2_PRE_FACT_TAC;ASM_REWRITE_TAC[]];STRIP_TAC];;
let C2_HEADER_COMPLETED_RUN = prove
 (c2_header_completed_run_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C2_COMPARE_PHASE_FACTS_TAC THEN
  MATCH_MP_TAC(ISPECL [`3`;`c2_branch_header_post p q n m (returned:x86state)`;
    `c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary initial a:x86state->bool`;
    `c2_segment_policy stackpointer p q n m rp wp xp ordinary:num->x86state->x86state->bool`;
    `returned:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:x86state` THEN DISCH_TAC THEN
    REWRITE_TAC[c2_header_completed] THEN EXISTS_TAC `returned:x86state` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
      `m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
      `ordinary:num->bool`;`returned:x86state`] C2_BRANCH_HEADER) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `c2_saved_prefix stackpointer p q n m (initial:x86state) returned` THEN
      REWRITE_TAC[c2_saved_prefix;c2_loaded_code] THEN MESON_TAC[];
      MATCH_MP_TAC C2_CALLER_FETCH_SPAN THEN C2_PRE_FACT_TAC]]);;
let C2_HEADER_INITIAL_FACTS = prove
 (c2_header_initial_facts_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_header_completed lib_file stackpointer p q n m rp wp xp ordinary (initial:x86state) a t` THEN
  REWRITE_TAC[c2_header_completed] THEN
  DISCH_THEN(X_CHOOSE_THEN `returned:x86state` STRIP_ASSUME_TAC) THEN
  C2_COMPARE_PHASE_FACTS_TAC THEN
  UNDISCH_TAC `c2_branch_header_post p q n m (returned:x86state) t` THEN
  REWRITE_TAC[c2_branch_header_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_saved_prefix stackpointer p q n m (initial:x86state) t`
   ASSUME_TAC THENL
   [UNDISCH_TAC `c2_saved_prefix stackpointer p q n m (initial:x86state) returned` THEN
    REWRITE_TAC[c2_saved_prefix] THEN STRIP_TAC THEN
    REWRITE_TAC[c2_saved_prefix] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[C2_COMPARE_MEMORY_CODE_GOT_TRANSPORT;C2_COMPARE_MEMORY_SLOT_TRANSPORT];ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes64 (stackpointer:int64)) (t:x86state)=ra`
   ASSUME_TAC THENL
   [MP_TAC(ISPECL [`returned:x86state`;`t:x86state`;`stackpointer:int64`]
     C2_COMPARE_MEMORY_SLOT_TRANSPORT) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `read (memory :> bytes64 (stackpointer:int64)) (initial:x86state)=ra`
     ASSUME_TAC THENL [C2_PRE_FACT_TAC;ASM_MESON_TAC[]];ALL_TAC] THEN
  SUBGOAL_THEN `~bit 18(read rflags (t:x86state))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`returned:x86state`;`t:x86state`] C2_HEADER_FRAME_AC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (initial:x86state) t`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`initial:x86state`;
     `returned:x86state`;`t:x86state`] C2_HEADER_BEFORE_CLEANUP_COMPOSE) THEN
    ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]]);;
let C2_HEADER_PHASE_FACTS_TAC =
 MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
  `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
  `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
  `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
  `initial:x86state`;`a:abi_omitted_state`;`t:x86state`] C2_HEADER_INITIAL_FACTS) THEN
 ASM_REWRITE_TAC[] THEN STRIP_TAC;;
let C2_SUFFIX_PERMISSIONS_TAC =
 REPEAT CONJ_TAC THENL
  [C2_PRE_FACT_TAC;C2_PRE_FACT_TAC;
   MATCH_MP_TAC C2_SCRATCH_READ_SPAN THEN CONJ_TAC THEN C2_PRE_FACT_TAC;
   MATCH_MP_TAC C2_INCOMING_READ_SPAN THEN C2_PRE_FACT_TAC;
   MATCH_MP_TAC C2_CALLER_FETCH_SPAN THEN C2_PRE_FACT_TAC];;
let C2_HEADER_TRUE_MIDDLE_READY = prove
 (c2_header_true_middle_ready_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C2_HEADER_PHASE_FACTS_TAC THEN
  REWRITE_TAC[c2_middle_ready] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes64 (stackpointer:int64)) (initial:x86state)=ra`
   ASSUME_TAC THENL [C2_PRE_FACT_TAC;ASM_REWRITE_TAC[]]);;
let C2_HEADER_FALSE_SUFFIX_READY = prove
 (c2_header_false_suffix_ready_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C2_HEADER_PHASE_FACTS_TAC THEN
  UNDISCH_TAC `c2_saved_prefix stackpointer p q n m (initial:x86state) t` THEN
  REWRITE_TAC[c2_saved_prefix;c2_loaded_code] THEN STRIP_TAC THEN
  REWRITE_TAC[c2_suffix_pre] THEN ASM_REWRITE_TAC[] THEN C2_SUFFIX_PERMISSIONS_TAC);;
let C2_CLEANSE_SUFFIX_READY = prove
 (c2_cleanse_suffix_ready_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;`lib_padding:int64->byte`;
   `client_file:num->byte`;`client_rw:int64->byte`;`client_padding:int64->byte`;
   `stackpointer:int64`;`ra:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
   `rp:num->bool`;`wp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
   `initial:x86state`;`a:abi_omitted_state`;`t:x86state`] C2_CLEANSE_RETURNED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c2_loaded_code (t:x86state)` THEN
  REWRITE_TAC[c2_loaded_code] THEN STRIP_TAC THEN
  REWRITE_TAC[c2_suffix_pre] THEN ASM_REWRITE_TAC[] THEN
  C2_SUFFIX_PERMISSIONS_TAC);;
