(* Attempt 3, written after literal-freeze-v1.json.
   Public post projection, memory transport, and generic frame algebra only. *)
let C1_COMPLETION_MEMORY_SLOT_TRANSPORT = prove
 (c1_completion_memory_slot_transport_statement,
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN MESON_TAC[]);;
let C1_COMPLETION_MEMORY_CODE_GOT_TRANSPORT = prove
 (c1_completion_memory_code_got_transport_statement,
  REWRITE_TAC[c1_loaded_code;c1_got;bytes_loaded;READ_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;
let C1_PREFIX_FRAME_INCLUDED = prove
 (c1_prefix_frame_included_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_prefix_frame;c1_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C1_CRYPTO_PUBLIC_FRAME_INCLUDED = prove
 (c1_crypto_public_frame_included_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_crypto_public_frame;c1_frame;SOME_FLAGS] THEN
  SUBSUMED_MAYCHANGE_TAC);;
let C1_FRAME_IDEMPOTENT = prove
 (c1_frame_idempotent_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_frame;SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC);;
let C1_CRYPTO_FRAME_COMPOSE = prove
 (c1_crypto_frame_compose_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1_frame stackpointer (initial:x86state) entry` ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C1_PREFIX_FRAME_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1_frame stackpointer (entry:x86state) returned` ASSUME_TAC THENL
   [MP_TAC(SPEC `stackpointer:int64` C1_CRYPTO_PUBLIC_FRAME_INCLUDED) THEN
    REWRITE_TAC[subsumed] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV) [GSYM C1_FRAME_IDEMPOTENT] THEN
  REWRITE_TAC[seq] THEN EXISTS_TAC `entry:x86state` THEN ASM_REWRITE_TAC[]);;
let C1_FRAME_SAVED_PRESERVED = prove
 (c1_frame_saved_preserved_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_frame] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM READ_BITELEMENT;GSYM READ_COMPONENT_COMPOSE] THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
   let component=hd(snd(strip_comb(lhand(snd gl)))) in
   (MATCH_MP_TAC (ISPECL
    [component;
     `[RIP;RSP;RAX;RDI;RSI;RDX;R10;R11]:((x86state,int64)component)list`;
     `SOME_FLAGS:((x86state,bool)component)list`;
     `[memory :> bytes(word_sub (stackpointer:int64) (word 16),8)]:
       ((x86state,num)component)list`;
     `[events]:((x86state,uarch_event list)component)list`;
     `s:x86state`;`t:x86state`] R1_SECRET_FOUR_FRAME_PRESERVATION) THEN
    ASM_REWRITE_TAC[ALL;CONJUNCT1 MAYCHANGE;SEQ_ID] THEN
    REWRITE_TAC[SOME_FLAGS;ALL] THEN REPEAT CONJ_TAC THEN
    ORTHOGONAL_COMPONENTS_TAC) gl));;
let C1_CRYPTO_RESULT_TRANSPORT = prove
 (c1_crypto_result_transport_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c1_crypto_ready lib_file (stackpointer:int64) p q n m rp xp ordinary
      (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c1_crypto_ready] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 16))
      (word 0x21001119) p q n (read events (entry:x86state))
      (read memory entry) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i<n ==> read memory (entry:x86state) (word_add p (word i))=
                 read memory entry (word_add q (word i))) <=>
    (!i. i<n ==> (m:int64->byte)(word_add p (word i))=m(word_add q (word i)))`
   ASSUME_TAC THENL [ASM_MESON_TAC[];ASM_REWRITE_TAC[]]);;
let C1_CRYPTO_RESULT_01 = prove
 (c1_crypto_result_01_statement,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;
let C1_CRYPTO_RETURN_STACK = prove
 (c1_crypto_return_stack_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES;VAL_WORD;DIMINDEX_64;
    ARITH_RULE `16<=x ==> 8<=x`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPEC `stackpointer:int64` C1_STACK_SUB16_VALUE) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
let C1_INCOMING_READ_SPAN = prove
 (c1_incoming_read_span_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC R1_SECRET_SPAN_MONO THEN
  EXISTS_TAC `\addr. (rp addr /\ ordinary addr) /\
    assurance_region (stackpointer:int64) 8 addr` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c1_allowed_read] THEN MESON_TAC[];
    MATCH_MP_TAC R1_SECRET_SPAN_REGION THEN ASM_REWRITE_TAC[]]);;
let C1_CRYPTO_COMPLETED_FACTS = prove
 (c1_crypto_completed_facts_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_crypto_completed] THEN
  DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `read RAX (returned:x86state)=
     (if (!i. i<n ==> (m:int64->byte)(word_add p (word i))=
                       m(word_add q (word i))) then word 0 else word 1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL
     [`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;`m:int64->byte`;
      `initial:x86state`;`entry:x86state`;`returned:x86state`;
      `lib_file:num->byte`;`rp:num->bool`;`xp:num->bool`;
      `ordinary:num->bool`;`a:abi_omitted_state`]
     C1_CRYPTO_RESULT_TRANSPORT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `c1_crypto_ready lib_file (stackpointer:int64) p q n m rp xp ordinary
      (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c1_crypto_ready] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 16))
      (word 0x21001119) p q n (read events (entry:x86state))
      (read memory entry) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1_frame stackpointer (initial:x86state) returned` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL
     [`stackpointer:int64`;`initial:x86state`;`entry:x86state`;
      `returned:x86state`] C1_CRYPTO_FRAME_COMPOSE) THEN
    ASM_REWRITE_TAC[c1_crypto_public_frame];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1_loaded_code (returned:x86state) /\ c1_got returned`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[C1_COMPLETION_MEMORY_CODE_GOT_TRANSPORT];ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (stackpointer:int64)) (returned:x86state)=
     read (memory :> bytes64 stackpointer) (entry:x86state)` ASSUME_TAC THENL
   [MATCH_MP_TAC C1_COMPLETION_MEMORY_SLOT_TRANSPORT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`stackpointer:int64`;`initial:x86state`;`returned:x86state`]
   C1_FRAME_SAVED_PRESERVED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
let C1_CRYPTO_COMPLETED_RUN = prove
 (c1_crypto_completed_run_statement,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`bp_assurance_call_steps n`;
    `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 16))
       (word 0x21001119) p q n (read events (entry:x86state)) (read memory entry) entry`;
    `c1_crypto_completed lib_file (stackpointer:int64) p q n m rp xp ordinary
       (initial:x86state) a:x86state->bool`;
    `c1_segment_policy (stackpointer:int64) p q n rp wp xp ordinary:
       num->x86state->x86state->bool`;
    `entry:x86state`] RA_CHECKED_RUN_POST_MONO) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `returned:x86state` THEN DISCH_TAC THEN
    REWRITE_TAC[c1_crypto_completed] THEN EXISTS_TAC `entry:x86state` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC (ISPECL
     [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
      `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
      `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;
      `entry:x86state`] C1_CRYPTO_SEGMENT_APPLICATION) THEN ASM_REWRITE_TAC[]]);;
let C1_CRYPTO_COMPLETED_ACCESS = prove
 (c1_crypto_completed_access_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL
   [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;`n:num`;
    `m:int64->byte`;`rp:num->bool`;`xp:num->bool`;`ordinary:num->bool`;
    `initial:x86state`;`a:abi_omitted_state`;`returned:x86state`]
   C1_CRYPTO_COMPLETED_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c1_pre lib_file lib_rw lib_padding client_file client_rw client_padding
      (stackpointer:int64) ra p q n m rp wp xp ordinary (initial:x86state,a)` THEN
  REWRITE_TAC[c1_pre] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `read RSP (returned:x86state)=word_sub (stackpointer:int64) (word 8)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C1_CRYPTO_RETURN_STACK THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN
   `(read RAX (returned:x86state)=word 0 \/ read RAX returned=word 1) /\
    (read RAX returned=word 0 <=>
      (!i. i<n ==> (m:int64->byte)(word_add p (word i))=m(word_add q (word i))))`
   (CONJUNCTS_THEN ASSUME_TAC) THENL
   [MATCH_MP_TAC C1_CRYPTO_RESULT_01 THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN
   `assurance_span_ok (c1_allowed_read rp ordinary (stackpointer:int64) p q n)
      (val stackpointer) 8` ASSUME_TAC THENL
   [MATCH_MP_TAC C1_INCOMING_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN
   `assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001110 22`
   ASSUME_TAC THENL
   [MATCH_MP_TAC C1_CALLER_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN
   `bytes_loaded (returned:x86state) (word 0x21001110) c1_crypto_caller_mc`
   ASSUME_TAC THENL
   [UNDISCH_TAC `c1_loaded_code (returned:x86state)` THEN
    REWRITE_TAC[c1_loaded_code] THEN MESON_TAC[];ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
