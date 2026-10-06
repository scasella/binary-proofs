(* Consumes the same public comparison post/frame, not its instruction proof. *)
let C2_COMPARE_STRONG_FACTS = prove
 (c2_compare_strong_facts_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `32<=val(stackpointer:int64) /\ val stackpointer+8<=2 EXP 64`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
       (stackpointer:int64) ra p q n m rp wp xp ordinary (initial:x86state,a)` THEN
    REWRITE_TAC[c2_pre] THEN STRIP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
  MP_TAC(ISPECL [`lib_file:num->byte`;`stackpointer:int64`;`p:int64`;`q:int64`;
    `n:num`;`m:int64->byte`;`rp:num->bool`;`wp:num->bool`;`xp:num->bool`;
    `ordinary:num->bool`;`initial:x86state`;`a:abi_omitted_state`;`returned:x86state`]
   C2_COMPARE_INITIAL_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `c2_crypto_completed lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (returned:x86state)` THEN
  REWRITE_TAC[c2_crypto_completed] THEN
  DISCH_THEN(X_CHOOSE_THEN `entry:x86state` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
   `c2_crypto_ready lib_file (stackpointer:int64) p q n m rp wp xp ordinary
     (initial:x86state) a (entry:x86state)` THEN
  REWRITE_TAC[c2_crypto_ready] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `bp_assurance_call_post 0x10241840 (word_sub (stackpointer:int64) (word 32))
     (word 0x22001132) p q n (read events (entry:x86state))
     (read memory entry) entry (returned:x86state)` THEN
  REWRITE_TAC[bp_assurance_call_post] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stackpointer:int64`;`initial:x86state`;`entry:x86state`]
    C2_PREFIX_OUTSIDE_SAVED_PRESERVED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`entry:x86state`;`returned:x86state`]
    C2_CRYPTO_PUBLIC_SAVED_PRESERVED) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stackpointer:int64`;`initial:x86state`;`entry:x86state`]
    C2_PREFIX_FRAME_INCOMING_SLOT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 stackpointer) (returned:x86state)=
    read (memory :> bytes64 stackpointer) (entry:x86state)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`entry:x86state`;`returned:x86state`;`stackpointer:int64`]
      C2_COMPARE_MEMORY_SLOT_TRANSPORT) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `c2_before_cleanup_frame stackpointer (initial:x86state) returned`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`stackpointer:int64`;`initial:x86state`;
      `entry:x86state`;`returned:x86state`] C2_BEFORE_CLEANUP_FRAME_COMPOSE) THEN
    ASM_REWRITE_TAC[c2_crypto_public_frame];ALL_TAC] THEN
  UNDISCH_TAC
   `c2_pre lib_file lib_rw lib_padding client_file client_rw client_padding
     (stackpointer:int64) ra p q n m rp wp xp ordinary (initial:x86state,a)` THEN
  REWRITE_TAC[c2_pre] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c2_saved_prefix] THEN REPEAT CONJ_TAC THEN
  (ASM_MESON_TAC[] ORELSE
   (fun gl -> print_endline "C2_COMPARE_STRONG_FACTS_RESIDUAL";
    print_goal gl;FAIL_TAC "C2 comparison public frame consequence residual" gl)));;
