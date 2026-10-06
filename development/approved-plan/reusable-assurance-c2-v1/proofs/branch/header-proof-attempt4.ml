(* Each public equality case owns its own tactical subgoal list.
   This scopes the two-case proof; the literal header target is unchanged. *)
let C2_HEADER_BRANCH_TAC condition =
 RULE_ASSUM_TAC(REWRITE_RULE[ASSUME condition]) THEN
 ASSUME_TAC(ASSUME condition) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MAYCHANGE [] (returned:x86state) returned` ASSUME_TAC THENL
   [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
  ABBREV_TAC `pc=0x22001120` THEN
  SUBGOAL_THEN `read RIP (returned:x86state)=word(pc+18)` ASSUME_TAC THENL
   [EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s1" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s2" THEN
  C2_POLICY_CHECKED_STEP_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS "s3" THEN
  SUBGOAL_THEN
   `(MAYCHANGE [RIP;R12] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])
      (returned:x86state) (s3:x86state)` ASSUME_TAC THENL
   [(let pth=prove (`R (s:x86state) t ==> R subsumed D ==> D s t`,
      REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
     FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
    REWRITE_TAC[ETA_AX;SOME_FLAGS] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    C2_FINITE_FRAME_WIDEN_TAC;ALL_TAC] THEN
  MP_TAC(ISPECL [`returned:x86state`;`s3:x86state`] C2_HEADER_FRAME_PRESERVED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[assurance_checked_run;c2_branch_header_post] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "pc" THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

let C2_BRANCH_HEADER = prove
 (c2_branch_header_statement,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c2_equal (m:int64->byte) p q n` THENL
   [C2_HEADER_BRANCH_TAC `c2_equal (m:int64->byte) p q n`;
    C2_HEADER_BRANCH_TAC `~c2_equal (m:int64->byte) p q n`]);;
