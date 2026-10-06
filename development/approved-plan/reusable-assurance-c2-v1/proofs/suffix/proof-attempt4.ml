(* O5 actual suffix: explicit artifact offsets selected after proving
   the public initial-equality branch. This is C2-only machine automation. *)
let C2_SUFFIX_AT_OFFSET_TAC offset =
  SUBGOAL_THEN `MAYCHANGE [] (returned:x86state) returned` ASSUME_TAC THENL
   [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
  ABBREV_TAC `pc=0x22001120` THEN
  SUBGOAL_THEN (parse_term ("read RIP (returned:x86state)=word(pc+"^string_of_int offset^")"))
    ASSUME_TAC THENL
   [EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  C2_SUFFIX_CHECKED_STEP_TAC "s1" THEN C2_SUFFIX_STATE_NORMALIZE_TAC THEN
  C2_SUFFIX_CHECKED_STEP_TAC "s2" THEN C2_SUFFIX_STATE_NORMALIZE_TAC THEN
  C2_SUFFIX_CHECKED_STEP_TAC "s3" THEN C2_SUFFIX_STATE_NORMALIZE_TAC THEN
  C2_SUFFIX_CHECKED_STEP_TAC "s4" THEN C2_SUFFIX_STATE_NORMALIZE_TAC THEN
  C2_SUFFIX_CHECKED_STEP_TAC "s5" THEN C2_SUFFIX_STATE_NORMALIZE_TAC THEN
  SUBGOAL_THEN
   `(MAYCHANGE [RIP;RSP;RAX;RBX;RBP;R12] ,, MAYCHANGE [events])
      (returned:x86state) (s5:x86state)` ASSUME_TAC THENL
   [(let pth=prove (`R (s:x86state) t ==> R subsumed D ==> D s t`,
      REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
     FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
    REWRITE_TAC[ETA_AX] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    C2_FINITE_FRAME_WIDEN_TAC;ALL_TAC] THEN
  MP_TAC(ISPECL [`returned:x86state`;`s5:x86state`] C2_SUFFIX_FRAME_PRESERVED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[assurance_checked_run;c2_suffix_post] THEN ASM_REWRITE_TAC[];;

let C2_SUFFIX = prove
 (c2_suffix_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2_suffix_pre] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c2_equal (m:int64->byte) p q n` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `c2_equal (m:int64->byte) p q n`]) THEN
    ASSUME_TAC(ASSUME `c2_equal (m:int64->byte) p q n`) THEN ASM_REWRITE_TAC[] THEN C2_SUFFIX_AT_OFFSET_TAC 51;
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~c2_equal (m:int64->byte) p q n`]) THEN
    ASSUME_TAC(ASSUME `~c2_equal (m:int64->byte) p q n`) THEN ASM_REWRITE_TAC[] THEN C2_SUFFIX_AT_OFFSET_TAC 26]);;
