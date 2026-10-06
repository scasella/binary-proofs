(* Five actual continuation transitions under the frozen access/RET policy.
   Supplier instruction execution arrays are excluded. *)
let C1_TAIL_WORD_ADD = WORD_RULE
 `!pointer:int64. word_add(word_sub pointer (word 8))(word 8)=pointer`;;
let C1_TAIL_RET_POLICY original update gl =
 let source=rand(rator(concl original)) in
 print_endline "C1_TAIL_POLICY_BEGIN";
 List.iter (fun (_,th)->try let l,_=dest_eq(concl th) in if is_read_rip l then(print_thm th;print_newline()) with Failure _->())(fst gl);
 List.iter (fun (_,th)->try if name_of(fst(strip_comb(concl th)))="bytes_loaded" then(print_thm th;print_newline()) with Failure _->())(fst gl);
 let decode,_=C1_SYMBOLIC_DECODE (snd C1_CALLER_RAW_EXEC) (map snd(fst gl)) source in
 print_endline "C1_TAIL_POLICY_SYMBOLIC_DECODE_COMPLETE";
 let decoded=BP_REUSE_DECODED_STEP in
 (REWRITE_TAC[c1_step_policy] THEN CONJ_TAC THENL
  [C1_PUBLIC_CODE_POLICY_TAC 22 "pc" (snd C1_CALLER_RAW_EXEC) original update;
   CONV_TAC NUM_REDUCE_CONV THEN (
    REWRITE_TAC[assurance_actual_ret] THEN CONJ_TAC THENL
     [ACCEPT_TAC decode;
      (fun retgl ->
       let d=MATCH_MP(ISPECL[`1`;`RET`;source]decoded)decode in
       let d=REWRITE_RULE[ASSURANCE_EXECUTE_RET]d in
       ACCEPT_TAC(EQ_MP(AP_THM d (rand(concl original)))original)retgl)])])gl;;
let C1_TAIL_STEP_TAC name =
 C1_CHECKED_STEP_TAC C1_TAIL_RET_POLICY C1_CALLER_RAW_EXEC
   [CONJ(fst C1_CALLER_RAW_EXEC)TRUTH] name;;
let C1_TAIL_CHECKED = prove
 (c1_tail_checked_statement,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1_tail_pre] THEN STRIP_TAC THEN
  (fun gl -> print_endline "C1_TAIL_CASE_CONTEXT"; print_goal gl; ALL_TAC gl) THEN
  FIRST_ASSUM (SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th)=`result:int64`)) THEN
  (ABBREV_TAC `pc=0x21001110` THEN
   SUBGOAL_THEN `read RIP(s:x86state)=word(pc+9)` ASSUME_TAC THENL
    [EXPAND_TAC "pc" THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
   SUBGOAL_THEN `MAYCHANGE [] (s:x86state) s` ASSUME_TAC THENL
    [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
   C1_CHECKPOINT "C1_TAIL_BEFORE_FIRST_STEP" THEN
   SUBGOAL_THEN `bytes_loaded (s:x86state) (word pc) c1_crypto_caller_mc` ASSUME_TAC THENL
    [EXPAND_TAC "pc" THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
   C1_TAIL_STEP_TAC "t1" THEN C1_CHECKPOINT "C1_TAIL_FIRST_STEP_DONE" THEN C1_TAIL_STEP_TAC "t2" THEN
   C1_TAIL_STEP_TAC "t3" THEN C1_TAIL_STEP_TAC "t4" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[C1_TAIL_WORD_ADD]) THEN
   C1_TAIL_STEP_TAC "t5" THEN C1_CHECKPOINT "C1_TAIL_ALL_FIVE_DONE" THEN
   REWRITE_TAC[assurance_checked_run;c1_tail_post] THEN
   ASM_REWRITE_TAC[C1_TAIL_WORD_ADD] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
   C1_CHECKPOINT "C1_TAIL_ENDPOINT_BEGIN" THEN
   (fun gl -> print_goal gl; ALL_TAC gl) THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC C1_TAIL_RETURN_RSP_VALUE THEN ASM_REWRITE_TAC[];
     (let pth=prove(`R(s:x86state)t ==> R subsumed D ==> D s t`,
        REWRITE_TAC[subsumed] THEN MESON_TAC[])in
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
     REWRITE_TAC[SOME_FLAGS;ETA_AX] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
     C1_CONT_FRAME_WIDEN_TAC]));;
