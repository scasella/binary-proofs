(* New C2 final-policy callback; uses the same original-successor tactic.
   The actual RET clause is discharged only at count 1 and actual RET decode. *)
let C2_SUFFIX_POLICY_TAC original update (asl,w) =
 let _,args=strip_comb w in
 let remaining=el 9 args and source=el 10 args and target=el 11 args in
 let decode,_=C2_SYMBOLIC_DECODE (snd C2_CALLER_RAW_EXEC) (map snd asl) source in
 let pc_fact=find(fun th -> is_eq(concl th) && is_read_rip(lhs(concl th)) &&
   rand(lhs(concl th))=source) (map snd asl) in
 let pc_num=rand(rhs(concl pc_fact)) in
 let actual_ret=ISPECL [pc_num;source;target] C2_ORIGINAL_RET in
 (MATCH_MP_TAC (ISPECL args C2_SEGMENT_TO_FINAL_POLICY) THEN CONJ_TAC THENL
   [C2_PUBLIC_CODE_POLICY_TAC 0x22001120 59 "pc" (snd C2_CALLER_RAW_EXEC) original update;
    if rand(concl(NUM_REDUCE_CONV remaining))=`1` then
      DISCH_TAC THEN MATCH_MP_TAC actual_ret THEN REPEAT CONJ_TAC THENL
       [ACCEPT_TAC pc_fact;ACCEPT_TAC(REWRITE_RULE[pc_fact] decode);ACCEPT_TAC original]
    else CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]) (asl,w);;
let C2_SUFFIX_CHECKED_STEP_TAC name =
 C2_CHECKED_STEP_TAC C2_SUFFIX_POLICY_TAC C2_CALLER_RAW_EXEC C2_CALLER_SUBTHS name;;
let C2_SUFFIX_STATE_NORMALIZE_TAC =
 RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE
  [C2_WORD_SUB_SUB;
   WORD_RULE `word_add (word_sub (sptr:int64) (word 24)) (word 8)=word_sub sptr (word 16)`;
   WORD_RULE `word_add (word_sub (sptr:int64) (word 16)) (word 8)=word_sub sptr (word 8)`;
   WORD_RULE `word_add (word_sub (sptr:int64) (word 8)) (word 8)=sptr`]);;
