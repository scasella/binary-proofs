(* Candidate preparation: parameterized original-successor scalar caller/PLT automation. No caller-specific predicates/addresses/offset tables. *)
let HT_CHECKED_STEP_TAC policy_tac rule subths sname =
 GEN_STEP_TAC
  (fun decode_ths next_name _ ->
    CLIENT_CHECKED_BASIC_STEP_TAC R1_X86_CONV decode_ths next_name policy_tac)
  ALL_TAC bytes_loaded_update (fun _ _ -> ())
  rule subths sname None (K STRIP_TAC);;
(* Caller/PLT-only callback. Delta is extracted from checked event read facts;
   every original successor and undefined-value choice remains quantified. *)
let HT_SYMBOLIC_DECODE array ths source =
 let pc_th=find (fun th ->
  try let l,_=dest_eq(concl th) in is_read_rip l && rand l=source
  with Failure _->false) ths in
 let pc_expr=rand(rhs(concl pc_th)) in
 let ofs=if is_var pc_expr then 0 else dest_small_numeral(snd(dest_binary "+" pc_expr)) in
 let ante=fst(dest_imp(snd(strip_forall(concl(option_get array.(0)))))) in
 let mc=last(snd(strip_comb ante)) in
 let loaded=find (fun th ->
  let c,args=strip_comb(concl th) in
  c=`bytes_loaded` && hd args=source && last args=mc) ths in
 let raw=MATCH_MP(option_get array.(ofs)) loaded in
 let raw=CONV_RULE (ONCE_DEPTH_CONV
  (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV)) raw in
 GEN_REWRITE_RULE (RATOR_CONV o RAND_CONV) [GSYM pc_th] raw,ofs;;
let HT_QUALIFIED_DECODE decode =
 let nd=REWRITE_RULE ([r1_near_operand64;r1_near_register] @ GPR_thms) decode in
 let _,inst=dest_pair(last(snd(strip_comb(concl nd)))) in
 let scalar=prove(mk_comb(`abi_caller_scalar_instruction`,inst),
  REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
   abi_scalar_instruction;abi_integer_operand;abi_integer_writable;
   abi_cmov_operand] THEN MESON_TAC[]) in
 MATCH_MP ABI_CALLER_DECODED_SCALAR_UNIQUE (CONJ nd scalar);;
let HT_WORD_SUB_SUB = WORD_RULE
 `!pointer:int64. !a b.
   word_sub (word_sub pointer (word a)) (word b)=word_sub pointer (word(a+b))`;;
let HT_PUBLIC_CODE_POLICY_TAC segment_definition fetch codelen abbreviation array event_span_tac original update (asl,w) =
 let source=rand(rator(concl original)) and target=rand(concl original) in
 let decode,offset=HT_SYMBOLIC_DECODE array (map snd asl) source in
 let qualified=HT_QUALIFIED_DECODE decode in
 let len,inst=dest_pair(last(snd(strip_comb(concl decode)))) in
 let event_fact=CONV_RULE
  (RAND_CONV(REPEATC COMPONENT_READ_OVER_WRITE_CONV))
  (SYM(AP_TERM `read events:x86state->uarch_event list` update)) in
 let oldevents=mk_comb(`read events:x86state->uarch_event list`,source) in
 let rec split_events tm =
  if tm=oldevents then [] else
  let c,args=strip_comb tm in
  if name_of c="CONS" then hd args::split_events(el 1 args)
  else failwith "caller delta must end in exact source event list" in
 let delta=mk_list(split_events(rhs(concl event_fact)),`:uarch_event`) in
 let pc_fact=find (fun th -> is_eq(concl th) && is_read_rip(lhs(concl th)) && rand(lhs(concl th))=source) (map snd asl) in
 let pc_expr=rand(rhs(concl pc_fact)) in
 let fetch_base=if offset=0 then pc_expr else fst(dest_binary "+" pc_expr) in
 let fetch_th=CONV_RULE (RAND_CONV(REWRITE_CONV[ADD_CLAUSES]))
  (SPECL [fetch;fetch_base;mk_small_numeral codelen;mk_small_numeral offset;len]
   R1_SECRET_SPAN_SUBSPAN) in
 (REWRITE_TAC[segment_definition] THEN CONJ_TAC THENL
   [REWRITE_TAC[assurance_step_policy] THEN
    EXISTS_TAC len THEN EXISTS_TAC inst THEN EXISTS_TAC delta THEN
    REPEAT CONJ_TAC THENL
     [ACCEPT_TAC decode;
      SUBGOAL_THEN (mk_binary "<" (pc_expr,`2 EXP 64`)) ASSUME_TAC THENL
       [EXPAND_TAC abbreviation THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
      PURE_ONCE_REWRITE_TAC[pc_fact] THEN
      ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      MATCH_MP_TAC fetch_th THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[APPEND;event_fact];
      REWRITE_TAC[ALL;assurance_event_policy] THEN
      ASM_REWRITE_TAC[HT_WORD_SUB_SUB] THEN EXPAND_TAC abbreviation THEN
      CONV_TAC NUM_REDUCE_CONV THEN event_span_tac];
    ACCEPT_TAC qualified]) (asl,w);;
(* Frozen normalization algorithm; callers supply closed concrete word identities only. *)
let HT_STATE_NORMALIZE_TAC facts =
 RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE
  (HT_WORD_SUB_SUB :: facts));;
(* Parameterized actual-RET bridge: local bridge is a closed theorem obtained by
   unfolding the caller final policy, not an additional caller premise. *)
let HT_FINAL_POLICY_TAC segment_tac final_bridge remaining source target array original update (asl,w) =
 let decode,_=HT_SYMBOLIC_DECODE array (map snd asl) source in
 let pc_fact=find(fun th -> is_eq(concl th) && is_read_rip(lhs(concl th)) &&
   rand(lhs(concl th))=source) (map snd asl) in
 let pc_num=rand(rhs(concl pc_fact)) in
 let actual_ret=ISPECL [pc_num;source;target] HT_ORIGINAL_RET in
 (MATCH_MP_TAC final_bridge THEN CONJ_TAC THENL
   [segment_tac original update;
    if rand(concl(NUM_REDUCE_CONV remaining))=`1` then
      DISCH_TAC THEN MATCH_MP_TAC actual_ret THEN REPEAT CONJ_TAC THENL
       [ACCEPT_TAC pc_fact;ACCEPT_TAC(REWRITE_RULE[pc_fact] decode);ACCEPT_TAC original]
    else CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]) (asl,w);;

(* Preparation parameterization: exact existing word/word_sub event-span dispatcher.
   The supplied theorem is a concrete caller scratch/site bound fact, not a new universal law. *)
let HT_EVENT_SPAN_TAC stack_segment_span (asl,w) =
 (ASM_REWRITE_TAC[HT_WORD_SUB_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun (asl,w) ->
   let _,args=strip_comb w in
   let permission=hd args and width=last args in
   let pointer=rand(el 1 args) in
   if is_comb pointer && name_of(rator pointer)="word" then
    (ASM_REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_REWRITE_TAC[]) (asl,w)
   else
    let stackpointer,k=dest_binary "word_sub" pointer in
    (MATCH_MP_TAC(SPECL [permission;stackpointer;rand k;width]
       stack_segment_span) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV) (asl,w))) (asl,w);;
