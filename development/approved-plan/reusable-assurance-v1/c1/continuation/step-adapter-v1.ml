(* Retains main8 (not executed before old checker OOM). Concrete library
   permission/immutable-memory premise projection replaces full-context MESON.
   Exact frozen case, access relation and handoff endpoint are unchanged. *)
(* Retains main7. Pin incoming-slot parameters and normalize the exact bound
   before rewriting. A residual fails here rather than leaking into later branches. *)
(* Retains main6 seqapply length mismatch. Endpoint phase checkpoints and
   first residual printing replace the final unrestricted search loop. *)
(* Retains main5 frame failure. Only concrete frame diagnostics and expansion
   of the existing SOME_FLAGS definition precede the same widening tactic. *)
(* Retains main4. Only PLT rule operand normalization and RIP diagnostics
   change; SUB/CALL, frozen endpoint, and original successor relation are identical. *)
(* Retains attempt3 interrupted live search. Diagnostic checkpoints only;
   explicit footprint parameter in the frame-byte theorem application. *)
(* Retains earlier attempts; TRY applies to the completed MESON tactic. *)
(* Retains attempt1; numeral constructor avoids ambient name shadowing. *)
(* Actual three transitions only: C1 SUB, direct CALL, resolved PLT JMP.
   Callee byte-array execution rules and supplier proof bodies are excluded.
   Supplied Crypto code length is used solely for byte preservation. *)
let C1_CALLER_RAW_EXEC = X86_MK_EXEC_RULE c1_crypto_caller_mc;;
let C1_PLT_RAW_EXEC = X86_MK_EXEC_RULE c1_crypto_plt_prefix;;
(* Operand rewrites are kernel definition rewrites of the actual PLT rule. *)
let C1_PLT_EXEC = R1_NORMALIZE_EXEC_RULE C1_PLT_RAW_EXEC;;
let C1_PREFIX_SUBTHS =
 [CONJ (fst C1_CALLER_RAW_EXEC) TRUTH;
  CONJ (fst C1_PLT_RAW_EXEC) TRUTH;
  CONJ BP_PUBLIC_CRYPTO_MEMCMP_CODE_LENGTH TRUTH];;
let C1_CHECKPOINT name gl =
 print_endline name; ALL_TAC gl;;
let C1_ENDPOINT_RESIDUAL (asl,w) =
 print_endline "C1_ENDPOINT_RESIDUAL";print_term w;print_newline();
 ALL_TAC (asl,w);;
let C1_TRACE_FRAME (asl,w) =
 print_endline "C1_FRAME_GOAL";print_term w;print_newline();
 List.iter (fun (_,th) ->
  try if maychange_term(concl th)
      then (print_endline "C1_FRAME_SOURCE_FACT";print_thm th;print_newline())
  with Failure _ -> ()) asl;
 ALL_TAC (asl,w);;
let C1_TRACE_RIP sname (asl,w) =
 let source=mk_var(sname,`:x86state`) in
 List.iter (fun (_,th) ->
  try if is_eq(concl th) && is_read_rip(lhs(concl th)) &&
         rand(lhs(concl th))=source
      then (print_endline "C1_PRE_PLT_RIP_FACT";print_thm th;print_newline())
  with Failure _ -> ()) asl;
 ALL_TAC (asl,w);;
let C1_WORD_SUB_SUB = WORD_RULE
 `!pointer:int64. !a b.
   word_sub (word_sub pointer (word a)) (word b)=word_sub pointer (word(a+b))`;;
let C1_CRYPTO_PLT_ADDRESS = prove
 (`(word(0x21001110+18446744073709551392):int64)=word 0x21001030`,
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Adaptation of already exposed generic original-successor automation.
   Decoder array membership is checked for the actual loaded caller/PLT. *)
let C1_SYMBOLIC_DECODE array ths source =
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
let C1_QUALIFIED_DECODE decode =
 let nd=REWRITE_RULE ([r1_near_operand64;r1_near_register] @ GPR_thms) decode in
 let _,inst=dest_pair(last(snd(strip_comb(concl nd)))) in
 let scalar=prove(mk_comb(`abi_caller_scalar_instruction`,inst),
  REWRITE_TAC[abi_caller_scalar_instruction;abi_cleanse_scalar_instruction;
   abi_scalar_instruction;abi_integer_operand;abi_integer_writable;
   abi_cmov_operand] THEN MESON_TAC[]) in
 MATCH_MP ABI_CALLER_DECODED_SCALAR_UNIQUE (CONJ nd scalar);;
let C1_PREFIX_EVENT_SPAN_TAC =
 C1_CHECKPOINT "C1_EVENT_SPAN_BEGIN" THEN
 ASM_REWRITE_TAC[C1_WORD_SUB_SUB] THEN
 C1_CHECKPOINT "C1_EVENT_SPAN_WORDSUB_DONE" THEN
 CONV_TAC NUM_REDUCE_CONV THEN
 C1_CHECKPOINT "C1_EVENT_SPAN_NUMERIC_DONE" THEN
 ASM_SIMP_TAC[C1_STACK_SUB16_VALUE;VAL_WORD;DIMINDEX_64] THEN
 C1_CHECKPOINT "C1_EVENT_SPAN_VALUES_DONE" THEN
 CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
 C1_CHECKPOINT "C1_EVENT_SPAN_END";;
let C1_PUBLIC_CODE_POLICY_TAC codelen abbreviation array original update (asl,w) =
 print_endline "C1_CALLBACK_ENTRY";
 let source=rand(rator(concl original)) in
 print_endline "C1_CALLBACK_DECODE_BEGIN";
 let decode,offset=C1_SYMBOLIC_DECODE array (map snd asl) source in
 print_endline "C1_CALLBACK_DECODE_END";
 print_endline "C1_CALLBACK_QUALIFIED_BEGIN";
 let qualified=C1_QUALIFIED_DECODE decode in
 print_endline "C1_CALLBACK_QUALIFIED_END";
 let len,_=dest_pair(last(snd(strip_comb(concl decode)))) in
 print_endline "C1_CALLBACK_EVENTFACT_BEGIN";
 let event_fact=CONV_RULE
  (RAND_CONV(REPEATC COMPONENT_READ_OVER_WRITE_CONV))
  (SYM(AP_TERM `read events:x86state->uarch_event list` update)) in
 print_endline "C1_CALLBACK_EVENTFACT_END";
 let oldevents=mk_comb(`read events:x86state->uarch_event list`,source) in
 let rec split_events tm =
  if tm=oldevents then [] else
  let c,args=strip_comb tm in
  if name_of c="CONS" then hd args::split_events(el 1 args)
  else failwith "C1 prefix event delta must end in exact source events" in
 let delta=mk_list(split_events(rhs(concl event_fact)),`:uarch_event`) in
 let _,params=strip_comb w in
 let fetch=mk_comb(mk_comb(`c1_allowed_fetch`,el 6 params),el 7 params) in
 let pc_fact=find (fun th -> is_eq(concl th) && is_read_rip(lhs(concl th)) &&
   rand(lhs(concl th))=source) (map snd asl) in
 let pc_expr=rand(rhs(concl pc_fact)) in
 let fetch_base=if offset=0 then pc_expr else fst(dest_binary "+" pc_expr) in
 print_endline "C1_CALLBACK_FETCH_SETUP_BEGIN";
 let fetch_th=CONV_RULE (RAND_CONV(REWRITE_CONV[ADD_CLAUSES]))
  (SPECL [fetch;fetch_base;mk_small_numeral codelen;mk_small_numeral offset;len]
   R1_SECRET_SPAN_SUBSPAN) in
 print_endline "C1_CALLBACK_FETCH_SETUP_END";
 let result=(C1_CHECKPOINT "C1_POLICY_BEGIN" THEN
  REWRITE_TAC[c1_segment_policy] THEN CONJ_TAC THENL
   [REWRITE_TAC[assurance_step_policy] THEN
    EXISTS_TAC len THEN EXISTS_TAC (snd(dest_pair(last(snd(strip_comb(concl decode)))))) THEN
    EXISTS_TAC delta THEN REPEAT CONJ_TAC THENL
     [ACCEPT_TAC decode;
      SUBGOAL_THEN (mk_binary "<" (pc_expr,`2 EXP 64`)) ASSUME_TAC THENL
       [EXPAND_TAC abbreviation THEN CONV_TAC NUM_REDUCE_CONV;ALL_TAC] THEN
      C1_CHECKPOINT "C1_FETCH_REWRITE_BEGIN" THEN
      PURE_ONCE_REWRITE_TAC[pc_fact] THEN
      C1_CHECKPOINT "C1_FETCH_PC_DONE" THEN
      ASM_SIMP_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      C1_CHECKPOINT "C1_FETCH_VALUES_DONE" THEN
      MATCH_MP_TAC fetch_th THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      C1_CHECKPOINT "C1_FETCH_SUBSPAN_DONE";
      C1_CHECKPOINT "C1_EVENT_APPEND_BEGIN" THEN
      REWRITE_TAC[APPEND;event_fact] THEN
      C1_CHECKPOINT "C1_EVENT_APPEND_END";
      C1_CHECKPOINT "C1_EVENT_POLICY_BEGIN" THEN
      REWRITE_TAC[ALL;assurance_event_policy] THEN
      C1_CHECKPOINT "C1_EVENT_POLICY_UNFOLD_DONE" THEN
      ASM_REWRITE_TAC[C1_WORD_SUB_SUB] THEN EXPAND_TAC abbreviation THEN
      CONV_TAC NUM_REDUCE_CONV THEN C1_PREFIX_EVENT_SPAN_TAC];
    ACCEPT_TAC qualified]) (asl,w) in
 print_endline "C1_CALLBACK_EXIT"; result;;
let C1_CHECKED_STEP_TAC policy_tac rule subths sname =
 GEN_STEP_TAC
  (fun decode_ths next_name _ ->
    CLIENT_CHECKED_BASIC_STEP_TAC R1_X86_CONV decode_ths next_name policy_tac)
  ALL_TAC bytes_loaded_update (fun _ _ -> ())
  rule subths sname None (K STRIP_TAC);;
let C1_CALLER_CHECKED_STEP_TAC sname =
 C1_CHECKED_STEP_TAC (C1_PUBLIC_CODE_POLICY_TAC 22 "pc" (snd C1_CALLER_RAW_EXEC))
  C1_CALLER_RAW_EXEC C1_PREFIX_SUBTHS sname;;
let C1_PLT_CHECKED_STEP_TAC sname =
 C1_CHECKED_STEP_TAC (C1_PUBLIC_CODE_POLICY_TAC 6 "pltpc" (snd C1_PLT_EXEC))
  C1_PLT_EXEC C1_PREFIX_SUBTHS sname;;
let C1_PROTECT_REGION_TAC address width readonly =
 let addr=mk_comb(`word:num->int64`,mk_small_numeral address) in
 let len=mk_small_numeral width in
 SUBGOAL_THEN
  (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
     mk_pair(`word_sub (stackpointer:int64) (word 16)`,`8`)),mk_pair(addr,len)))
  ASSUME_TAC THENL
  [MATCH_MP_TAC (ISPECL [`wp:num->bool`;`ordinary:num->bool`;
     `word_sub (stackpointer:int64) (word 16)`;`8`;addr;len]
      C1_WRITABLE_READONLY_NONOVERLAPPING) THEN
   ASM_SIMP_TAC[C1_STACK_SUB16_VALUE;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[readonly];
   ALL_TAC];;
let C1_PREFIX_PERMISSIONS_TAC =
 SUBGOAL_THEN
  `assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
     (val(stackpointer:int64)-16) 8` ASSUME_TAC THENL
  [MATCH_MP_TAC C1_SLOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c1_allowed_write wp ordinary stackpointer)
     (val(stackpointer:int64)-16) 8` ASSUME_TAC THENL
  [MATCH_MP_TAC C1_SLOT_WRITE_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001110 22` ASSUME_TAC THENL
  [MATCH_MP_TAC C1_CALLER_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c1_allowed_fetch xp ordinary) 0x21001030 6` ASSUME_TAC THENL
  [MATCH_MP_TAC C1_PLT_FETCH_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  `assurance_span_ok (c1_allowed_read rp ordinary stackpointer p q n)
     0x21003fd8 8` ASSUME_TAC THENL
  [MATCH_MP_TAC C1_GOT_READ_SPAN THEN ASM_REWRITE_TAC[];ALL_TAC];;
let rec C1_FINITE_FRAME_WIDEN_TAC gl =
 let left,_=dest_binary "subsumed" (snd gl) in
 if is_binary ",," left then
  (MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN CONJ_TAC THENL
   [MAYCHANGE_IDEMPOT_TAC;
    CONJ_TAC THENL[C1_FINITE_FRAME_WIDEN_TAC;C1_FINITE_FRAME_WIDEN_TAC]]) gl
 else SUBSUMED_MAYCHANGE_TAC gl;;

(* These callbacks select the exact known premises and never expose the
   unrelated decoded-byte/state-update context to permission reasoning. *)
let C1_LIBRARY_WP_PROJECTION_TAC (asl,w) =
 let expected=`!addr. lw_image_domain addr ==>
    rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr) /\
    (wp addr <=> lw_image_write addr)` in
 let permission=find (fun th -> aconv expected (concl th)) (map snd asl) in
 (MP_TAC permission THEN POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[]) (asl,w);;
let C1_IMMUTABLE_MEMORY_POINT_TAC (asl,w) =
 let expected_memory=`!addr:int64. ~c1_call_slot stackpointer (val addr)
    ==> read memory (s3:x86state) addr=m addr` in
 let expected_disjoint=`!addr. fb_immutable addr ==> ~c1_call_slot stackpointer addr` in
 let ths=map snd asl in
 let memory=find (fun th -> aconv expected_memory (concl th)) ths in
 let disjoint=find (fun th -> aconv expected_disjoint (concl th)) ths in
 (MATCH_MP_TAC(SPEC `addr:int64` memory) THEN
  MATCH_MP_TAC(SPEC `val(addr:int64)` disjoint) THEN ASM_REWRITE_TAC[]) (asl,w);;

