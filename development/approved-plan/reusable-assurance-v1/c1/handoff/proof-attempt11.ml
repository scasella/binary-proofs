(* Main10 reached the endpoint with exactly four printed residuals.
   This preserves all actual steps and replaces only that diagnostic with
   exact upper-bound, constant-word, AC-frame and permission projections. *)
(* Main8 OOM was localized to whole-context code/slot normalization.
   Main9 was not executed before that OOM. This source keeps its concrete
   library projections and uses a separately frozen three-premise address rule. *)
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

(* Select the three exact scalar-address facts. The kernel theorem is
   normalized before its application; no caller-context simplifier runs. *)
let C1_CRYPTO_SLOT_REGION_TAC (asl,w) =
 print_endline "C1_CRYPTO_SLOT_PROJECT_BEGIN";
 let ths=map snd asl in
 let lower_term=`16<=val(stackpointer:int64)` in
 let upper_term=concl(CONV_RULE NUM_REDUCE_CONV
   (ASSUME `val(stackpointer:int64)+8<2 EXP 64`)) in
 let nonoverlap_term=`nonoverlapping(word_sub (stackpointer:int64) (word 16),8)
      (word 0x10241840,95)` in
 let pick term=find (fun th -> aconv term (concl th)) ths in
 let premises=CONJ (pick lower_term) (CONJ (pick upper_term) (pick nonoverlap_term)) in
 let local_rule=CONV_RULE NUM_REDUCE_CONV
   (SPEC `stackpointer:int64` C1_CRYPTO_SLOT_REGION_DISJOINT) in
 let exact=MATCH_MP local_rule premises in
 print_endline "C1_CRYPTO_SLOT_PROJECT_END";
 (POP_ASSUM_LIST(K ALL_TAC) THEN ACCEPT_TAC exact) (asl,w);;

(* Final obligations are solved by four exact, small premise projections.
   The dispatcher rejects every unexpected goal; it performs no general search. *)
let C1_FINAL_ENDPOINT_TAC (asl,w) =
 let ths=map snd asl in
 let pick term=find(fun th -> aconv term (concl th)) ths in
 let upper_term=concl(CONV_RULE NUM_REDUCE_CONV
   (ASSUME `val(stackpointer:int64)+8<2 EXP 64`)) in
 let end_bound=concl(CONV_RULE NUM_REDUCE_CONV
   (ASSUME `val(stackpointer:int64)-16+8<2 EXP 64`)) in
 let fixed_neq=`~((word 0x21001119:int64)=word 0x10241840)` in
 let ac_goal=`~bit 18(read rflags(s3:x86state))` in
 let library_goal=`!addr. lw_image_domain addr ==>
   rp addr /\ ordinary addr /\ (xp addr <=> lw_execute addr)` in
 if aconv w end_bound then
  (C1_CHECKPOINT "C1_FINAL_STACK_BOUND" THEN
   MP_TAC(pick upper_term) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC) (asl,w)
 else if aconv w fixed_neq then
  (C1_CHECKPOINT "C1_FINAL_FIXED_RETURN_NEQ" THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   REWRITE_TAC[GSYM VAL_EQ;VAL_WORD;DIMINDEX_64] THEN
   CONV_TAC NUM_REDUCE_CONV) (asl,w)
 else if aconv w ac_goal then
  let prefix=pick `c1_prefix_frame stackpointer (s:x86state) s3` in
  let included=REWRITE_RULE[subsumed]
    (SPEC `stackpointer:int64` C1_PREFIX_FRAME_INCLUDED) in
  let full_frame=MATCH_MP included prefix in
  let saved=MATCH_MP
    (ISPECL [`stackpointer:int64`;`s:x86state`;`s3:x86state`]
      C1_FRAME_SAVED_PRESERVED) full_frame in
  let aceq=last(CONJUNCTS saved) in
  let initial=pick `~bit 18(read rflags(s:x86state))` in
  (C1_CHECKPOINT "C1_FINAL_AC_FRAME" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
   REWRITE_TAC[aceq] THEN ACCEPT_TAC initial) (asl,w)
 else if aconv w library_goal then
  (C1_CHECKPOINT "C1_FINAL_LIBRARY_PERMISSION" THEN
   C1_LIBRARY_WP_PROJECTION_TAC) (asl,w)
 else
  (C1_ENDPOINT_RESIDUAL THEN FAIL_TAC "C1 unexpected final endpoint") (asl,w);;

let C1_CRYPTO_HANDOFF = prove
 (c1_handoff_statement,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1_pre;c1_loaded_code;c1_got;C_ARGUMENTS] THEN STRIP_TAC THEN
  C1_PREFIX_PERMISSIONS_TAC THEN
  C1_PROTECT_REGION_TAC 0x21001110 22 C1_CALLER_READONLY_REGION THEN
  C1_PROTECT_REGION_TAC 0x21001030 6 C1_PLT_READONLY_REGION THEN
  C1_PROTECT_REGION_TAC 0x10241840 95 C1_CRYPTO_READONLY_REGION THEN
  C1_PROTECT_REGION_TAC 0x21003fd8 8 C1_GOT_READONLY_REGION THEN
  SUBGOAL_THEN `MAYCHANGE [] (s:x86state) s` ASSUME_TAC THENL
   [REWRITE_TAC[MAYCHANGE;ASSIGNS_SEQ];ALL_TAC] THEN
  ABBREV_TAC `pc=0x21001110` THEN
  C1_CHECKPOINT "C1_BEFORE_SUB" THEN
  C1_CALLER_CHECKED_STEP_TAC "s1" THEN
  C1_CHECKPOINT "C1_AFTER_SUB_BEFORE_CALL" THEN
  C1_CALLER_CHECKED_STEP_TAC "s2" THEN
  C1_CHECKPOINT "C1_AFTER_CALL" THEN
  SUBGOAL_THEN `read RIP (s2:x86state)=word 0x21001030` ASSUME_TAC THENL
   [UNDISCH_TAC `read RIP (s2:x86state)=word(pc+18446744073709551392)` THEN
    EXPAND_TAC "pc" THEN REWRITE_TAC[C1_CRYPTO_PLT_ADDRESS];ALL_TAC] THEN
  ABBREV_TAC `pltpc=0x21001030` THEN
  C1_CHECKPOINT "C1_BEFORE_PLT" THEN C1_TRACE_RIP "s2" THEN
  C1_PLT_CHECKED_STEP_TAC "s3" THEN
  C1_CHECKPOINT "C1_AFTER_PLT" THEN
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[C1_WORD_SUB_SUB]) THEN
  C1_CHECKPOINT "C1_EP_PREFIX_FRAME_BEGIN" THEN
  SUBGOAL_THEN `c1_prefix_frame stackpointer (s:x86state) s3` ASSUME_TAC THENL
   [REWRITE_TAC[c1_prefix_frame] THEN C1_TRACE_FRAME THEN
    (let pth=prove (`R (s:x86state) t ==> R subsumed D ==> D s t`,
       REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
     FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check(maychange_term o concl))) THEN
    C1_CHECKPOINT "C1_FRAME_SUBSUMED_GOAL" THEN C1_TRACE_FRAME THEN
    REWRITE_TAC[ETA_AX;SOME_FLAGS] THEN
    C1_CHECKPOINT "C1_FRAME_FLAGS_EXPANDED" THEN C1_TRACE_FRAME THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN C1_FINITE_FRAME_WIDEN_TAC;
    ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_PREFIX_FRAME_END_MEMORY_BEGIN" THEN
  SUBGOAL_THEN `!addr:int64. ~c1_call_slot stackpointer (val addr)
    ==> read memory (s3:x86state) addr=m addr` ASSUME_TAC THENL
   [X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN
    SUBGOAL_THEN `read memory (s3:x86state) addr=read memory (s:x86state) addr`
     (fun th->ACCEPT_TAC(TRANS th
       (AP_THM(ASSUME `read memory (s:x86state)=m`) `addr:int64`))) THEN
    MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`addr:int64`;
      `s:x86state`;`s3:x86state`] C1_PREFIX_FRAME_BYTE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_MEMORY_END_LIBRARY_SLOT_BEGIN" THEN
  SUBGOAL_THEN `!addr. fb_immutable addr ==> ~c1_call_slot stackpointer addr`
   ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`wp:num->bool`;`ordinary:num->bool`]
      C1_LIBRARY_SLOT_DISJOINT) THEN ASM_REWRITE_TAC[] THEN
    C1_LIBRARY_WP_PROJECTION_TAC;
    ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_LIBRARY_SLOT_END_IMAGE_BEGIN" THEN
  SUBGOAL_THEN `fb_full_image lib_file (read memory (s3:x86state))
     (read memory s3) (read memory s3)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`lib_file:num->byte`;`lib_rw:int64->byte`;
     `lib_padding:int64->byte`;`m:int64->byte`;`read memory (s3:x86state)`]
      C1_LIBRARY_REBIND) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `addr:int64` THEN DISCH_TAC THEN C1_IMMUTABLE_MEMORY_POINT_TAC;
    ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_IMAGE_END_P_BUFFER_BEGIN" THEN
  SUBGOAL_THEN `!i. i<n ==> read memory (s3:x86state) (word_add p (word i))=
     m(word_add p (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;`p:int64`;
     `n:num`;`stackpointer:int64`;`m:int64->byte`;`s3:x86state`]
      C1_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_P_BUFFER_END_Q_BUFFER_BEGIN" THEN
  SUBGOAL_THEN `!i. i<n ==> read memory (s3:x86state) (word_add q (word i))=
     m(word_add q (word i))` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`\addr:num. rp addr /\ ordinary addr`;`q:int64`;
     `n:num`;`stackpointer:int64`;`m:int64->byte`;`s3:x86state`]
      C1_UNCHANGED_BUFFER) THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_Q_BUFFER_END_INCOMING_BEGIN" THEN
  SUBGOAL_THEN `read (memory :> bytes64 stackpointer) (s3:x86state)=
     read (memory :> bytes64 stackpointer) (s:x86state)` ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL [`stackpointer:int64`;`s:x86state`;`s3:x86state`]
      C1_PREFIX_FRAME_INCOMING_SLOT) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    C1_CHECKPOINT "C1_INCOMING_SLOT_UNSOLVED" THEN C1_ENDPOINT_RESIDUAL THEN
    FAIL_TAC "C1 incoming-slot residual";
    ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_INCOMING_END_STACK_VALUE_BEGIN" THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 16))=val stackpointer-16`
   ASSUME_TAC THENL [ASM_SIMP_TAC[C1_STACK_SUB16_VALUE];ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_STACK_VALUE_END_ALIGNMENT_BEGIN" THEN
  SUBGOAL_THEN `val(word_sub (stackpointer:int64) (word 16)) MOD 16=8`
   ASSUME_TAC THENL [MATCH_MP_TAC C1_STACK_ALIGNMENT THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_ALIGNMENT_END_CALLEE_RA_REGION_BEGIN" THEN
  SUBGOAL_THEN `!addr.
     ~(assurance_region (word 0x10241840) 95 addr /\
       assurance_region (word_sub (stackpointer:int64) (word 16)) 8 addr)`
   ASSUME_TAC THENL
   [C1_CRYPTO_SLOT_REGION_TAC;ALL_TAC] THEN
  C1_CHECKPOINT "C1_EP_CALLEE_RA_REGION_END_FINAL_REWRITE_BEGIN" THEN
  REWRITE_TAC[assurance_checked_run;c1_crypto_ready;bp_e2_crypto_public_pre;
    bp_e2_crypto_pre;C_ARGUMENTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[C1_WORD_SUB_SUB;c1_loaded_code;c1_got] THEN
  C1_CHECKPOINT "C1_EP_PUBLIC_DEFINITIONS_REWRITTEN" THEN
  EXPAND_TAC "pc" THEN EXPAND_TAC "pltpc" THEN CONV_TAC NUM_REDUCE_CONV THEN
  C1_CHECKPOINT "C1_EP_CONCRETE_PCS_REWRITTEN" THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[assurance_canonical48;VAL_WORD;DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  C1_CHECKPOINT "C1_EP_FINAL_REWRITES_COMPLETE" THEN
  REPEAT CONJ_TAC THEN C1_FINAL_ENDPOINT_TAC);;
