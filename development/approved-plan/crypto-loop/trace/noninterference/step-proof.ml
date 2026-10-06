needs "/work/development/approved-plan/crypto-loop/trace/noninterference/model.ml";;
needs "/work/development/approved-plan/crypto-loop/trace/noninterference/schema.ml";;
let CRYPTO_OBS_LOCAL_TAC count_term decode_ths offset original_step update obs =
 let dt=Option.get decode_ths.(offset) in
 let _,conseq=dest_imp(snd(strip_forall(concl dt))) in
 let len,inst=dest_pair(rand conseq) in
 let _,step_args=strip_comb(concl original_step) in
 let source=hd step_args and target=last step_args in
 let d0=if offset=14 then `[EventJump(word(pc+16),if count=0 then word(pc+93) else word(pc+16))]`
   else if offset=20 then `[EventJump(word(pc+22),if count=16 then word(pc+22) else word(pc+64))]`
   else if offset=93 then `[EventJump(word(pc+95),returnaddress);EventLoad(stackpointer:int64,8)]`
   else if offset=50 then `[EventJump(word(pc+52),returnaddress);EventLoad(stackpointer:int64,8)]`
   else if offset=64 then `[EventLoad(p:int64,1)]`
   else if offset=71 then `[EventLoad(q:int64,1)]`
   else if offset=22 then `[EventLoad(p:int64,8)]`
   else if offset=25 then `[EventLoad(word_add(p:int64)(word 8),8)]`
   else if offset=36 then `[EventLoad(q:int64,8)]`
   else if offset=39 then `[EventLoad(word_add(q:int64)(word 8),8)]`
   else if offset=84 then
     `[EventJump(word(pc+86),if count=1 then word(pc+86) else word(pc+64))]`
   else `[]:uarch_event list` in
 let d=vsubst [count_term,`count:num`] d0 in
 let prefix=list_mk_comb(`APPEND:uarch_event list->uarch_event list->uarch_event list`,
   [d;mk_comb(`read events:x86state->uarch_event list`,source)]) in
 let prefixeq=mk_eq(mk_comb(`read events:x86state->uarch_event list`,target),prefix) in
 let deltaeq=mk_eq(list_mk_comb(`assurance_delta`,[source;target]),d) in
 SUBGOAL_THEN prefixeq ASSUME_TAC THENL
  [SUBST1_TAC(SYM update) THEN ASM_REWRITE_TAC[APPEND] THEN
   CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
   ASM_REWRITE_TAC[APPEND;WORD_ADD_0;GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
    ARITH_RULE `SUC k=1 <=> k=0`;ARITH_RULE `SUC k=0 <=> F`];ALL_TAC] THEN
 SUBGOAL_THEN deltaeq ASSUME_TAC THENL
  [MATCH_MP_TAC ASSURANCE_DELTA_EXACT THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
 SUBGOAL_THEN
  (mk_eq(obs,list_mk_comb(`assurance_observation`,[source;len;inst;target])))
  SUBST1_TAC THENL
  [ASM_REWRITE_TAC[assurance_observation;crypto_public_observation;crypto_public_decode;
    FST;SND;REVERSE;APPEND;WORD_ADD_0;ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_REWRITE_TAC[ARITH_RULE `SUC k=1 <=> k=0`;ARITH_RULE `SUC k=0 <=> F`];
   MATCH_MP_TAC ASSURANCE_DECODED_OBSERVATION_ALL_SUCCESSORS THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
     ACCEPT_TAC original_step]];;
let CRYPTO_OBS_BASIC_STEP_TAC count_term offset decode_ths sname (asl,w) =
 let _,args=strip_comb w in
 let _,consargs=strip_comb(hd args) in let obs=hd consargs in
 let sv=last args and sv'=mk_var(sname,`:x86state`) in
 let eth=X86_CONV decode_ths (map snd asl) (mk_comb(mk_comb(`x86`,sv),sv')) in
 (GEN_REWRITE_TAC I [crypto_observed_run] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
    X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
     MP_TAC(EQ_MP eth original_step) THEN REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
     DISCH_THEN(fun update -> CONJ_TAC THENL
      [CRYPTO_OBS_LOCAL_TAC count_term decode_ths offset original_step update obs;MP_TAC update]))]) (asl,w);;
let CRYPTO_OBS_STEP_TAC count_term offset (length_th,decode_ths) sname =
 CRYPTO_OBS_BASIC_STEP_TAC count_term offset decode_ths sname THEN
 NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update length_th) THEN
 ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(fun update ->
  let reads=STATE_UPDATE_NEW_RULE update in
  if reads=[] then ALL_TAC else MP_TAC(end_itlist CONJ reads) THEN
  ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;
