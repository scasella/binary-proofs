let CRYPTO_CONTROL_RUN_LOCAL_POLICY_TAC count_term decode_ths offset original_step update =
  let dt=Option.get decode_ths.(offset) in
  let _,conseq=dest_imp(snd(strip_forall(concl dt))) in
  let len,inst=dest_pair(rand conseq) in
  let d0=if offset=14 then `[EventJump(word(pc+16),if count=0 then word(pc+93) else word(pc+16))]`
    else if offset=20 then `[EventJump(word(pc+22),if count=16 then word(pc+22) else word(pc+64))]`
    else if offset=93 then `[EventJump(word(pc+95),returnaddress);EventLoad(stackpointer:int64,8)]`
    else if offset=64 then `[EventLoad(p:int64,1)]`
    else if offset=71 then `[EventLoad(q:int64,1)]`
    else if offset=84 then
      `[EventJump(word(pc+86),if count=1 then word(pc+86) else word(pc+64))]`
    else `[]:uarch_event list` in
  let d=vsubst [count_term,`count:num`] d0 in
  REWRITE_TAC[assurance_zero_step] THEN CONJ_TAC THENL
  [REWRITE_TAC[assurance_step_policy] THEN MAP_EVERY EXISTS_TAC [len;inst;d] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ASSURANCE_CODE_OFFSET_VALUE;ASSURANCE_CODE_BASE_VALUE;
      ARITH_RULE(mk_binary "<" (mk_numeral(num offset),`95`))] THEN
    MP_TAC(ISPECL [`xp:num->bool`;`pc:num`;`95`;mk_numeral(num offset);len]
      ASSURANCE_SPAN_SUBRANGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC;REWRITE_TAC[ADD_CLAUSES]];
    SUBST1_TAC(SYM update) THEN ASM_REWRITE_TAC[APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
    ASM_REWRITE_TAC[APPEND;WORD_ADD_0;GSYM WORD_ADD_ASSOC;GSYM WORD_ADD;
      ARITH_RULE `SUC k=1 <=> k=0`;ARITH_RULE `SUC k=0 <=> F`];
    REWRITE_TAC[ALL;assurance_event_policy] THEN ASM_REWRITE_TAC[WORD_ADD_0]];
   if offset<>93 then
    MATCH_MP_TAC(TAUT `~p ==> (p ==> q)`) THEN ARITH_TAC else
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ASSURANCE_RET_FROM_DECODE_AND_STEP THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(Option.get decode_ths.(93)) THEN ASM_REWRITE_TAC[];
      ACCEPT_TAC original_step]];;
let CRYPTO_CONTROL_RUN_SCALAR_LOCAL_TAC count_term decode_ths offset original_step update =
  let dt=Option.get decode_ths.(offset) in
  let _,conseq=dest_imp(snd(strip_forall(concl dt))) in
  let len,inst=dest_pair(rand conseq) in
  let _,step_args=strip_comb(concl original_step) in let source=hd step_args in
  GEN_REWRITE_TAC I [assurance_zero_scalar_step] THEN CONJ_TAC THENL
   [CRYPTO_CONTROL_RUN_LOCAL_POLICY_TAC count_term decode_ths offset original_step update;
    MATCH_MP_TAC(ISPECL [len;inst;source] ASSURANCE_DECODED_SCALAR_UNIQUE) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] dt) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [mk_numeral(num offset);len;inst]
        ABI_CRYPTO_REGISTERED_SITE_IS_SCALAR) THEN REWRITE_TAC[abi_crypto_site]]];;
let CRYPTO_CONTROL_RUN_SCALAR_BASIC_STEP_TAC count_term offset decode_ths sname (asl,w) =
  let _,args=strip_comb w in
  let stepn=hd args in
  let predecessor=mk_binary "-" (stepn,`1:num`) in
  let n_th=ARITH_RULE(mk_eq(stepn,mk_binary "+" (`1:num`,predecessor))) in
  let sv=last args and sv'=mk_var(sname,`:x86state`) in
  let eth=X86_CONV decode_ths (map snd asl) (mk_comb(mk_comb(`x86`,sv),sv')) in
  (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [n_th] THEN
   GEN_REWRITE_TAC I [ASSURANCE_RUN_STEP] THEN CONJ_TAC THENL
    [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
     X_GEN_TAC sv' THEN DISCH_THEN(fun original_step ->
       MP_TAC(EQ_MP eth original_step) THEN REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
       DISCH_THEN(fun update -> CONJ_TAC THENL
        [CRYPTO_CONTROL_RUN_SCALAR_LOCAL_TAC count_term decode_ths offset original_step update;MP_TAC update]))]) (asl,w);;
let CRYPTO_CONTROL_RUN_SCALAR_STEP_TAC count_term offset (length_th,decode_ths) sname =
  CRYPTO_CONTROL_RUN_SCALAR_BASIC_STEP_TAC count_term offset decode_ths sname THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update length_th) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(fun update ->
   let reads=STATE_UPDATE_NEW_RULE update in
   if reads=[] then ALL_TAC else MP_TAC(end_itlist CONJ reads) THEN
   ASSEMBLER_SIMPLIFY_TAC THEN STRIP_TAC);;
